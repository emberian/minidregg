/* Objective Bend demand machine, defunctionalized to C.
 *
 * This is Theory/ObjectiveBendDemandMachine.lean's `stepRaw`, `step` and
 * `runBounded` over a per-program code ROM emitted by
 * Compiler/ObjectiveBendEmitC.lean. Every case below names the Lean case it
 * transcribes. The ROM already contains the code `stepRaw` manufactures
 * (fix bodies, mix bodies, `bound 0`), so this file never renames a term.
 *
 * Exactness: naturals are unbounded (32-bit limbs), heap/stack/tick accounting
 * is the Lean accounting, capacity suspension restores the exact
 * pre-transition state, and the State is written in the canonical codec
 * `objective-state.v1` (see the Lean module). Refinement to `stepRaw` is NOT
 * proved; native/objective-emit/differential.py is the evidence.
 *
 * Activities: `perform` outside every update frame yields the whole program
 * (Control.yielded, terminal for stepRaw); under an update frame it is refused
 * `sharedEffect`. At a yield the driver below resumes (Lean `resume`: control
 * := evaluate response [], heap and stack unchanged) with the next of the
 * program's closed responses, which the emitter interned as ROM roots
 * (ob_responses), and continues under the SAME tick budget; with no response
 * left the run ends `yielded`.
 *
 * usage: prog HEAP STACK TICKS OUT_STATE [RESUME_STATE [FIRST_RESPONSE]]
 *   RESUME_STATE "-" starts from the entry; FIRST_RESPONSE (default 0) is the
 *   index into ob_responses of the next response to deliver.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern const uint32_t ob_node_count, ob_label_count, ob_entry, ob_bound_zero, ob_response_count;
extern const uint32_t ob_responses[];
extern const uint8_t ob_tag[], ob_label_bytes[];
extern const uint32_t ob_a[], ob_b[], ob_c[], ob_d[], ob_pair_off[], ob_pair_len[], ob_pairs[],
    ob_nat_off[], ob_nat_len[], ob_limbs[], ob_label_off[], ob_label_len[];

enum { T_BOUND, T_LAM, T_APP, T_MIX, T_FIX, T_SPEC, T_PROTO, T_REFLECT, T_METADATA, T_PROJECT,
       T_NAT, T_BOOL, T_LABEL, T_BINARY, T_EXTEND, T_RECORD, T_GET, T_IFZERO, T_INJECT, T_CASE,
       T_IFBOOL, T_PERFORM, T_DONE };
enum { P_ADD, P_MUL, P_EQUAL, P_CONJ, P_LABELEQ };
enum { R_UNBOUND, R_MISSINGCELL, R_MISSINGFIELD, R_WRONGVALUE, R_INVALIDUPDATE, R_CAPACITY,
       R_MISSINGARM, R_SHAREDEFFECT };
static const char *refusal_name[] = {"unbound", "missingCell", "missingField", "wrongValue",
                                     "invalidUpdate", "capacity", "missingArm", "sharedEffect"};

static void die(const char *message) { fprintf(stderr, "{\"error\":\"%s\"}\n", message); exit(2); }

/* ---- arena: nothing is freed; the run is bounded by the Lean limits ---- */
static char *arena_ptr; static size_t arena_left;
static void *arena(size_t size) {
  size = (size + 15) & ~(size_t)15;
  if (size > arena_left) {
    size_t chunk = size > (1u << 22) ? size : (1u << 22);
    arena_ptr = malloc(chunk); if (!arena_ptr) die("out of memory");
    arena_left = chunk;
  }
  void *out = arena_ptr; arena_ptr += size; arena_left -= size; return out;
}

/* ---- unbounded naturals: little-endian 32-bit limbs, no leading zero limb ---- */
typedef struct ONat { uint32_t len; uint32_t limb[]; } ONat;
static ONat *nat_alloc(uint32_t len) { ONat *n = arena(sizeof(ONat) + 4 * (size_t)len); n->len = len; return n; }
static const ONat *nat_norm(ONat *n) { while (n->len && n->limb[n->len - 1] == 0) n->len--; return n; }
static const ONat *nat_rom(uint32_t node) {
  ONat *n = nat_alloc(ob_nat_len[node]);
  memcpy(n->limb, ob_limbs + ob_nat_off[node], 4 * (size_t)n->len); return nat_norm(n);
}
static int nat_eq(const ONat *a, const ONat *b) { return a->len == b->len && !memcmp(a->limb, b->limb, 4 * (size_t)a->len); }
static const ONat *nat_add(const ONat *a, const ONat *b) {
  uint32_t len = (a->len > b->len ? a->len : b->len) + 1; ONat *r = nat_alloc(len); uint64_t carry = 0;
  for (uint32_t i = 0; i < len; i++) {
    uint64_t s = carry + (i < a->len ? a->limb[i] : 0) + (i < b->len ? b->limb[i] : 0);
    r->limb[i] = (uint32_t)s; carry = s >> 32;
  }
  return nat_norm(r);
}
static const ONat *nat_mul(const ONat *a, const ONat *b) {
  if (!a->len || !b->len) return nat_alloc(0);
  ONat *r = nat_alloc(a->len + b->len); memset(r->limb, 0, 4 * (size_t)r->len);
  for (uint32_t i = 0; i < a->len; i++) {
    uint64_t carry = 0;
    for (uint32_t j = 0; j < b->len; j++) {
      uint64_t t = (uint64_t)a->limb[i] * b->limb[j] + r->limb[i + j] + carry;
      r->limb[i + j] = (uint32_t)t; carry = t >> 32;
    }
    for (uint32_t k = i + b->len; carry; k++) { uint64_t t = (uint64_t)r->limb[k] + carry; r->limb[k] = (uint32_t)t; carry = t >> 32; }
  }
  return nat_norm(r);
}
static const ONat *nat_pred(const ONat *a) { /* a > 0 */
  ONat *r = nat_alloc(a->len); memcpy(r->limb, a->limb, 4 * (size_t)a->len);
  for (uint32_t i = 0; i < r->len; i++) { if (r->limb[i]--) break; }
  return nat_norm(r);
}

/* ---- environments: immutable cons lists of addresses (Lean `List Address`) ---- */
typedef struct Env { uint64_t addr; uint64_t len; const struct Env *next; } Env;
static const Env *env_cons(uint64_t addr, const Env *next) {
  Env *e = arena(sizeof(Env)); e->addr = addr; e->next = next; e->len = next ? next->len + 1 : 1; return e;
}

/* ---- values, cells, frames, control ---- */
typedef struct { uint32_t label; uint64_t addr; } Field;
typedef struct { uint64_t len; Field f[]; } Fields;
enum { V_CLOSURE, V_NATURAL, V_BOOLEAN, V_LABEL, V_RECORD, V_SPEC, V_PROTO, V_VARIANT };
typedef struct {
  uint8_t tag; uint8_t b; uint32_t code_or_label; uint64_t x, y;
  const Env *env; const ONat *nat; const Fields *rec;
} Value;
/* closure: code_or_label=body node, env | natural: nat | boolean: b | label: code_or_label
   record: rec | specification/prototype: x,y | variant: code_or_label=label, x=payload */

/* A closure origin. code == -1 is the one non-ROM term: the cached `.nat n`
   predecessor an ifZero successor step allocates (Lean: `⟨.nat n, []⟩`). */
typedef struct { int64_t code; const ONat *lit; const Env *env; } Closure;
enum { C_SUSPENDED, C_EVALUATING, C_CACHED };
typedef struct { uint8_t st; Closure origin; Value value; } Cell;

typedef struct { uint32_t label, code; } Pair;
enum { F_ARGUMENT, F_UPDATE, F_FIELD, F_REFLECT, F_METADATA, F_PROJECT, F_EXTEND, F_CONDITION,
       F_BINLEFT, F_BINRIGHT, F_CASE, F_IFBOOL };
typedef struct {
  uint8_t tag; uint8_t prim; uint32_t t1, t2; uint64_t addr; uint32_t label;
  const Pair *pairs; uint64_t npairs; const Env *env; Value left;
} Frame;
/* argument: t1=term env | update: addr | field: label | extend: pairs env
   condition: t1=zero t2=successor env | binaryLeft: prim t1=right env
   binaryRight: prim left | case: pairs env | ifBool: t1=true t2=false env */

enum { K_EVALUATE, K_ENTER, K_BLACKHOLE, K_RETURNED, K_COMPLETE, K_REFUSED, K_YIELDED };
/* yielded: addr = the plan cell's address */
typedef struct { uint8_t tag; uint8_t reason; uint32_t code; const Env *env; uint64_t addr; Value value; } Control;

static Cell *heap; static uint64_t heap_len, heap_cap;
static Frame *stk; static uint64_t stack_len, stack_cap; /* stk[stack_len-1] is the list head */
static Control ctl;

static void heap_push(Cell c) {
  if (heap_len == heap_cap) { heap_cap = heap_cap ? 2 * heap_cap : 1024; heap = realloc(heap, heap_cap * sizeof(Cell)); if (!heap) die("out of memory"); }
  heap[heap_len++] = c;
}
static void stack_push(Frame f) {
  if (stack_len == stack_cap) { stack_cap = stack_cap ? 2 * stack_cap : 1024; stk = realloc(stk, stack_cap * sizeof(Frame)); if (!stk) die("out of memory"); }
  stk[stack_len++] = f;
}

/* ---- undo record: capacity suspension keeps the EXACT pre-transition state ---- */
static uint64_t undo_heap_len, undo_stack_len; static Control undo_ctl;
static int undo_has_top; static Frame undo_top; static int undo_has_cell; static uint64_t undo_cell_addr; static Cell undo_cell;
static void undo_save(void) {
  undo_heap_len = heap_len; undo_stack_len = stack_len; undo_ctl = ctl; undo_has_cell = 0;
  undo_has_top = stack_len > 0; if (undo_has_top) undo_top = stk[stack_len - 1];
}
static void heap_set(uint64_t addr, Cell c) {
  if (!undo_has_cell) { undo_has_cell = 1; undo_cell_addr = addr; undo_cell = heap[addr]; }
  heap[addr] = c;
}
static void undo_restore(void) {
  heap_len = undo_heap_len; stack_len = undo_stack_len; ctl = undo_ctl;
  if (undo_has_top) stk[stack_len - 1] = undo_top;
  if (undo_has_cell) heap[undo_cell_addr] = undo_cell;
}

static Value v_simple(uint8_t tag) { Value v; memset(&v, 0, sizeof v); v.tag = tag; return v; }
static void evaluate(uint32_t code, const Env *env) { ctl.tag = K_EVALUATE; ctl.code = code; ctl.env = env; }
static void enter(uint64_t addr) { ctl.tag = K_ENTER; ctl.addr = addr; }
static void returned(Value v) { ctl.tag = K_RETURNED; ctl.value = v; }
static void refuse(uint8_t reason) { ctl.tag = K_REFUSED; ctl.reason = reason; }
static Frame f_simple(uint8_t tag) { Frame f; memset(&f, 0, sizeof f); f.tag = tag; return f; }
static Cell suspended_cell(uint32_t code, const Env *env) {
  Cell c; memset(&c, 0, sizeof c); c.st = C_SUSPENDED; c.origin.code = code; c.origin.env = env; return c;
}
static const Pair *rom_pairs(uint32_t node) { return (const Pair *)(ob_pairs + 2 * (size_t)ob_pair_off[node]); }

/* allocateFields: one suspended cell per field, in order; addresses old size + k. */
static Fields *allocate_fields(const Pair *pairs, uint64_t n, const Env *env, uint64_t extra) {
  Fields *r = arena(sizeof(Fields) + (n + extra) * sizeof(Field)); r->len = n;
  for (uint64_t k = 0; k < n; k++) {
    r->f[k].label = pairs[k].label; r->f[k].addr = heap_len;
    heap_push(suspended_cell(pairs[k].code, env));
  }
  return r;
}

/* ---- stepRaw ---- */
static void step_raw(void) {
  switch (ctl.tag) {
  case K_COMPLETE: case K_REFUSED: case K_BLACKHOLE: case K_YIELDED: return;
  case K_ENTER: {
    uint64_t a = ctl.addr;
    if (a >= heap_len) { refuse(R_MISSINGCELL); return; }                 /* none */
    Cell c = heap[a];
    if (c.st == C_EVALUATING) { ctl.tag = K_BLACKHOLE; return; }           /* evaluating */
    if (c.st == C_CACHED) { returned(c.value); return; }                    /* cached */
    if (c.origin.code < 0) die("suspended cell without ROM code");
    Cell e = c; e.st = C_EVALUATING; heap_set(a, e);                        /* suspended */
    evaluate((uint32_t)c.origin.code, c.origin.env);
    Frame f = f_simple(F_UPDATE); f.addr = a; stack_push(f);
    return;
  }
  case K_EVALUATE: {
    uint32_t n = ctl.code; const Env *env = ctl.env;
    switch (ob_tag[n]) {
    case T_BOUND: {
      uint64_t i = ob_a[n]; const Env *e = env;
      while (e && i) { e = e->next; i--; }
      if (e) enter(e->addr); else refuse(R_UNBOUND);
      return;
    }
    case T_LAM: { Value v = v_simple(V_CLOSURE); v.code_or_label = ob_a[n]; v.env = env; returned(v); return; }
    case T_NAT: { Value v = v_simple(V_NATURAL); v.nat = nat_rom(n); returned(v); return; }
    case T_BOOL: { Value v = v_simple(V_BOOLEAN); v.b = (uint8_t)ob_a[n]; returned(v); return; }
    case T_LABEL: { Value v = v_simple(V_LABEL); v.code_or_label = ob_a[n]; returned(v); return; }
    case T_APP: { Frame f = f_simple(F_ARGUMENT); f.t1 = ob_b[n]; f.env = env; evaluate(ob_a[n], env); stack_push(f); return; }
    case T_MIX: evaluate(ob_d[n], env); return;                               /* mixBody */
    case T_FIX: {                                                              /* tie one address */
      uint64_t a = heap_len;
      heap_push(suspended_cell(ob_d[n], env_cons(a, env))); enter(a); return;
    }
    case T_SPEC: case T_PROTO: {
      uint64_t a = heap_len;
      heap_push(suspended_cell(ob_a[n], env)); heap_push(suspended_cell(ob_b[n], env));
      Value v = v_simple(ob_tag[n] == T_SPEC ? V_SPEC : V_PROTO); v.x = a; v.y = a + 1; returned(v); return;
    }
    case T_REFLECT: case T_METADATA: case T_PROJECT: {
      uint8_t tag = ob_tag[n] == T_REFLECT ? F_REFLECT : ob_tag[n] == T_METADATA ? F_METADATA : F_PROJECT;
      evaluate(ob_a[n], env); stack_push(f_simple(tag)); return;
    }
    case T_RECORD: {
      Fields *r = allocate_fields(rom_pairs(n), ob_pair_len[n], env, 0);
      Value v = v_simple(V_RECORD); v.rec = r; returned(v); return;
    }
    case T_GET: { Frame f = f_simple(F_FIELD); f.label = ob_b[n]; evaluate(ob_a[n], env); stack_push(f); return; }
    case T_EXTEND: {
      Frame f = f_simple(F_EXTEND); f.pairs = rom_pairs(n); f.npairs = ob_pair_len[n]; f.env = env;
      evaluate(ob_a[n], env); stack_push(f); return;
    }
    case T_IFZERO: {
      Frame f = f_simple(F_CONDITION); f.t1 = ob_b[n]; f.t2 = ob_c[n]; f.env = env;
      evaluate(ob_a[n], env); stack_push(f); return;
    }
    case T_BINARY: {
      Frame f = f_simple(F_BINLEFT); f.prim = (uint8_t)ob_a[n]; f.t1 = ob_c[n]; f.env = env;
      evaluate(ob_b[n], env); stack_push(f); return;
    }
    case T_INJECT: {
      uint64_t a = heap_len; heap_push(suspended_cell(ob_b[n], env));
      Value v = v_simple(V_VARIANT); v.code_or_label = ob_a[n]; v.x = a; returned(v); return;
    }
    case T_CASE: {
      Frame f = f_simple(F_CASE); f.pairs = rom_pairs(n); f.npairs = ob_pair_len[n]; f.env = env;
      evaluate(ob_a[n], env); stack_push(f); return;
    }
    case T_IFBOOL: {
      Frame f = f_simple(F_IFBOOL); f.t1 = ob_b[n]; f.t2 = ob_c[n]; f.env = env;
      evaluate(ob_a[n], env); stack_push(f); return;
    }
    case T_DONE: evaluate(ob_a[n], env); return;                              /* administrative */
    case T_PERFORM: {
#ifndef OB_MUTATE_SHARED
      /* OB_MUTATE_SHARED: deliberate mutation for the harness control (no sharedEffect refusal). */
      for (uint64_t k = 0; k < stack_len; k++)                               /* forcingShared */
        if (stk[k].tag == F_UPDATE) { refuse(R_SHAREDEFFECT); return; }
#endif
      uint64_t a = heap_len;
#ifndef OB_MUTATE_PERFORM
      heap_push(suspended_cell(ob_a[n], env));                               /* the plan, lazily */
#endif
      /* OB_MUTATE_PERFORM: deliberate mutation for the harness control (the plan is not allocated). */
      ctl.tag = K_YIELDED; ctl.addr = a; return;
    }
    }
    die("unknown ROM tag");
  }
  case K_RETURNED: {
    Value v = ctl.value;
    if (stack_len == 0) { ctl.tag = K_COMPLETE; return; }
    Frame f = stk[stack_len - 1];
#define POP() (stack_len--)
    switch (f.tag) {
    case F_UPDATE:
      if (f.addr < heap_len && heap[f.addr].st == C_EVALUATING) {
        Cell c = heap[f.addr]; c.st = C_CACHED; c.value = v;
#ifdef OB_MUTATE_UPDATE
        /* Deliberate mutation for the harness control: forget the value (call-by-name). */
        c.st = C_SUSPENDED;
#endif
        heap_set(f.addr, c); POP();
      } else { refuse(R_INVALIDUPDATE); POP(); }
      return;
    case F_REFLECT:
      if (v.tag == V_PROTO) { enter(v.x); POP(); } else { refuse(R_WRONGVALUE); POP(); } return;
    case F_METADATA:
      if (v.tag == V_SPEC) { enter(v.x); POP(); } else { refuse(R_WRONGVALUE); POP(); } return;
    case F_PROJECT:
      if (v.tag == V_PROTO) { enter(v.y); POP(); } else { refuse(R_WRONGVALUE); POP(); } return;
    case F_ARGUMENT:
      if (v.tag == V_SPEC) { enter(v.y); return; }                         /* frame stays */
      if (v.tag == V_CLOSURE) {
        uint64_t a = heap_len; heap_push(suspended_cell(f.t1, f.env));
        evaluate(v.code_or_label, env_cons(a, v.env)); POP(); return;
      }
      refuse(R_WRONGVALUE); POP(); return;
    case F_FIELD:
      if (v.tag == V_RECORD) {
        for (uint64_t k = 0; k < v.rec->len; k++)
          if (v.rec->f[k].label == f.label) { enter(v.rec->f[k].addr); POP(); return; }
        refuse(R_MISSINGFIELD); POP(); return;
      }
      refuse(R_WRONGVALUE); POP(); return;
    case F_EXTEND:
      if (v.tag == V_RECORD) {
        Fields *r = allocate_fields(f.pairs, f.npairs, f.env, v.rec->len);
#ifdef OB_MUTATE_EXTEND
        /* Deliberate mutation for the harness control: drop the shadowing filter. */
        for (uint64_t k = 0; k < v.rec->len; k++) r->f[r->len++] = v.rec->f[k];
#else
        for (uint64_t k = 0; k < v.rec->len; k++) {
          int shadowed = 0;
          for (uint64_t j = 0; j < f.npairs; j++) if (f.pairs[j].label == v.rec->f[k].label) { shadowed = 1; break; }
          if (!shadowed) r->f[r->len++] = v.rec->f[k];
        }
#endif
        Value out = v_simple(V_RECORD); out.rec = r; returned(out); POP(); return;
      }
      refuse(R_WRONGVALUE); POP(); return;
    case F_CONDITION:
      if (v.tag == V_NATURAL && v.nat->len == 0) { evaluate(f.t1, f.env); POP(); return; }
      if (v.tag == V_NATURAL) {
        uint64_t a = heap_len; const ONat *p = nat_pred(v.nat);
        Cell c; memset(&c, 0, sizeof c); c.st = C_CACHED; c.origin.code = -1; c.origin.lit = p; c.origin.env = NULL;
        c.value = v_simple(V_NATURAL); c.value.nat = p; heap_push(c);
        evaluate(f.t2, env_cons(a, f.env)); POP(); return;
      }
      refuse(R_WRONGVALUE); POP(); return;
    case F_BINLEFT: {
      Frame g = f_simple(F_BINRIGHT); g.prim = f.prim; g.left = v;
      evaluate(f.t1, f.env); stk[stack_len - 1] = g; return;
    }
    case F_BINRIGHT: {
      Value l = f.left, out;
      if (f.prim == P_ADD && l.tag == V_NATURAL && v.tag == V_NATURAL) { out = v_simple(V_NATURAL); out.nat = nat_add(l.nat, v.nat); }
      else if (f.prim == P_MUL && l.tag == V_NATURAL && v.tag == V_NATURAL) { out = v_simple(V_NATURAL); out.nat = nat_mul(l.nat, v.nat); }
      else if (f.prim == P_EQUAL && l.tag == V_NATURAL && v.tag == V_NATURAL) { out = v_simple(V_BOOLEAN); out.b = (uint8_t)nat_eq(l.nat, v.nat); }
      else if (f.prim == P_CONJ && l.tag == V_BOOLEAN && v.tag == V_BOOLEAN) { out = v_simple(V_BOOLEAN); out.b = l.b && v.b; }
      else if (f.prim == P_LABELEQ && l.tag == V_LABEL && v.tag == V_LABEL) { out = v_simple(V_BOOLEAN); out.b = l.code_or_label == v.code_or_label; }
      else { refuse(R_WRONGVALUE); POP(); return; }
      returned(out); POP(); return;
    }
    case F_CASE:
      if (v.tag == V_VARIANT) {
        for (uint64_t k = 0; k < f.npairs; k++)
          if (f.pairs[k].label == v.code_or_label) {
            uint64_t a = heap_len; heap_push(suspended_cell(ob_bound_zero, env_cons(v.x, NULL)));
            evaluate(f.pairs[k].code, env_cons(a, f.env)); POP(); return;
          }
        refuse(R_MISSINGARM); POP(); return;
      }
      refuse(R_WRONGVALUE); POP(); return;
    case F_IFBOOL:
      if (v.tag == V_BOOLEAN) { evaluate(v.b ? f.t1 : f.t2, f.env); POP(); return; }
      refuse(R_WRONGVALUE); POP(); return;
    }
#undef POP
    die("unknown frame");
  }
  }
  die("unknown control");
}

/* ---- canonical State codec objective-state.v1 ---- */
static uint8_t *out_buf; static size_t out_len, out_cap;
static void put(uint8_t b) {
  if (out_len == out_cap) { out_cap = out_cap ? 2 * out_cap : 65536; out_buf = realloc(out_buf, out_cap); if (!out_buf) die("out of memory"); }
  out_buf[out_len++] = b;
}
static void put32(uint64_t v) { for (int k = 0; k < 4; k++) put((uint8_t)(v >> (8 * k))); }
static void put64(uint64_t v) { for (int k = 0; k < 8; k++) put((uint8_t)(v >> (8 * k))); }
static void put_nat(const ONat *n) {
  uint32_t bytes = 4 * n->len;
  while (bytes && !((n->limb[(bytes - 1) / 4] >> (8 * ((bytes - 1) % 4))) & 0xff)) bytes--;
  put32(bytes); for (uint32_t i = 0; i < bytes; i++) put((uint8_t)(n->limb[i / 4] >> (8 * (i % 4))));
}
static void put_label(uint32_t id) {
  put32(ob_label_len[id]); for (uint32_t i = 0; i < ob_label_len[id]; i++) put(ob_label_bytes[ob_label_off[id] + i]);
}
static void put_env(const Env *e) { put64(e ? e->len : 0); for (; e; e = e->next) put64(e->addr); }
static int64_t rom_find_nat(const ONat *n) {
  for (uint32_t i = 0; i < ob_node_count; i++)
    if (ob_tag[i] == T_NAT && nat_eq(nat_rom(i), n)) return i;
  return -1;
}
static void put_term_code(uint32_t code) { put(1); put32(code); }
static void put_origin(const Closure *c) {
  if (c->code >= 0) put_term_code((uint32_t)c->code);
  else { int64_t r = rom_find_nat(c->lit); if (r >= 0) put_term_code((uint32_t)r); else { put(0); put_nat(c->lit); } }
  put_env(c->env);
}
static void put_value(const Value *v) {
  put(v->tag);
  switch (v->tag) {
  case V_CLOSURE: put_term_code(v->code_or_label); put_env(v->env); break;
  case V_NATURAL: put_nat(v->nat); break;
  case V_BOOLEAN: put(v->b); break;
  case V_LABEL: put_label(v->code_or_label); break;
  case V_RECORD: put64(v->rec->len); for (uint64_t k = 0; k < v->rec->len; k++) { put_label(v->rec->f[k].label); put64(v->rec->f[k].addr); } break;
  case V_SPEC: case V_PROTO: put64(v->x); put64(v->y); break;
  case V_VARIANT: put_label(v->code_or_label); put64(v->x); break;
  }
}
static void put_pairs(const Pair *p, uint64_t n) { put64(n); for (uint64_t k = 0; k < n; k++) { put_label(p[k].label); put_term_code(p[k].code); } }
static void put_frame(const Frame *f) {
  put(f->tag);
  switch (f->tag) {
  case F_ARGUMENT: put_term_code(f->t1); put_env(f->env); break;
  case F_UPDATE: put64(f->addr); break;
  case F_FIELD: put_label(f->label); break;
  case F_REFLECT: case F_METADATA: case F_PROJECT: break;
  case F_EXTEND: case F_CASE: put_pairs(f->pairs, f->npairs); put_env(f->env); break;
  case F_CONDITION: case F_IFBOOL: put_term_code(f->t1); put_term_code(f->t2); put_env(f->env); break;
  case F_BINLEFT: put(f->prim); put_term_code(f->t1); put_env(f->env); break;
  case F_BINRIGHT: put(f->prim); put_value(&f->left); break;
  }
}
static void put_state(void) {
  out_len = 0; put('O'); put('B'); put('S'); put('1');
  put64(heap_len);
  for (uint64_t i = 0; i < heap_len; i++) {
    put(heap[i].st); put_origin(&heap[i].origin);
    if (heap[i].st == C_CACHED) put_value(&heap[i].value);
  }
  put(ctl.tag);
  switch (ctl.tag) {
  case K_EVALUATE: put_term_code(ctl.code); put_env(ctl.env); break;
  case K_ENTER: case K_BLACKHOLE: case K_YIELDED: put64(ctl.addr); break;
  case K_RETURNED: case K_COMPLETE: put_value(&ctl.value); break;
  case K_REFUSED: put(ctl.reason); break;
  }
  put64(stack_len);
  for (uint64_t i = stack_len; i-- > 0;) put_frame(&stk[i]);
}

/* A term written as a ROM index is reused; the codec writes `.nat` literals
   that ARE ROM nodes as ROM indices (the Lean encoder looks the term up first). */
static void canonical_rom_terms_check(void) {
  for (uint32_t i = 0; i < ob_node_count; i++) if (ob_tag[i] > T_DONE) die("ROM tag out of range");
  for (uint32_t i = 0; i < ob_response_count; i++) if (ob_responses[i] >= ob_node_count) die("response outside the ROM");
}

/* ---- decoder (resume from a State written by either side) ---- */
static const uint8_t *in_buf; static size_t in_len, in_pos;
static uint8_t get8(void) { if (in_pos >= in_len) die("state truncated"); return in_buf[in_pos++]; }
static uint64_t getn(int n) { uint64_t v = 0; for (int k = 0; k < n; k++) v |= (uint64_t)get8() << (8 * k); return v; }
static const ONat *get_nat(void) {
  uint32_t bytes = (uint32_t)getn(4); ONat *n = nat_alloc((bytes + 3) / 4); memset(n->limb, 0, 4 * (size_t)n->len);
  for (uint32_t i = 0; i < bytes; i++) n->limb[i / 4] |= (uint32_t)get8() << (8 * (i % 4));
  if (bytes && in_buf[in_pos - 1] == 0) die("non-minimal natural");
  return nat_norm(n);
}
static uint32_t get_label(void) {
  uint32_t len = (uint32_t)getn(4); if (in_pos + len > in_len) die("state truncated");
  for (uint32_t id = 0; id < ob_label_count; id++)
    if (ob_label_len[id] == len && !memcmp(ob_label_bytes + ob_label_off[id], in_buf + in_pos, len)) { in_pos += len; return id; }
  die("label outside the ROM"); return 0;
}
static uint32_t get_code(void) {
  if (get8() != 1) die("expected a ROM term");
  uint32_t c = (uint32_t)getn(4); if (c >= ob_node_count) die("ROM index out of range"); return c;
}
static const Env *get_env(void) {
  uint64_t len = getn(8); uint64_t *addrs = malloc((len ? len : 1) * 8);
  for (uint64_t k = 0; k < len; k++) addrs[k] = getn(8);
  const Env *e = NULL; for (uint64_t k = len; k-- > 0;) e = env_cons(addrs[k], e);
  free(addrs); return e;
}
static Value get_value(void) {
  Value v = v_simple(get8());
  switch (v.tag) {
  case V_CLOSURE: v.code_or_label = get_code(); v.env = get_env(); break;
  case V_NATURAL: v.nat = get_nat(); break;
  case V_BOOLEAN: v.b = get8(); if (v.b > 1) die("bad boolean"); break;
  case V_LABEL: v.code_or_label = get_label(); break;
  case V_RECORD: { uint64_t n = getn(8); Fields *r = arena(sizeof(Fields) + n * sizeof(Field)); r->len = n;
    for (uint64_t k = 0; k < n; k++) { r->f[k].label = get_label(); r->f[k].addr = getn(8); } v.rec = r; break; }
  case V_SPEC: case V_PROTO: v.x = getn(8); v.y = getn(8); break;
  case V_VARIANT: v.code_or_label = get_label(); v.x = getn(8); break;
  default: die("bad value tag");
  }
  return v;
}
static void get_pairs(Frame *f) {
  uint64_t n = getn(8); Pair *p = arena((n ? n : 1) * sizeof(Pair));
  for (uint64_t k = 0; k < n; k++) { p[k].label = get_label(); p[k].code = get_code(); }
  f->pairs = p; f->npairs = n;
}
static void load_state(const char *path) {
  FILE *fp = fopen(path, "rb"); if (!fp) die("cannot open resume state");
  fseek(fp, 0, SEEK_END); in_len = (size_t)ftell(fp); fseek(fp, 0, SEEK_SET);
  uint8_t *b = malloc(in_len ? in_len : 1); if (fread(b, 1, in_len, fp) != in_len) die("short read"); fclose(fp);
  in_buf = b; in_pos = 0;
  if (get8() != 'O' || get8() != 'B' || get8() != 'S' || get8() != '1') die("not objective-state.v1");
  uint64_t cells = getn(8);
  for (uint64_t i = 0; i < cells; i++) {
    Cell c; memset(&c, 0, sizeof c); c.st = get8(); if (c.st > C_CACHED) die("bad cell");
    uint8_t kind = get8();
    if (kind == 1) { c.origin.code = getn(4); if ((uint64_t)c.origin.code >= ob_node_count) die("ROM index out of range"); }
    else if (kind == 0) { c.origin.code = -1; c.origin.lit = get_nat(); if (c.st != C_CACHED) die("literal origin on a live cell"); }
    else die("bad term tag");
    c.origin.env = get_env();
    if (c.st == C_CACHED) c.value = get_value();
    heap_push(c);
  }
  ctl.tag = get8();
  switch (ctl.tag) {
  case K_EVALUATE: ctl.code = get_code(); ctl.env = get_env(); break;
  case K_ENTER: case K_BLACKHOLE: case K_YIELDED: ctl.addr = getn(8); break;
  case K_RETURNED: case K_COMPLETE: ctl.value = get_value(); break;
  case K_REFUSED: ctl.reason = get8(); if (ctl.reason > R_SHAREDEFFECT) die("bad refusal"); break;
  default: die("bad control");
  }
  uint64_t frames = getn(8); Frame *tmp = malloc((frames ? frames : 1) * sizeof(Frame));
  for (uint64_t k = 0; k < frames; k++) {
    Frame f = f_simple(get8());
    switch (f.tag) {
    case F_ARGUMENT: f.t1 = get_code(); f.env = get_env(); break;
    case F_UPDATE: f.addr = getn(8); break;
    case F_FIELD: f.label = get_label(); break;
    case F_REFLECT: case F_METADATA: case F_PROJECT: break;
    case F_EXTEND: case F_CASE: get_pairs(&f); f.env = get_env(); break;
    case F_CONDITION: case F_IFBOOL: f.t1 = get_code(); f.t2 = get_code(); f.env = get_env(); break;
    case F_BINLEFT: f.prim = get8(); f.t1 = get_code(); f.env = get_env(); break;
    case F_BINRIGHT: f.prim = get8(); f.left = get_value(); break;
    default: die("bad frame");
    }
    tmp[k] = f;
  }
  for (uint64_t k = frames; k-- > 0;) stack_push(tmp[k]);
  free(tmp);
  if (in_pos != in_len) die("trailing bytes after state");
}

/* ---- runBounded with the per-tick fingerprint ---- */
static uint64_t fnv(uint64_t h, uint8_t b) { return (h ^ b) * 0x100000001b3ULL; }
static uint64_t fingerprint(uint64_t h) {
  h = fnv(h, ctl.tag);
  for (int k = 0; k < 8; k++) h = fnv(h, (uint8_t)(heap_len >> (8 * k)));
  for (int k = 0; k < 8; k++) h = fnv(h, (uint8_t)(stack_len >> (8 * k)));
  return h;
}

int main(int argc, char **argv) {
  if (argc < 5 || argc > 7) { fprintf(stderr, "usage: %s HEAP STACK TICKS OUT_STATE [RESUME_STATE [FIRST_RESPONSE]]\n", argv[0]); return 2; }
  uint64_t heap_limit = strtoull(argv[1], NULL, 10), stack_limit = strtoull(argv[2], NULL, 10), ticks = strtoull(argv[3], NULL, 10);
  uint64_t next_response = argc == 7 ? strtoull(argv[6], NULL, 10) : 0, resumes = 0;
  canonical_rom_terms_check();
  if (argc >= 6 && strcmp(argv[5], "-") != 0) load_state(argv[5]); else { ctl.tag = K_EVALUATE; ctl.code = ob_entry; ctl.env = NULL; }
  uint64_t used = 0, hash = 0xcbf29ce484222325ULL; const char *outcome; char detail[64] = "";
  for (;;) {
    if (ctl.tag == K_COMPLETE) { outcome = "finished"; break; }
    if (ctl.tag == K_BLACKHOLE) { outcome = "divergent"; snprintf(detail, sizeof detail, "%llu", (unsigned long long)ctl.addr); break; }
    if (ctl.tag == K_REFUSED) { outcome = "refused"; snprintf(detail, sizeof detail, "%s", refusal_name[ctl.reason]); break; }
    if (ctl.tag == K_YIELDED) {                         /* Lean `resume`: heap and stack unchanged */
      if (next_response >= ob_response_count) { outcome = "yielded"; snprintf(detail, sizeof detail, "%llu", (unsigned long long)ctl.addr); break; }
      evaluate(ob_responses[next_response++], NULL); resumes++; continue;
    }
    if (used == ticks) { outcome = "suspended-ticks"; break; }
    undo_save(); step_raw();
    if (heap_len <= heap_limit && stack_len <= stack_limit) { used++; hash = fingerprint(hash); }
    else { undo_restore(); outcome = "suspended-capacity"; break; }
  }
  put_state();
  FILE *fp = fopen(argv[4], "wb"); if (!fp || fwrite(out_buf, 1, out_len, fp) != out_len) die("cannot write state"); fclose(fp);
  printf("{\"outcome\":\"%s\",\"detail\":\"%s\",\"ticks\":%llu,\"trace\":\"%016llx\",\"heap\":%llu,\"stack\":%llu,\"bytes\":%zu,\"resumes\":%llu}\n",
         outcome, detail, (unsigned long long)used, (unsigned long long)hash, (unsigned long long)heap_len,
         (unsigned long long)stack_len, out_len, (unsigned long long)resumes);
  return 0;
}
