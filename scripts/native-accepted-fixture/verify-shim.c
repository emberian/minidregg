/* verify-shim.c -- records every Ed25519 check a Lean re-run asks the linked native kernel.
 *
 * Live verification is in-process: `CredentialSignatureIO.ed25519Kernel` is compiled into
 * .lake/native/libmini_kernels_lean.so, and the interpreter calls its boxed entry point by symbol.
 * generate.sh builds this file into a shared library and loads it BEFORE the kernel library
 * (`--load-dynlib` order), so the interpreter resolves that symbol here; the shim records the
 * check, forwards to the kernel's own entry point (dlsym in $MINI_KERNELS_LIB, the kernel library
 * generate.sh loads) and returns its verdict
 * unchanged. One line per check is appended to $VERIFY_LOG: `KEY FRAME SIGNATURE VERDICT` (hex,
 * hex, hex, the kernel's verdict byte). generate.sh keeps the triples the kernel verified and
 * re-submits each to the pinned verifier binary; those are the transcript the fixture replays
 * without a process.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <lean/lean.h>

#define ENTRY lp_minidregg_Minidregg_Compiler_CredentialSignatureIO_ed25519Kernel___boxed
#define STR2(x) #x
#define STR(x) STR2(x)

typedef lean_object *(*entry_fn)(lean_object *, lean_object *, lean_object *);

static void put_hex(FILE *out, lean_object *bytes) {
  size_t n = lean_sarray_size(bytes);
  uint8_t const *p = lean_sarray_cptr(bytes);
  for (size_t i = 0; i < n; i++) fprintf(out, "%02x", p[i]);
}

lean_object *ENTRY(lean_object *key, lean_object *frame, lean_object *signature) {
  static entry_fn real = NULL;
  if (real == NULL) {
    char const *lib = getenv("MINI_KERNELS_LIB");
    void *kernels = lib != NULL ? dlopen(lib, RTLD_NOW | RTLD_LOCAL) : NULL;
    real = kernels != NULL ? (entry_fn)dlsym(kernels, STR(ENTRY)) : NULL;
    if (real == NULL) { fprintf(stderr, "verify-shim: no %s in MINI_KERNELS_LIB\n", STR(ENTRY)); abort(); }
  }
  char const *path = getenv("VERIFY_LOG");
  FILE *log = NULL;
  if (path != NULL) {
    /* read the arguments before forwarding: the boxed entry may release them */
    log = fopen(path, "a");
    if (log == NULL) { fprintf(stderr, "verify-shim: cannot open %s\n", path); abort(); }
    put_hex(log, key); fputc(' ', log); put_hex(log, frame); fputc(' ', log); put_hex(log, signature);
  }
  lean_object *verdict = real(key, frame, signature);
  if (log != NULL) {
    fprintf(log, " %u\n", (unsigned)lean_unbox(verdict));
    fclose(log);
  }
  return verdict;
}
