/* The C side of libminidregg-intents.so: Lean runtime initialisation and ByteArray marshalling for the
 * mini-sdk `lean-codec` check, which dlopens this library and calls the exports of
 * Kernel.Contracts.Intents (`minidregg_intent_encode`, `minidregg_intent_id_preimage`) directly.
 * No codec logic lives here: lean.h's allocation and accessor helpers are static inline, so Rust
 * reaches them through these wrappers. */
#include <lean/lean.h>

#define MDI_EXPORT __attribute__((visibility("default")))

extern void lean_initialize(void);
extern lean_object *initialize_minidregg_Kernel_Contracts_Intents(uint8_t builtin);

/* As the generated `main` of a Lean executable whose closure imports `Lean` (Intents reads JSON through
 * Lean.Data.Json): initialise the whole runtime, then this module and its imports, then mark the end
 * of initialisation. */
MDI_EXPORT int mdi_init(void) {
  lean_initialize();
  lean_object *res = initialize_minidregg_Kernel_Contracts_Intents(1);
  lean_io_mark_end_initialization();
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
  lean_dec_ref(res);
  lean_init_task_manager();
  return 0;
}

MDI_EXPORT lean_object *mdi_bytes_new(const uint8_t *p, size_t n) {
  lean_object *a = lean_alloc_sarray(1, n, n);
  if (n) __builtin_memcpy(lean_sarray_cptr(a), p, n);
  return a;
}

MDI_EXPORT size_t mdi_bytes_len(lean_object *a) { return lean_sarray_size(a); }

MDI_EXPORT const uint8_t *mdi_bytes_ptr(lean_object *a) { return lean_sarray_cptr(a); }

MDI_EXPORT void mdi_dec(lean_object *a) { lean_dec(a); }
