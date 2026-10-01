/* The C side of libminidregg-channel.so (CH-RELAY-1): Lean runtime initialisation and ByteArray
 * marshalling for `mini relay`, which dlopens this library and calls the channel exports of
 * Kernel.DomainEpochExport and Theory.Channel directly. No channel logic lives here: lean.h's
 * allocation and accessor helpers are static inline, so Rust reaches them through these wrappers. */
#include <lean/lean.h>

#define MDC_EXPORT __attribute__((visibility("default")))

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_minidregg_Kernel_DomainEpochExport(uint8_t builtin);

/* As the generated `main` of a Lean executable whose closure does NOT import `Lean`: initialise the
 * runtime only, then this module and its imports (which initialise the `Init` modules they reach), then
 * mark the end of initialisation. The closure is `Init` plus eight package modules (CH-CLIENT-1);
 * build.sh refuses to link if it ever reaches `Lean`, `Std`, Mathlib or another package again. */
MDC_EXPORT int mdc_init(void) {
  lean_initialize_runtime_module();
  lean_object *res = initialize_minidregg_Kernel_DomainEpochExport(1);
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

MDC_EXPORT lean_object *mdc_bytes_new(const uint8_t *p, size_t n) {
  lean_object *a = lean_alloc_sarray(1, n, n);
  if (n) __builtin_memcpy(lean_sarray_cptr(a), p, n);
  return a;
}

MDC_EXPORT size_t mdc_bytes_len(lean_object *a) { return lean_sarray_size(a); }

MDC_EXPORT const uint8_t *mdc_bytes_ptr(lean_object *a) { return lean_sarray_cptr(a); }

MDC_EXPORT void mdc_dec(lean_object *a) { lean_dec(a); }
