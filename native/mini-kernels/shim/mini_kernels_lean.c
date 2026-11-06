/* The Lean side of native/mini-kernels: ByteArray marshalling for the
 * `@[extern]` declarations in Theory/Sp800185Cshake256Native.lean,
 * Theory/Sp800185Cshake256Midstate.lean,
 * Compiler/Sp800185Kmac256.lean and Compiler/CredentialSignatureKernel.lean.
 * lean.h's allocation and accessor helpers are static inline, so the Rust
 * kernels never see a lean_object. All arguments are borrowed (`@&` in Lean:
 * b_lean_obj_arg); hashes return a fresh ByteArray and signature checks return
 * their UInt8 verdict code. No framing or admission semantics live here. */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

void mini_kernels_cshake256_32(const uint8_t *customization, size_t customization_len,
                               const uint8_t *input, size_t input_len, uint8_t *output);
size_t mini_kernels_cshake256_absorb(const uint8_t *customization, size_t customization_len,
                                     const uint8_t *prefix, size_t prefix_len, uint8_t *output);
void mini_kernels_cshake256_finish_32(const uint8_t *midstate, size_t midstate_len,
                                      const uint8_t *suffix, size_t suffix_len, uint8_t *output);
void mini_kernels_kmac256_32(const uint8_t *key, size_t key_len,
                             const uint8_t *customization, size_t customization_len,
                             const uint8_t *input, size_t input_len, uint8_t *output);
uint8_t mini_kernels_ed25519_verify(const uint8_t *public_key, size_t public_key_len,
                                    const uint8_t *frame, size_t frame_len,
                                    const uint8_t *signature, size_t signature_len);
uint8_t mini_kernels_sshsig_verify(const uint8_t *public_key, size_t public_key_len,
                                   const uint8_t *name_space, size_t name_space_len,
                                   const uint8_t *message, size_t message_len,
                                   const uint8_t *signature, size_t signature_len);

static lean_obj_res mini_kernels_fresh_32(void) {
  return lean_alloc_sarray(1, 32, 32);
}

LEAN_EXPORT lean_obj_res mini_cshake256_32(b_lean_obj_arg customization, b_lean_obj_arg input) {
  lean_obj_res out = mini_kernels_fresh_32();
  mini_kernels_cshake256_32(lean_sarray_cptr(customization), lean_sarray_size(customization),
                            lean_sarray_cptr(input), lean_sarray_size(input),
                            lean_sarray_cptr(out));
  return out;
}

/* The fixed part of a midstate (25 lanes and the suffix byte) and under one rate block of tail:
 * MIDSTATE_MAX_BYTES in native/mini-kernels/src/lib.rs. */
#define MINI_KERNELS_MIDSTATE_MAX 336

LEAN_EXPORT lean_obj_res mini_cshake256_absorb(b_lean_obj_arg customization, b_lean_obj_arg prefix) {
  uint8_t buffer[MINI_KERNELS_MIDSTATE_MAX];
  size_t length = mini_kernels_cshake256_absorb(lean_sarray_cptr(customization), lean_sarray_size(customization),
                                                lean_sarray_cptr(prefix), lean_sarray_size(prefix), buffer);
  lean_obj_res out = lean_alloc_sarray(1, length, length);
  uint8_t *target = lean_sarray_cptr(out);
  for (size_t i = 0; i < length; i++) target[i] = buffer[i];
  return out;
}

LEAN_EXPORT lean_obj_res mini_cshake256_finish_32(b_lean_obj_arg midstate, b_lean_obj_arg suffix) {
  lean_obj_res out = mini_kernels_fresh_32();
  mini_kernels_cshake256_finish_32(lean_sarray_cptr(midstate), lean_sarray_size(midstate),
                                   lean_sarray_cptr(suffix), lean_sarray_size(suffix),
                                   lean_sarray_cptr(out));
  return out;
}

LEAN_EXPORT lean_obj_res mini_kmac256_32(b_lean_obj_arg key, b_lean_obj_arg customization,
                                         b_lean_obj_arg input) {
  lean_obj_res out = mini_kernels_fresh_32();
  mini_kernels_kmac256_32(lean_sarray_cptr(key), lean_sarray_size(key),
                          lean_sarray_cptr(customization), lean_sarray_size(customization),
                          lean_sarray_cptr(input), lean_sarray_size(input),
                          lean_sarray_cptr(out));
  return out;
}

LEAN_EXPORT uint8_t mini_ed25519_verify(b_lean_obj_arg public_key, b_lean_obj_arg frame,
                                        b_lean_obj_arg signature) {
  return mini_kernels_ed25519_verify(
      lean_sarray_cptr(public_key), lean_sarray_size(public_key),
      lean_sarray_cptr(frame), lean_sarray_size(frame),
      lean_sarray_cptr(signature), lean_sarray_size(signature));
}

LEAN_EXPORT uint8_t mini_sshsig_verify(b_lean_obj_arg public_key, b_lean_obj_arg name_space,
                                       b_lean_obj_arg message, b_lean_obj_arg signature) {
  return mini_kernels_sshsig_verify(
      lean_sarray_cptr(public_key), lean_sarray_size(public_key),
      lean_sarray_cptr(name_space), lean_sarray_size(name_space),
      lean_sarray_cptr(message), lean_sarray_size(message),
      lean_sarray_cptr(signature), lean_sarray_size(signature));
}
