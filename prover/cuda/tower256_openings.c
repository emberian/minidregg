/* Native receipt assembly for the GPU host's openings (tower256_gpu.py prove_gpu, round loop): the same bytes
 * the Python path writes, i.e. per query a: lo[a] (32 bytes), hi[a] (32 bytes), encode_nat(k - 1), then for
 * each level d < k - 1 encode_nat_le32(sibling[d][a]). encode_nat is StreamCodec's base-255 digits, least
 * significant first, terminated by 255. Build: cc -O2 -shared -fPIC -o tower256_openings.so tower256_openings.c
 * Bit-exact against the Python path: tower256_gpu.py --openings-check (both paths, every round, every query). */
#include <stdint.h>
#include <string.h>
#include <stddef.h>

static size_t enc_nat_u64(uint64_t v, uint8_t *o) {
    size_t n = 0;
    while (v) { o[n++] = (uint8_t)(v % 255); v /= 255; }
    o[n++] = 255; return n;
}
/* 256-bit little-endian value as 8 u32 limbs; repeated division by 255 */
static size_t enc_nat_256(const uint64_t w[4], uint8_t *o) {
    uint32_t l[8]; size_t n = 0; int top = 7;
    for (int i = 0; i < 4; i++) { l[2 * i] = (uint32_t)w[i]; l[2 * i + 1] = (uint32_t)(w[i] >> 32); }
    while (top >= 0 && !l[top]) top--;
    while (top >= 0) {
        uint64_t rem = 0;
        for (int k = top; k >= 0; k--) { uint64_t cur = (rem << 32) | l[k]; l[k] = (uint32_t)(cur / 255); rem = cur % 255; }
        o[n++] = (uint8_t)rem;
        while (top >= 0 && !l[top]) top--;
    }
    o[n++] = 255; return n;
}
/* Worst case per query: 64 + 9 + (k - 1) * 33 bytes (a 256-bit value has at most 33 base-255 digits). */
size_t t256_openings_bound(int q, int k) { return (size_t)q * (64 + 9 + (size_t)(k > 1 ? k - 1 : 0) * 34); }
size_t t256_openings(const uint64_t *lo, const uint64_t *hi, const uint64_t *sib, int q, int k, uint8_t *out) {
    uint8_t klen[16]; size_t kl = enc_nat_u64((uint64_t)(k - 1), klen), n = 0;
    for (int a = 0; a < q; a++) {
        memcpy(out + n, lo + 4 * (size_t)a, 32); n += 32;   /* rows are little-endian u64 x 4 = row_bytes */
        memcpy(out + n, hi + 4 * (size_t)a, 32); n += 32;
        memcpy(out + n, klen, kl); n += kl;
        for (int d = 0; d < k - 1; d++) n += enc_nat_256(sib + 4 * ((size_t)d * q + a), out + n);
    }
    return n;
}
