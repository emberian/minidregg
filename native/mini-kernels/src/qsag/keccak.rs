//! NIST FIPS 202 `Keccak-f[1600]` 24-round permutation, `SHAKE256` XOF, and
//! NIST SP 800-185 `cSHAKE256` customizable XOF in `#![no_std]` `#![forbid(unsafe_code)]` Rust.

/// Sponge rate of `SHAKE256` and `cSHAKE256` in bytes (`1088 / 8 = 136`).
pub const SHAKE256_RATE_BYTES: usize = 136;

/// Number of 64-bit lanes in the `SHAKE256` / `cSHAKE256` rate (`136 / 8 = 17`).
pub const SHAKE256_RATE_LANES: usize = 17;

/// Standard 24 NIST FIPS 202 `Keccak-f[1600]` round constants.
pub const KECCAK_ROUND_CONSTANTS: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// Single round (`iota o chi o pi o rho o theta`) of NIST FIPS 202 `Keccak-f[1600]`.
pub fn keccak_f1600_round(state: &mut [u64; 25], rc: u64) {
    // Theta
    let c0 = state[0] ^ state[5] ^ state[10] ^ state[15] ^ state[20];
    let c1 = state[1] ^ state[6] ^ state[11] ^ state[16] ^ state[21];
    let c2 = state[2] ^ state[7] ^ state[12] ^ state[17] ^ state[22];
    let c3 = state[3] ^ state[8] ^ state[13] ^ state[18] ^ state[23];
    let c4 = state[4] ^ state[9] ^ state[14] ^ state[19] ^ state[24];

    let d0 = c4 ^ c1.rotate_left(1);
    let d1 = c0 ^ c2.rotate_left(1);
    let d2 = c1 ^ c3.rotate_left(1);
    let d3 = c2 ^ c4.rotate_left(1);
    let d4 = c3 ^ c0.rotate_left(1);

    let a0 = state[0] ^ d0;
    let a1 = state[1] ^ d1;
    let a2 = state[2] ^ d2;
    let a3 = state[3] ^ d3;
    let a4 = state[4] ^ d4;
    let a5 = state[5] ^ d0;
    let a6 = state[6] ^ d1;
    let a7 = state[7] ^ d2;
    let a8 = state[8] ^ d3;
    let a9 = state[9] ^ d4;
    let a10 = state[10] ^ d0;
    let a11 = state[11] ^ d1;
    let a12 = state[12] ^ d2;
    let a13 = state[13] ^ d3;
    let a14 = state[14] ^ d4;
    let a15 = state[15] ^ d0;
    let a16 = state[16] ^ d1;
    let a17 = state[17] ^ d2;
    let a18 = state[18] ^ d3;
    let a19 = state[19] ^ d4;
    let a20 = state[20] ^ d0;
    let a21 = state[21] ^ d1;
    let a22 = state[22] ^ d2;
    let a23 = state[23] ^ d3;
    let a24 = state[24] ^ d4;

    // Rho + Pi
    let b0 = a0;
    let b10 = a1.rotate_left(1);
    let b20 = a2.rotate_left(62);
    let b5 = a3.rotate_left(28);
    let b15 = a4.rotate_left(27);
    let b16 = a5.rotate_left(36);
    let b1 = a6.rotate_left(44);
    let b11 = a7.rotate_left(6);
    let b21 = a8.rotate_left(55);
    let b6 = a9.rotate_left(20);
    let b7 = a10.rotate_left(3);
    let b17 = a11.rotate_left(10);
    let b2 = a12.rotate_left(43);
    let b12 = a13.rotate_left(25);
    let b22 = a14.rotate_left(39);
    let b23 = a15.rotate_left(41);
    let b8 = a16.rotate_left(45);
    let b18 = a17.rotate_left(15);
    let b3 = a18.rotate_left(21);
    let b13 = a19.rotate_left(8);
    let b14 = a20.rotate_left(18);
    let b24 = a21.rotate_left(2);
    let b9 = a22.rotate_left(61);
    let b19 = a23.rotate_left(56);
    let b4 = a24.rotate_left(14);

    // Chi + Iota
    state[0] = (b0 ^ ((!b1) & b2)) ^ rc;
    state[1] = b1 ^ ((!b2) & b3);
    state[2] = b2 ^ ((!b3) & b4);
    state[3] = b3 ^ ((!b4) & b0);
    state[4] = b4 ^ ((!b0) & b1);

    state[5] = b5 ^ ((!b6) & b7);
    state[6] = b6 ^ ((!b7) & b8);
    state[7] = b7 ^ ((!b8) & b9);
    state[8] = b8 ^ ((!b9) & b5);
    state[9] = b9 ^ ((!b5) & b6);

    state[10] = b10 ^ ((!b11) & b12);
    state[11] = b11 ^ ((!b12) & b13);
    state[12] = b12 ^ ((!b13) & b14);
    state[13] = b13 ^ ((!b14) & b10);
    state[14] = b14 ^ ((!b10) & b11);

    state[15] = b15 ^ ((!b16) & b17);
    state[16] = b16 ^ ((!b17) & b18);
    state[17] = b17 ^ ((!b18) & b19);
    state[18] = b18 ^ ((!b19) & b15);
    state[19] = b19 ^ ((!b15) & b16);

    state[20] = b20 ^ ((!b21) & b22);
    state[21] = b21 ^ ((!b22) & b23);
    state[22] = b22 ^ ((!b23) & b24);
    state[23] = b23 ^ ((!b24) & b20);
    state[24] = b24 ^ ((!b20) & b21);
}

/// Exact 24-round NIST FIPS 202 `Keccak-f[1600]` permutation over 25 little-endian 64-bit lanes.
pub fn keccak_f1600(state: &mut [u64; 25]) {
    keccak_f1600_round(state, 0x0000_0000_0000_0001);
    keccak_f1600_round(state, 0x0000_0000_0000_8082);
    keccak_f1600_round(state, 0x8000_0000_0000_808a);
    keccak_f1600_round(state, 0x8000_0000_8000_8000);
    keccak_f1600_round(state, 0x0000_0000_0000_808b);
    keccak_f1600_round(state, 0x0000_0000_8000_0001);
    keccak_f1600_round(state, 0x8000_0000_8000_8081);
    keccak_f1600_round(state, 0x8000_0000_0000_8009);
    keccak_f1600_round(state, 0x0000_0000_0000_008a);
    keccak_f1600_round(state, 0x0000_0000_0000_0088);
    keccak_f1600_round(state, 0x0000_0000_8000_8009);
    keccak_f1600_round(state, 0x0000_0000_8000_000a);
    keccak_f1600_round(state, 0x0000_0000_8000_808b);
    keccak_f1600_round(state, 0x8000_0000_0000_008b);
    keccak_f1600_round(state, 0x8000_0000_0000_8089);
    keccak_f1600_round(state, 0x8000_0000_0000_8003);
    keccak_f1600_round(state, 0x8000_0000_0000_8002);
    keccak_f1600_round(state, 0x8000_0000_0000_0080);
    keccak_f1600_round(state, 0x0000_0000_0000_800a);
    keccak_f1600_round(state, 0x8000_0000_8000_000a);
    keccak_f1600_round(state, 0x8000_0000_8000_8081);
    keccak_f1600_round(state, 0x8000_0000_0000_8080);
    keccak_f1600_round(state, 0x0000_0000_8000_0001);
    keccak_f1600_round(state, 0x8000_0000_8000_8008);
}

#[inline]
fn load_le_u64(block: &[u8; SHAKE256_RATE_BYTES], off: usize) -> u64 {
    (block[off] as u64)
        | ((block[off + 1] as u64) << 8)
        | ((block[off + 2] as u64) << 16)
        | ((block[off + 3] as u64) << 24)
        | ((block[off + 4] as u64) << 32)
        | ((block[off + 5] as u64) << 40)
        | ((block[off + 6] as u64) << 48)
        | ((block[off + 7] as u64) << 56)
}

fn xor_rate_block(state: &mut [u64; 25], block: &[u8; SHAKE256_RATE_BYTES]) {
    let mut lane_idx: usize = 0;
    while lane_idx < SHAKE256_RATE_LANES {
        let off = 8 * lane_idx;
        state[lane_idx] ^= load_le_u64(block, off);
        lane_idx += 1;
    }
}

/// Encode `value` via NIST SP 800-185 `left_encode` into a fixed stack buffer `(buf, len)`.
fn sp800_185_left_encode_u128(value: u128) -> ([u8; 17], usize) {
    if value == 0 {
        return ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 2);
    }
    let mut tmp = [0u8; 16];
    let mut n: usize = 0;
    let mut v = value;
    while v > 0 && n < 16 {
        tmp[n] = (v & 0xFF) as u8;
        v >>= 8;
        n += 1;
    }
    let mut out = [0u8; 17];
    out[0] = n as u8;
    let mut i: usize = 0;
    while i < n {
        out[1 + i] = tmp[n - 1 - i];
        i += 1;
    }
    (out, 1 + n)
}

/// Heap-free streaming NIST FIPS 202 `SHAKE256` / SP 800-185 `cSHAKE256` sponge.
#[derive(Clone)]
pub struct Shake256Sponge {
    pub state: [u64; 25],
    pub buf: [u8; SHAKE256_RATE_BYTES],
    pub buf_len: usize,
    pub suffix: u8,
    pub squeezing: bool,
    pub squeeze_offset: usize,
}

impl Shake256Sponge {
    /// Initialize uncustomized NIST FIPS 202 `SHAKE256` (`suffix = 0x1F`).
    pub const fn new_shake256() -> Self {
        Self {
            state: [0u64; 25],
            buf: [0u8; SHAKE256_RATE_BYTES],
            buf_len: 0,
            suffix: 0x1f,
            squeezing: false,
            squeeze_offset: 0,
        }
    }

    /// Initialize NIST SP 800-185 `cSHAKE256` (`N = ""`, caller customization `S`) in `O(1)` stack memory.
    /// The bit length is widened to `u128`, preserving every 64-bit slice length.
    /// Its SP 800-185 encoding uses a bounded stack buffer.
    pub fn new_cshake256(customization: &[u8]) -> Self {
        if customization.is_empty() {
            return Self::new_shake256();
        }
        let mut s = Self {
            state: [0u64; 25],
            buf: [0u8; SHAKE256_RATE_BYTES],
            buf_len: 0,
            suffix: 0x04,
            squeezing: false,
            squeeze_offset: 0,
        };
        // bytepad(encode_string("") || encode_string(S), 136):
        // left_encode(136) = [1, 136], encode_string("") = [1, 0]
        let header = [1u8, 136u8, 1u8, 0u8];
        s.absorb(&header);
        // A 64-bit slice length needs up to 67 bits when expressed in bits.
        let bit_len = (customization.len() as u128) * 8;
        let (len_enc, len_enc_bytes) = sp800_185_left_encode_u128(bit_len);
        let mut j: usize = 0;
        while j < len_enc_bytes {
            let single = [len_enc[j]];
            s.absorb(&single);
            j += 1;
        }
        s.absorb(customization);
        if s.buf_len > 0 && s.buf_len < SHAKE256_RATE_BYTES {
            let mut k = s.buf_len;
            while k < SHAKE256_RATE_BYTES {
                s.buf[k] = 0;
                k += 1;
            }
            xor_rate_block(&mut s.state, &s.buf);
            keccak_f1600(&mut s.state);
            s.buf_len = 0;
        }
        s
    }

    /// Absorb `data` into the sponge prior to squeezing.
    ///
    /// Panics once squeezing has begun, as production `Cshake256Xof::absorb` does
    /// (`crates/qsag-core/src/sponge/keccak.rs`): a late absorb is a caller bug, never a no-op.
    pub fn absorb(&mut self, data: &[u8]) {
        assert!(
            !self.squeezing,
            "cannot absorb into Shake256Sponge after squeezing began"
        );
        let mut pos: usize = 0;
        while pos < data.len() {
            if self.buf_len < SHAKE256_RATE_BYTES {
                self.buf[self.buf_len] = data[pos];
                self.buf_len += 1;
                pos += 1;
            }
            if self.buf_len == SHAKE256_RATE_BYTES {
                xor_rate_block(&mut self.state, &self.buf);
                keccak_f1600(&mut self.state);
                self.buf_len = 0;
            }
        }
    }

    /// Apply multi-rate domain-separation padding (`suffix` + `0x80`) and switch to squeezing.
    pub fn finalize(&mut self) {
        if self.squeezing {
            return;
        }
        if self.buf_len >= SHAKE256_RATE_BYTES {
            xor_rate_block(&mut self.state, &self.buf);
            keccak_f1600(&mut self.state);
            self.buf_len = 0;
        }
        let mut i = self.buf_len;
        while i < SHAKE256_RATE_BYTES {
            self.buf[i] = 0;
            i += 1;
        }
        self.buf[self.buf_len] ^= self.suffix;
        self.buf[SHAKE256_RATE_BYTES - 1] ^= 0x80;
        xor_rate_block(&mut self.state, &self.buf);
        keccak_f1600(&mut self.state);
        self.squeezing = true;
        self.squeeze_offset = 0;
    }

    /// Squeeze `out.len()` bytes from the sponge.
    pub fn squeeze(&mut self, out: &mut [u8]) {
        self.finalize();
        let mut written: usize = 0;
        while written < out.len() {
            if self.squeeze_offset >= SHAKE256_RATE_BYTES {
                keccak_f1600(&mut self.state);
                self.squeeze_offset = 0;
            }
            let lane_idx = self.squeeze_offset / 8;
            let byte_in_lane = (self.squeeze_offset % 8) as u32;
            let shift = 8 * byte_in_lane;
            out[written] = ((self.state[lane_idx] >> shift) & 0xFF) as u8;
            written += 1;
            self.squeeze_offset += 1;
        }
    }
}

/// Evaluate 32-byte NIST FIPS 202 `SHAKE256(input, 256)`.
pub fn shake256_32(input: &[u8]) -> [u8; 32] {
    let mut sp = Shake256Sponge::new_shake256();
    sp.absorb(input);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// Evaluate 32-byte NIST SP 800-185 `cSHAKE256(input, 256, "", customization)`.
pub fn cshake256_32(customization: &[u8], input: &[u8]) -> [u8; 32] {
    let mut sp = Shake256Sponge::new_cshake256(customization);
    sp.absorb(input);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

#[cfg(test)]
mod framing_tests {
    #[test]
    fn left_encode_does_not_saturate_large_bit_lengths() {
        for value in [0u128, 1, 255, 256, u64::MAX as u128, (u64::MAX as u128) * 8] {
            let (bytes, len) = super::sp800_185_left_encode_u128(value);
            assert_eq!(bytes[0] as usize + 1, len);
            assert_eq!(bytes[1..len].iter().fold(0u128, |v, b| (v << 8) | u128::from(*b)), value);
            assert!(len == 2 || bytes[1] != 0);
        }
    }
}
