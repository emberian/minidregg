"""Work 9104 on a GPU: the Tower256 additive-FRI honest prover with its heavy loops on CUDA.

The host (this file) owns the transcript, the codecs and the receipt, ported from
prover/src/tower256_fri_fast.rs; the device (tower256_fri.cu) owns the encode (Gao-Mateer
additive FFT), the Merkle trees (one Keccak-f per leaf and per node from the cSHAKE midstate),
the folds and the final interpolation, all in Fan-Paar coordinates.

Checks, all bit-exact, none comparing a thing with itself:
  * device Keccak leaves and nodes against pycryptodome's cSHAKE256 on random inputs;
  * device Tower256 products and inverses against binary_tower_256.rs (mul_check.bin, written
    by the Rust reference multiplication);
  * the five Lean request/response pairs (tower256_fri_vectors.json): receipt bytes equal;
  * production-shape requests regenerated here from the Rust benchmark's SplitMix stream: the
    request's SHA3-256 equals Rust's, and the receipt's SHA3-256 and every root equal the
    Rust fast prover's (expect_ell*.json), itself checked against the conformance kernel.

    python3 tower256_gpu.py --data DIR [--ells 14,16] [--reps 3] [--backend cupy|emu]
                            [--cubin F | --lib F] [--rust-bench BIN] [--out results.json]
"""
import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import time

import numpy as np

MASK64 = (1 << 64) - 1

# ------------------------------------------------------------------------------------------
# Keccak and cSHAKE256 on the host (midstates; the transcript when pycryptodome is absent).

RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
      0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
      0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
      0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
      0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
      0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]


def _rotl(x, s):
    return ((x << s) | (x >> (64 - s))) & MASK64 if s else x


def keccak_f(a):
    """FIPS 202 Keccak-f[1600] on 25 lanes a[x + 5y] (written from the spec, not the .cu)."""
    for rnd in range(24):
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotl(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rotl(a[x + 5 * y], ROT[x][y])
        a = [b[i] ^ ((~b[(i % 5 + 1) % 5 + 5 * (i // 5)]) & b[(i % 5 + 2) % 5 + 5 * (i // 5)]) for i in range(25)]
        a[0] ^= RC[rnd]
    return a


def _left_encode(x):
    n = max(1, (x.bit_length() + 7) // 8)
    return bytes([n]) + x.to_bytes(n, "big")


class PyCShake:
    """cSHAKE256(N = "", S) with an absorb/clone/finish interface. Rate 136."""

    def __init__(self, custom):
        self.state = [0] * 25
        self.buf = b""
        z = _left_encode(0) + _left_encode(8 * len(custom)) + custom
        block = _left_encode(136) + z
        block += bytes((-len(block)) % 136)
        self.absorb(block)

    def clone(self):
        c = PyCShake.__new__(PyCShake)
        c.state, c.buf = list(self.state), self.buf
        return c

    def absorb(self, data):
        self.buf += data
        while len(self.buf) >= 136:
            blk, self.buf = self.buf[:136], self.buf[136:]
            for i in range(17):
                self.state[i] ^= int.from_bytes(blk[8 * i:8 * i + 8], "little")
            self.state = keccak_f(self.state)
        return self

    def finish32(self):
        blk = bytearray(self.buf + bytes(136 - len(self.buf)))
        blk[len(self.buf)] ^= 0x04
        blk[135] ^= 0x80
        st = list(self.state)
        for i in range(17):
            st[i] ^= int.from_bytes(blk[8 * i:8 * i + 8], "little")
        st = keccak_f(st)
        return b"".join(st[i].to_bytes(8, "little") for i in range(4))

    def midstate(self):
        assert self.buf == b""
        return list(self.state)


try:
    from Crypto.Hash import cSHAKE256 as _pyc_cshake  # pycryptodome
except Exception:  # noqa: BLE001
    _pyc_cshake = None


def xof32(custom, data):
    if _pyc_cshake is not None:
        return _pyc_cshake.new(data=data, custom=custom).read(32)
    return PyCShake(custom).absorb(data).finish32()


LEAF_CUSTOM = b"\x01MINIDREGG/TOWER256/MERKLE/LEAF/V1"
NODE_CUSTOM = b"\x02MINIDREGG/TOWER256/MERKLE/NODE/V1"
CHALLENGE_CUSTOM = b"MD-FRI-C"
QUERY_CUSTOM = b"MD-FRI-Q"

# ------------------------------------------------------------------------------------------
# Codecs (Theory/StreamCodec.lean; Tower256CshakeMerkleController framing)


def encode_nat(out, v):
    while v > 0:
        out.append(v % 255)
        v //= 255
    out.append(255)


def encode_nat_le32(out, digest):
    encode_nat(out, int.from_bytes(digest, "little"))


def encode_nat_le32_rows(rows):
    """encode_nat_le32 of many digests at once ((N, 4) uint64 rows): base-255 digits by long
    division of all rows together on 32-bit limbs. Returns a list of byte strings."""
    n = rows.shape[0]
    if n == 0:
        return []
    limbs = np.ascontiguousarray(rows, dtype="<u8").view("<u4").reshape(n, 8).astype(np.uint64)
    digits, alive = [], []
    while True:
        live = limbs.any(axis=1)
        if not live.any():
            break
        rem = np.zeros(n, dtype=np.uint64)
        for k in range(7, -1, -1):
            cur = (rem << np.uint64(32)) | limbs[:, k]
            limbs[:, k] = cur // np.uint64(255)
            rem = cur % np.uint64(255)
        digits.append(rem.astype(np.uint8))
        alive.append(live)
    if not digits:
        return [b"\xff"] * n
    d = np.stack(digits, axis=1)
    cnt = np.stack(alive, axis=1).sum(axis=1)
    return [d[i, :cnt[i]].tobytes() + b"\xff" for i in range(n)]


def encode_length(out, n):
    out.extend(bytes(n))
    out.append(1)


def envelope(out, data):
    encode_length(out, len(data))
    out.extend(data)


class RequestError(Exception):
    pass


class ProveError(Exception):
    pass


def decode_request(b):
    pos = [0]

    def byte():
        if pos[0] >= len(b):
            raise RequestError("truncated")
        pos[0] += 1
        return b[pos[0] - 1]

    def nat():
        digits = []
        while True:
            x = byte()
            if x == 255:
                break
            digits.append(x)
        if digits and digits[-1] == 0:
            raise RequestError("non-canonical natural")
        v = 0
        for d in reversed(digits):
            v = v * 255 + d
        return v

    def take(n):
        if pos[0] + n > len(b):
            raise RequestError("truncated")
        pos[0] += n
        return bytes(b[pos[0] - n:pos[0]])

    def c8_list():
        n = nat()
        if n > len(b):
            raise RequestError("list longer than the request")
        return [take(32) for _ in range(n)]

    st = take(nat())
    ell, m, q = nat(), nat(), nat()
    beta = c8_list()
    offset = take(32)
    dn = nat()
    if dn > len(b):
        raise RequestError("list longer than the request")
    degree = [nat() for _ in range(dn)]
    word = elems_to_array(c8_list())
    if pos[0] != len(b):
        raise RequestError("trailing bytes")
    return dict(statement=st, ell=ell, m=m, q=q, beta=beta, offset=offset, degree=degree, word=word)


def encode_request(r):
    out = bytearray()
    encode_nat(out, len(r["statement"]))
    out += r["statement"]
    for k in ("ell", "m", "q"):
        encode_nat(out, r[k])
    encode_nat(out, len(r["beta"]))
    for x in r["beta"]:
        out += x
    out += r["offset"]
    encode_nat(out, len(r["degree"]))
    for d in r["degree"]:
        encode_nat(out, d)
    encode_nat(out, r["word"].shape[0])
    out += np.ascontiguousarray(r["word"], dtype="<u8").tobytes()
    return bytes(out)


GAMMA = np.uint64(0x9E3779B97F4A7C15)


def sm_draws(seed, count):
    """SplitMix64 outputs 1..count from `seed` (the Rust `splitmix`), vectorized."""
    z = np.uint64(seed) + np.arange(1, count + 1, dtype=np.uint64) * GAMMA
    z = (z ^ (z >> np.uint64(30))) * np.uint64(0xBF58476D1CE4E5B9)
    z = (z ^ (z >> np.uint64(27))) * np.uint64(0x94D049BB133111EB)
    return z ^ (z >> np.uint64(31))


def production_request(ell):
    """tower256_fri_fast_bench.rs production_request: lb 2, m = ell - 4, q 148, final degree 4."""
    lb, m = 2, ell - 4
    n = 1 << (ell - lb)
    d = sm_draws(0x70430000 + ell, 48 + 4 * ell + 4 + 4 * n)
    st = bytes((d[:48] & np.uint64(0xFF)).astype(np.uint8))
    el = lambda x: np.ascontiguousarray(x, dtype="<u8").tobytes()
    beta = [el(d[48 + 4 * i:52 + 4 * i]) for i in range(ell)]
    o = 48 + 4 * ell
    return dict(statement=st, ell=ell, m=m, q=148, beta=beta, offset=el(d[o:o + 4]),
                degree=[1 << (ell - lb - j) for j in range(m + 1)], word=d[o + 4:].reshape(n, 4).copy())


def batch_request(ell, b):
    """tower256_fri_fast_bench.rs batch_request: leaf b of the end-to-end batch."""
    r = production_request(ell)
    if b:
        n = r["word"].shape[0]
        d = sm_draws(0xE2E000000000 + (ell << 20) + b, 48 + 4 * n)
        r["statement"] = bytes((d[:48] & np.uint64(0xFF)).astype(np.uint8))
        r["word"] = d[48:].reshape(n, 4).copy()
    return r


# ------------------------------------------------------------------------------------------
# Backends: the same kernels on a GPU (cupy) or as the host-C++ emulation build (ctypes).


class CupyBackend:
    name = "cupy"

    def __init__(self, cubin=None, source=None):
        import cupy as cp

        self.cp = cp
        self.xp = cp
        if cubin:
            self.mod = cp.RawModule(path=cubin)
        else:  # NVRTC, when no nvcc is installed
            self.mod = cp.RawModule(code=open(source).read(), backend="nvrtc", options=("-std=c++17",))
        self.fns = {}
        self.sms = cp.cuda.runtime.getDeviceProperties(0)["multiProcessorCount"]
        self.call("init_tables", 1)
        self.call("init_prod", 65536)
        cp.cuda.runtime.deviceSynchronize()

    def call(self, name, n, *args):
        if n == 0:
            return
        f = self.fns.get(name)
        if f is None:
            f = self.fns[name] = self.mod.get_function(name)
            if name.endswith("_full"):
                f.max_dynamic_shared_size_bytes = 65536
        conv = tuple(a if isinstance(a, self.cp.ndarray) else np.uint64(a) for a in args) + (np.uint64(n),)
        if name.endswith("_full"):
            # One 1024-thread block per SM (the 64 KiB table fills its shared memory), grid-stride.
            f((min(self.sms, (n + 1023) // 1024),), (1024,), conv, shared_mem=65536)
        else:
            f(((n + 255) // 256,), (256,), conv)

    def asarray(self, x):
        return self.cp.ascontiguousarray(self.cp.asarray(x, dtype=np.uint64))

    def host(self, x):
        return self.cp.asnumpy(x)

    def sync(self):
        self.cp.cuda.runtime.deviceSynchronize()

    def ptr(self, x):
        return int(x.data.ptr)

    def streams(self, k):
        if not hasattr(self, "_streams"):
            self._streams = []
        while len(self._streams) < k:
            self._streams.append(self.cp.cuda.Stream(non_blocking=True))
        return self._streams[:k]


class EmuBackend:
    name = "emu"

    def __init__(self, lib):
        import ctypes

        self.ct = ctypes
        self.lib = ctypes.CDLL(lib)
        self.xp = np
        self.call("init_tables", 1)
        self.call("init_prod", 65536)

    def call(self, name, n, *args):
        if n == 0:
            return
        conv = []
        for a in args:
            if isinstance(a, np.ndarray):
                assert a.flags["C_CONTIGUOUS"] and a.dtype == np.uint64, name
                conv.append(self.ct.c_void_p(a.ctypes.data))
            else:
                conv.append(self.ct.c_ulonglong(int(a)))
        conv.append(self.ct.c_ulonglong(n))
        getattr(self.lib, name)(*conv)

    def asarray(self, x):
        return np.ascontiguousarray(np.asarray(x, dtype=np.uint64))

    def host(self, x):
        return np.asarray(x)

    def sync(self):
        pass

    def ptr(self, x):
        assert x.flags["C_CONTIGUOUS"]
        return int(x.ctypes.data)

    def streams(self, k):
        import contextlib
        return [contextlib.nullcontext()]


def elems_to_array(elems):
    """32-byte little-endian elements -> (n, 4) uint64."""
    if not elems:
        return np.zeros((0, 4), dtype=np.uint64)
    return np.frombuffer(b"".join(elems), dtype="<u8").reshape(-1, 4).astype(np.uint64)


def row_bytes(row):
    return np.asarray(row, dtype="<u8").tobytes()


class Dev:
    """Field and hash operations over backend arrays of shape (n, 4)."""

    def __init__(self, be, mul="logexp"):
        self.be = be
        # Bulk multiply kernels: log/exp tables (768 B shared) or the 64 KiB product table.
        self.mulv = mul
        self.k = {n: n + ("_full" if mul == "full" else "") for n in ("t256_mul", "ntt_scale", "ntt_butterfly", "fri_fold")}
        self.xp = be.xp
        self.one = be.asarray(np.array([[1, 0, 0, 0]], dtype=np.uint64))
        self.leaf_mid = be.asarray(np.array(PyCShake(LEAF_CUSTOM).midstate(), dtype=np.uint64))
        self.node_mid = be.asarray(np.array(PyCShake(NODE_CUSTOM).midstate(), dtype=np.uint64))
        self.counts = {"mul": 0, "keccak": 0}
        self.setup = {}   # statement-constant device data, built once per shape
        self.query_mid = be.asarray(np.array(PyCShake(QUERY_CUSTOM).midstate(), dtype=np.uint64))
        pw = [255 ** k for k in range(33)]
        self.pow255 = be.asarray(np.array([[(v >> (64 * i)) & MASK64 for i in range(4)] for v in pw], dtype=np.uint64))

    def bulk(self, name, items, *args):
        """A bulk multiply kernel over `items` work items: the bit-sliced fused variant (32 items
        per thread) when chosen and items is a multiple of 32, else the table kernel."""
        if self.mulv == "bs" and items >= 32 and items % 32 == 0:
            self.be.call(name + "_bsx", items // 32, *args)
        else:
            self.be.call(self.k[name], items, *args)

    def empty(self, n):
        return self.xp.zeros((n, 4), dtype=np.uint64)

    def c(self, x):
        return self.xp.ascontiguousarray(x)

    def mul(self, a, b):
        """a * b elementwise; b may be one row (a scalar)."""
        a, b = self.c(a), self.c(b)
        out = self.empty(a.shape[0])
        self.bulk("t256_mul", a.shape[0], a, b, out, 0 if b.shape[0] == 1 else 1)
        self.counts["mul"] += a.shape[0]
        return out

    def inv(self, a):
        a = self.c(a)
        out = self.empty(a.shape[0])
        self.be.call("t256_inv", a.shape[0], a, out)
        return out

    def is_zero_row(self, a):
        return not bool(self.be.host(a).any())

    def pivot_map(self, x, p):
        x, p = self.c(x), self.c(p)
        out = self.empty(x.shape[0])
        self.be.call("t256_pivot_map", x.shape[0], x, p, out)
        self.counts["mul"] += 2 * x.shape[0]
        return out

    def span(self, offset, basis):
        n = 1 << basis.shape[0]
        out = self.empty(n)
        b = self.c(basis) if basis.shape[0] else self.empty(1)
        self.be.call("t256_span", n, self.c(offset), b, out)
        return out

    def powers(self, base, n):
        """base^i for i < n (n a power of two)."""
        logn = max(0, (n - 1).bit_length())
        h = logn // 2
        lo = self.empty(1 << h)
        hi = self.empty(max(1, n >> h))
        base = self.c(base)
        self.be.call("t256_pow_small", lo.shape[0], base, lo, 0)
        self.be.call("t256_pow_small", hi.shape[0], base, hi, h)
        out = self.empty(n)
        self.be.call("t256_pow_combine", n, lo, hi, out, h)
        self.counts["mul"] += n
        return out

    def eval_subspace(self, coeffs, offset, basis, batch=1):
        """Gao-Mateer, as tower256_fri_fast.rs eval_subspace: f on offset + span(basis).
        batch > 1: `batch` polynomials of one power-of-two length side by side, every
        depth's kernels run over all of them at once; the words come back side by side."""
        k = basis.shape[0]
        n = 1 << k
        if batch == 1:
            nz = np.nonzero(self.be.host(coeffs).any(axis=1))[0]
            used = int(nz[-1]) + 1 if len(nz) else 0
            if used == 0:
                return self.empty(n)
            l = 1 << (used - 1).bit_length()
        else:
            used = l = coeffs.shape[0] // batch
            assert l * batch == coeffs.shape[0] and l & (l - 1) == 0 and l <= n
        # Per-depth parameters depend only on the domain and l: built once per shape (setup).
        key = ("ntt", l, self.be.host(offset).tobytes(), self.be.host(basis).tobytes())
        if key not in self.setup:
            depths = []
            s, bs, block = self.c(offset), self.c(basis), l
            while block > 1 and bs.shape[0] > 0:
                b0 = bs[0:1]
                if self.is_zero_row(b0):
                    depths = None
                    break
                inv = self.inv(b0)
                powers = self.powers(b0, block)
                t = self.mul(s, inv)
                gamma = self.mul(bs[1:], inv) if bs.shape[0] > 1 else self.empty(0)
                z = self.span(t, gamma)
                s = self.pivot_map(t, self.one)
                bs = self.pivot_map(gamma, self.one) if gamma.shape[0] else self.empty(0)
                depths.append((powers, z))
                block //= 2
            self.setup[key] = (depths, s)
        depths, s = self.setup[key]
        if depths is None:
            assert batch == 1
            xs = self.span(offset, basis)
            out = self.empty(n)
            self.be.call("horner_points", n, self.c(coeffs[:used]), xs, out, used)
            self.counts["mul"] += n * used
            return out
        L, N = l * batch, n * batch
        if batch == 1:
            a = self.empty(l)
            a[:used] = coeffs[:used]
        else:
            a = self.c(coeffs).copy()
        tmp = self.empty(L)
        for d, (powers, _) in enumerate(depths):
            bsz = l >> d
            self.bulk("ntt_scale", L, a, powers, tmp, bsz)
            self.counts["mul"] += L
            sz = bsz
            while sz >= 4:
                self.be.call("ntt_taylor_step", (L // sz) * (sz // 4), tmp, sz)
                sz //= 2
            self.be.call("ntt_deinterleave", L // 2, tmp, a, bsz)
        d_end = len(depths)
        leaf_size, leaf_len = n >> d_end, l >> d_end
        cur = self.empty(N)
        if leaf_len == 1:
            self.be.call("ntt_fill", N, a, cur, leaf_size)
        else:
            self.be.call("ntt_horner_blocks", N, a, s, cur, leaf_len)
        nxt = self.empty(N)
        for d in reversed(range(d_end)):
            size = n >> d
            self.bulk("ntt_butterfly", N // 2, cur, depths[d][1], nxt, size)
            self.counts["mul"] += N // 2
            cur, nxt = nxt, cur
        return cur

    def tree(self, word, store, batch=1):
        """Cube tree levels: levels[t] has 2^t digests (levels[0] the root). batch > 1:
        that many trees side by side; levels[0] holds the batch's roots."""
        n = word.shape[0] // batch
        k = n.bit_length() - 1
        cur = self.empty(n * batch)
        self.be.call("merkle_leaves", n * batch, self.c(word), self.leaf_mid, cur)
        levels = [None] * (k + 1)
        for t in reversed(range(k)):
            h = 1 << t
            nxt = self.empty(h * batch)
            self.be.call("merkle_nodes", h * batch, cur, self.node_mid, nxt, h)
            if store and t + 1 < k:
                levels[t + 1] = cur
            cur = nxt
        levels[0] = cur
        self.counts["keccak"] += (2 * n - 1) * batch
        return levels

    def fold(self, w, c):
        half = w.shape[0] // 2
        out = self.empty(half)
        self.bulk("fri_fold", half, self.c(w), self.c(c), out)
        self.counts["mul"] += half
        return out


def natlen(v):
    c = 1
    while v:
        c += 1
        v //= 255
    return c


def prove_steps(dev, reqs, out, sync_timing=False):
    """Generator: proves `reqs` (one shape, basis, offset and degree schedule; statements of one
    length) as one batch on the current stream, every proof's receipt bytes identical to the CPU
    prover's (tower256_fri_fast.rs). It yields before each host read, so a driver can interleave
    batches on separate streams. Fills out["receipts"], out["roots"], out["phases"]."""
    be, xp = dev.be, dev.xp
    B, r0 = len(reqs), reqs[0]
    ell, m, q = r0["ell"], r0["m"], r0["q"]
    for r in reqs:
        assert (r["ell"], r["m"], r["q"], r["beta"], r["offset"], r["degree"]) == \
            (ell, m, q, r0["beta"], r0["offset"], r0["degree"]) and len(r["statement"]) == len(r0["statement"])
    if m > ell or ell > 24 or ell == 0:
        raise ProveError("Shape")
    if len(r0["beta"]) != ell:
        raise ProveError("BasisLength")
    final_degree = r0["degree"][m] if m < len(r0["degree"]) else 0
    last_size = 1 << (ell - m)
    if final_degree > last_size:
        raise ProveError("FinalDegree")
    if final_degree > 16:
        raise ProveError("final degree above the device kernel's 16")
    tm = out.setdefault("phases", {})
    for key in ("upload", "encode", "merkle", "folds", "final", "seeds", "openings", "host", "readback"):
        tm.setdefault(key, 0.0)

    def tick():
        if sync_timing:
            be.sync()
        return time.perf_counter()

    t0 = tick()
    beta = be.asarray(elems_to_array(r0["beta"]))
    offset = be.asarray(elems_to_array([r0["offset"]]))
    wl = max(r["word"].shape[0] for r in reqs)
    l = 1 << max(0, (wl - 1).bit_length()) if wl else 1
    host_coeffs = np.zeros((B * l, 4), dtype=np.uint64)
    for b, r in enumerate(reqs):
        host_coeffs[b * l:b * l + r["word"].shape[0]] = r["word"]
    coeffs = be.asarray(host_coeffs)
    t1 = tick()
    tm["upload"] += t1 - t0
    # Round maps, inverse pivots, the folds' shared spans and the last domain depend only on the
    # statement's domain: built once per shape (setup), like the FFT's depth parameters.
    skey = ("rounds", ell, m, final_degree, tuple(r0["beta"]), r0["offset"])
    if skey not in dev.setup:
        imgs, pinvs, spans = [], [], []
        cur = xp.concatenate([offset, beta], axis=0)
        for j in range(m):
            p = cur[1 + (ell - 1 - j):2 + (ell - 1 - j)]
            if dev.is_zero_row(p):
                raise ProveError("ZeroPivot(%d)" % j)
            imgs.append(cur)
            pinvs.append(dev.inv(p))
            k = ell - j
            scaled = dev.mul(cur[1:k], pinvs[-1]) if k > 1 else dev.empty(0)
            spans.append(dev.span(dev.mul(cur[0:1], pinvs[-1]), scaled))
            cur = dev.pivot_map(cur, p)
        imgs.append(cur)
        dom_m = dev.span(cur[0:1], cur[1:1 + (ell - m)])
        dev.setup[skey] = (pinvs, spans, dom_m)
    pinvs, spans, dom_m = dev.setup[skey]
    bp, tmp = bytearray(), bytearray()
    encode_length(tmp, ell)
    envelope(bp, tmp)
    tmp = bytearray()
    encode_length(tmp, m)
    envelope(bp, tmp)
    envelope(bp, r0["offset"])
    for i, bb in enumerate(r0["beta"]):
        inner, tmp = bytearray(), bytearray()
        encode_length(tmp, i)
        envelope(inner, tmp)
        envelope(inner, bb)
        envelope(bp, inner)
    trans = []
    for r in reqs:
        h = bytearray()
        envelope(h, r["statement"])
        envelope(h, bp)
        trans.append(h)
    t2 = tick()
    tm["host"] += t2 - t1
    if B == 1:
        w0 = dev.eval_subspace(coeffs, offset, beta)
    else:
        w0 = dev.eval_subspace(coeffs, offset, beta, B)
    t3 = tick()
    tm["encode"] += t3 - t2
    words, trees = [w0], [dev.tree(w0, m > 0, B)]
    t4 = tick()
    tm["merkle"] += t4 - t3
    yield
    roots = [[row_bytes(x)] for x in be.host(trees[0][0])]
    challenges = [[] for _ in range(B)]

    def push_root(buf, n, root):
        tmp = bytearray()
        encode_length(tmp, n)
        envelope(buf, tmp)
        envelope(buf, root)

    for b in range(B):
        push_root(trans[b], 0, roots[b][0])
    t5 = tick()
    tm["readback"] += t5 - t4
    for j in range(m):
        t0 = tick()
        al = []
        for b in range(B):
            ab = xof32(CHALLENGE_CUSTOM, bytes(trans[b]))
            challenges[b].append(ab)
            al.append(ab)
        alpha = be.asarray(elems_to_array(al))
        t1 = tick()
        tm["host"] += t1 - t0
        k = ell - j
        half = 1 << (k - 1)
        S = spans[j]
        dv = dev.mul(alpha, pinvs[j])
        nxt = dev.empty(B * half)
        be.call("fri_fold_batch", B * half, dev.c(words[j]), S, dv, nxt, half)
        dev.counts["mul"] += B * half
        words.append(nxt)
        t2 = tick()
        tm["folds"] += t2 - t1
        if j + 1 < m:
            trees.append(dev.tree(nxt, True, B))
            t3 = tick()
            tm["merkle"] += t3 - t2
            yield
            for b, x in enumerate(be.host(trees[-1][0])):
                roots[b].append(row_bytes(x))
                push_root(trans[b], j + 1, roots[b][-1])
            tm["readback"] += tick() - t3
    t0 = tick()
    fd = final_degree
    fco = dev.empty(B * max(fd, 1))
    vals = dev.empty(B * last_size)
    status = xp.zeros((B,), dtype=np.uint64)
    be.call("fri_final", B, dev.c(dom_m[:max(fd, 1)]), dev.c(words[m]), dom_m, fco, vals, status, fd, last_size,
            last_size)
    t1 = tick()
    tm["final"] += t1 - t0
    last_tree = dev.tree(vals, False, B) if m > 0 else None
    t2 = tick()
    tm["merkle"] += t2 - t1
    yield
    if be.host(status).any():
        raise ProveError("SingularInterpolation")
    fco_h = be.host(fco).reshape(B, max(fd, 1), 4)
    if last_tree is not None:
        for b, x in enumerate(be.host(last_tree[0])):
            roots[b].append(row_bytes(x))
            push_root(trans[b], m, roots[b][-1])
    t3 = tick()
    tm["readback"] += t3 - t2
    # The query prefix: roots 0..m (already in trans) and the challenges.
    for b in range(B):
        for cb in challenges[b]:
            envelope(trans[b], cb)
    seeds_dev = None
    if q:
        P = len(trans[0])
        assert all(len(t) == P for t in trans)
        nb, r_ = P // 136, P % 136
        blocks = np.frombuffer(b"".join(bytes(t[:nb * 136]) for t in trans), dtype="<u8").astype(np.uint64)
        rem = np.zeros((B, 17), dtype=np.uint64)
        rem_b = np.frombuffer(b"".join(bytes(t[nb * 136:]) + bytes(136 - r_) for t in trans), dtype="<u8")
        rem[:] = rem_b.reshape(B, 17)
        states = xp.zeros((B, 25), dtype=np.uint64)
        t4 = tick()
        tm["host"] += t4 - t3
        be.call("cshake_absorb", B, dev.query_mid, be.asarray(blocks) if nb else dev.empty(1), states, nb)
        seeds_dev = xp.zeros((B * q,), dtype=np.uint64)
        be.call("query_seeds", B * q, states, be.asarray(rem), seeds_dev, r_, q, ell - 1)
        t3 = tick()
        tm["seeds"] += t3 - t4
    hq, hm = natlen(q), natlen(m)
    blob = None
    if m and q:
        wptr = be.asarray(np.array([be.ptr(words[j]) for j in range(m)], dtype=np.uint64))
        lp = np.zeros((m, 32), dtype=np.uint64)
        for j in range(m):
            for t in range(1, ell - j):
                lp[j, t] = be.ptr(trees[j][t])
        lptr = be.asarray(lp)
        n_rec = B * m * q
        lens = xp.zeros((n_rec,), dtype=np.uint64)
        be.call("open_lengths", n_rec, seeds_dev, wptr, lptr, dev.pow255, lens, ell, m, q)
        L = lens.reshape(B, m * q).astype(np.int64)
        first = xp.zeros((m * q,), dtype=np.int64)
        first[::q] = hq
        L = L + first[None, :]
        tot = hm + L.sum(axis=1)
        base = xp.cumsum(tot) - tot
        offs = (base[:, None] + hm + xp.cumsum(L, axis=1) - L + first[None, :]).astype(np.uint64).reshape(-1)
        total = int(be.host(tot).sum())
        buf = xp.zeros(((total + 7) // 8,), dtype=np.uint64)
        be.call("open_write", n_rec, seeds_dev, wptr, lptr, xp.ascontiguousarray(offs), buf, ell, m, q)
        t4 = tick()
        tm["openings"] += t4 - t3
        t3 = t4
    yield
    seeds_h = be.host(seeds_dev).reshape(B, q) if q else np.zeros((B, 0), dtype=np.uint64)
    if m and q:
        tot_h, base_h = be.host(tot), be.host(base)
        blob = be.host(buf).view(np.uint8)
    t4 = tick()
    tm["readback"] += t4 - t3
    receipts = []
    for b in range(B):
        o = bytearray()
        encode_nat(o, m + 1)
        for rt in roots[b][:m + 1]:
            encode_nat_le32(o, rt)
        encode_nat(o, m)
        for cb in challenges[b]:
            o += cb
        encode_nat(o, q)
        for s_ in seeds_h[b]:
            encode_nat(o, int(s_))
        if m and q:
            o += blob[int(base_h[b]):int(base_h[b]) + int(tot_h[b])].tobytes()
        else:
            encode_nat(o, m)
            for _ in range(m):
                encode_nat(o, q)
        encode_nat(o, fd)
        for c in range(fd):
            o += row_bytes(fco_h[b, c])
        receipts.append(bytes(o))
    tm["host"] += tick() - t4
    out["receipts"], out["roots"] = receipts, roots


def prove_batches(dev, reqs, streams=1, sync_timing=False, sub=None):
    """Proves reqs in sub-batches of `sub` (default: all), interleaved over `streams` CUDA streams:
    a sub-batch's host work (challenges, receipt assembly) overlaps another's kernels."""
    be = dev.be
    sub = sub or len(reqs)
    parts = [reqs[i:i + sub] for i in range(0, len(reqs), sub)]
    outs = [{} for _ in parts]
    gens = [prove_steps(dev, p, o, sync_timing) for p, o in zip(parts, outs)]
    ctx = be.streams(streams)
    live = list(range(len(gens)))
    slot = {g: ctx[i % len(ctx)] for i, g in enumerate(live)}
    while live:
        for g in list(live):
            with slot[g]:
                try:
                    next(gens[g])
                except StopIteration:
                    live.remove(g)
    be.sync()
    receipts, roots, phases = [], [], {}
    for o in outs:
        receipts += o["receipts"]
        roots += o["roots"]
        for k, v in o["phases"].items():
            phases[k] = phases.get(k, 0.0) + v
    return receipts, roots, phases


def prove_gpu(dev, r, timings=None):
    """One proof (the batch path at B = 1)."""
    rec, roots, ph = prove_batches(dev, [r], sync_timing=True)
    if timings is not None:
        timings.update(ph)
    return rec[0], roots[0]


# ------------------------------------------------------------------------------------------
# Checks and measurements


def check_keccak(dev, rng, n=4096):
    """Device leaves/nodes against pycryptodome (and the host Python Keccak)."""
    be = dev.be
    vals = rng.integers(0, 2**63, size=(2 * n, 4), dtype=np.uint64) * 2 + rng.integers(0, 2, size=(2 * n, 4), dtype=np.uint64)
    dv = be.asarray(vals)
    leaves = dev.empty(2 * n)
    be.call("merkle_leaves", 2 * n, dv, dev.leaf_mid, leaves)
    nodes = dev.empty(n)
    be.call("merkle_nodes", n, leaves, dev.node_mid, nodes, n)
    hl, hn = be.host(leaves), be.host(nodes)
    ref = _pyc_cshake is not None
    bad = 0
    sample = range(0, 2 * n, max(1, (2 * n) // 512))
    for i in sample:
        data = b"\x00" + bytes(32) + b"\x01" + row_bytes(vals[i])
        want = xof32(LEAF_CUSTOM, data) if ref else PyCShake(LEAF_CUSTOM).absorb(data).finish32()
        bad += row_bytes(hl[i]) != want
    for i in range(0, n, max(1, n // 512)):
        data = b"\x01" + bytes(32) + b"\x01" + row_bytes(hl[i]) + bytes(32) + b"\x01" + row_bytes(hl[i + n])
        want = xof32(NODE_CUSTOM, data) if ref else PyCShake(NODE_CUSTOM).absorb(data).finish32()
        bad += row_bytes(hn[i]) != want
    return {"keccak_checked": len(sample) + len(range(0, n, max(1, n // 512))), "keccak_mismatch": int(bad),
            "keccak_reference": "pycryptodome cSHAKE256" if ref else "host Python Keccak (pycryptodome absent)"}


def check_mul(dev, path):
    """Device products and inverses against binary_tower_256.rs (mul_check.bin)."""
    raw = open(path, "rb").read()
    n = int.from_bytes(raw[:8], "little")
    ni = int.from_bytes(raw[8:16], "little")
    body = np.frombuffer(raw[16:16 + 96 * n], dtype="<u8").reshape(n, 3, 4).astype(np.uint64)
    inv = np.frombuffer(raw[16 + 96 * n:16 + 96 * n + 64 * ni], dtype="<u8").reshape(ni, 2, 4).astype(np.uint64)
    be = dev.be
    got = be.host(dev.mul(be.asarray(body[:, 0]), be.asarray(body[:, 1])))
    goti = be.host(dev.inv(be.asarray(inv[:, 0])))
    return {"mul_checked": n, "mul_mismatch": int((got != body[:, 2]).any(axis=1).sum()),
            "inv_checked": ni, "inv_mismatch": int((goti != inv[:, 1]).any(axis=1).sum())}


def check_bitslice(dev, path, rng, big=1 << 20, reps=5):
    """The bit-sliced multiply: bit-exact against binary_tower_256.rs (mul_check.bin) through
    both the resident path (to_sliced, t256_mul_bs, from_sliced) and the fused one
    (t256_mul_bsx); then against the table kernel on `big` random products; then rates."""
    be = dev.be
    raw = open(path, "rb").read()
    n = int.from_bytes(raw[:8], "little")
    body = np.frombuffer(raw[16:16 + 96 * n], dtype="<u8").reshape(n, 3, 4).astype(np.uint64)
    assert n % 32 == 0
    g = n // 32
    a, b = be.asarray(body[:, 0]), be.asarray(body[:, 1])
    sa, sb, sr = dev.empty(n * 2), dev.empty(n * 2), dev.empty(n * 2)  # 256 u32 planes per group
    be.call("t256_to_sliced", g, a, sa)
    be.call("t256_to_sliced", g, b, sb)
    be.call("t256_mul_bs", g, sa, sb, sr)
    r1 = dev.empty(n)
    be.call("t256_from_sliced", g, sr, r1)
    r2 = dev.empty(n)
    be.call("t256_mul_bsx", g, a, b, r2, 1)
    want = body[:, 2]
    out = {"bs_checked": n,
           "bs_resident_mismatch": int((be.host(r1) != want).any(axis=1).sum()),
           "bs_fused_mismatch": int((be.host(r2) != want).any(axis=1).sum())}
    # A large batch against the table kernel (itself checked against the Rust reference).
    A = be.asarray(rng.integers(0, 2**63, size=(big, 4), dtype=np.uint64) * 2 + 1)
    B = be.asarray(rng.integers(0, 2**63, size=(big, 4), dtype=np.uint64) * 2 + 1)
    G = big // 32
    ref = dev.empty(big)
    be.call("t256_mul", big, A, B, ref, 1)
    SA, SB, SR = dev.empty(big * 2), dev.empty(big * 2), dev.empty(big * 2)
    be.call("t256_to_sliced", G, A, SA)
    be.call("t256_to_sliced", G, B, SB)
    fused, res_el = dev.empty(big), dev.empty(big)

    def timed(fn):
        fn()
        be.sync()
        best = None
        for _ in range(reps):
            t0 = time.perf_counter()
            fn()
            be.sync()
            dt = time.perf_counter() - t0
            best = dt if best is None else min(best, dt)
        return best

    t_res = timed(lambda: be.call("t256_mul_bs", G, SA, SB, SR))
    t_fused = timed(lambda: be.call("t256_mul_bsx", G, A, B, fused, 1))
    t_tab = timed(lambda: be.call("t256_mul", big, A, B, ref, 1))
    t_in = timed(lambda: be.call("t256_to_sliced", G, A, SA))
    t_out = timed(lambda: be.call("t256_from_sliced", G, SR, res_el))
    out["bs_big_checked"] = big
    out["bs_big_resident_mismatch"] = int((be.host(res_el) != be.host(ref)).any(axis=1).sum())
    out["bs_big_fused_mismatch"] = int((be.host(fused) != be.host(ref)).any(axis=1).sum())
    out["rates"] = {"bs_resident_per_s": big / t_res, "bs_fused_per_s": big / t_fused,
                    "table_per_s": big / t_tab, "to_sliced_elems_per_s": big / t_in,
                    "from_sliced_elems_per_s": big / t_out,
                    "seconds": {"bs_resident": t_res, "bs_fused": t_fused, "table": t_tab,
                                "to_sliced": t_in, "from_sliced": t_out}}
    return out


def check_lean(dev, path):
    vecs = json.load(open(path))["vectors"]
    res = []
    for v in vecs:
        req = decode_request(bytes.fromhex(v["request"]))
        got, _ = prove_gpu(dev, req)
        res.append({"name": v["name"], "identical": got == bytes.fromhex(v["response"]), "bytes": len(got)})
    return res


def rate(be, dev, kind, threads, iters, reps=3):
    """Warm, synchronized throughput of the two primitives."""
    xp = be.xp
    if kind.startswith("keccak"):
        out = xp.zeros((threads,), dtype=np.uint64)
        args = (dev.leaf_mid, out, iters)
        name = kind.replace("keccak", "keccak_rate")
    else:
        out = xp.zeros((threads, 4), dtype=np.uint64)
        seed = be.asarray(np.arange(8, dtype=np.uint64).reshape(2, 4) * np.uint64(0x9E3779B97F4A7C15))
        args = (seed, out, iters)
        name = "t256_mul_rate" + ("_full" if kind == "mul_full" else "")
    be.call(name, threads, *args)
    be.sync()
    best = None
    for _ in range(reps):
        t0 = time.perf_counter()
        be.call(name, threads, *args)
        be.sync()
        dt = time.perf_counter() - t0
        best = dt if best is None else min(best, dt)
    return threads * iters / best, best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True, help="dir with tower256_fri_vectors.json, mul_check.bin, expect_ell*.json")
    ap.add_argument("--ells", default="10,12,14")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--backend", default="cupy", choices=["cupy", "emu"])
    ap.add_argument("--cubin")
    ap.add_argument("--lib")
    ap.add_argument("--rust-bench", help="tower256_fri_fast_bench binary: CPU timings on this box")
    ap.add_argument("--rust-threads", default="1,4")
    ap.add_argument("--rate-threads", type=int, default=40 * 1024)
    ap.add_argument("--mul", default="logexp", choices=["logexp", "full", "bs"], help="bulk multiply kernels")
    ap.add_argument("--bitslice-bench", action="store_true", help="check and time the bit-sliced multiply")
    ap.add_argument("--bitslice-big", type=int, default=1 << 20)
    ap.add_argument("--e2e", default="", help="ell:batch,... the whole prover on batches (expect_e2e_ell*.json)")
    ap.add_argument("--streams", default="1,2")
    ap.add_argument("--skip-rates", action="store_true")
    ap.add_argument("--batch", type=int, default=0, help="words in the batched encode+commit measurement")
    ap.add_argument("--batch-ell", type=int, default=14)
    ap.add_argument("--source", help="compile tower256_fri.cu with NVRTC instead of loading --cubin")
    ap.add_argument("--out", default=os.environ.get("ACCEL_RESULTS", "results.json"))
    a = ap.parse_args()
    res = {"host": platform.platform(), "python": sys.version.split()[0], "backend": a.backend,
           "transcript_hash": "pycryptodome" if _pyc_cshake is not None else "host-python"}

    def save():
        with open(a.out, "w") as f:
            json.dump(res, f, indent=1)

    if a.backend == "cupy":
        import cupy as cp

        props = cp.cuda.runtime.getDeviceProperties(0)
        res["device"] = props["name"].decode() if isinstance(props["name"], bytes) else props["name"]
        res["device_count"] = cp.cuda.runtime.getDeviceCount()
        res["sm"] = "%d.%d" % (props["major"], props["minor"])
        res["sm_count"] = props["multiProcessorCount"]
        res["clock_khz"] = props["clockRate"]
        assert res["device_count"] >= 1
        be = CupyBackend(a.cubin, a.source)
    else:
        be = EmuBackend(a.lib)
    dev = Dev(be, a.mul)
    res["mul_variant"] = a.mul
    print("backend", be.name, res.get("device"), flush=True)
    rng = np.random.default_rng(9104)
    res["checks"] = {}
    res["checks"].update(check_keccak(dev, rng))
    res["checks"].update(check_mul(dev, os.path.join(a.data, "mul_check.bin")))
    print("checks", res["checks"], flush=True)
    if a.bitslice_bench:
        bs = check_bitslice(dev, os.path.join(a.data, "mul_check.bin"), rng,
                            big=a.bitslice_big, reps=a.reps + 2)
        res["bitslice"] = bs
        if "clock_khz" in res:
            lanes = res["sm_count"] * 64 * res["clock_khz"] * 1e3
            r = bs["rates"]
            best = max(r["bs_resident_per_s"], r["bs_fused_per_s"])
            res["tower256_mul_per_s"] = best
            res["tower256_mul_variant"] = "bit-sliced resident" if best == r["bs_resident_per_s"] else "bit-sliced fused"
            res["ops_per_mul"] = lanes / best
            res["ops_per_mul_fused"] = lanes / r["bs_fused_per_s"]
            res["ops_per_mul_table"] = lanes / r["table_per_s"]
            res["ops_per_mul_f3_assumption"] = 718
        print("bitslice", bs, flush=True)
        save()
    res["lean_vectors"] = check_lean(dev, os.path.join(a.data, "tower256_fri_vectors.json"))
    print("lean", res["lean_vectors"], flush=True)
    save()
    if a.backend == "cupy" and not a.skip_rates:
        it_k, it_m = 64, 16
        clock = res["clock_khz"] * 1e3
        # int32 lanes per second at the reported clock (64 per SM per cycle on sm_70..sm_90).
        lanes = res["sm_count"] * 64 * clock
        res["rates"] = {}
        for kind, it in (("keccak", it_k), ("keccak_shf", it_k), ("keccak_u2", it_k),
                         ("mul", it_m), ("mul_full", it_m)):
            try:
                r_, t_ = rate(be, dev, kind, a.rate_threads, it)
            except Exception as e:  # noqa: BLE001  (a variant that cannot launch is a result too)
                res["rates"][kind] = {"error": repr(e)[:300]}
                print("rate", kind, "failed", repr(e)[:200], flush=True)
                continue
            res["rates"][kind] = {"per_s": r_, "seconds": t_, "threads": a.rate_threads, "iters": it,
                                  "implied_int32_ops": lanes / r_}
            print("rate", kind, r_, flush=True)
        best_k = max((k for k in ("keccak", "keccak_shf", "keccak_u2") if "per_s" in res["rates"][k]),
                     key=lambda k: res["rates"][k]["per_s"])
        res["keccak_f_per_s"] = res["rates"][best_k]["per_s"]
        res["keccak_f_per_s_source"] = "rate probe " + best_k
        res["implied_int32_ops_per_keccak_f"] = res["rates"][best_k]["implied_int32_ops"]
        res["t256_mul_per_s"] = res["rates"]["mul_full" if a.mul == "full" else "mul"].get("per_s")
        res["merkle_keccak_variant"] = "keccak_shf"
        save()
    res["prove"] = []
    for ell in [int(x) for x in a.ells.split(",") if x]:
        exp = json.load(open(os.path.join(a.data, "expect_ell%d.json" % ell)))
        t0 = time.perf_counter()
        req = production_request(ell)
        reqb = encode_request(req)
        gen_s = time.perf_counter() - t0
        same_req = hashlib.sha3_256(reqb).hexdigest() == exp["request_sha3_256"]
        best, best_tm, ok = None, None, True
        for rep in range(a.reps):
            dev.counts = {"mul": 0, "keccak": 0}
            tm = {}
            t0 = time.perf_counter()
            got, roots = prove_gpu(dev, req, tm)
            be.sync()
            dt = time.perf_counter() - t0
            ok = ok and hashlib.sha3_256(got).hexdigest() == exp["receipt_sha3_256"] and \
                [r.hex() for r in roots] == exp["roots"]
            if best is None or dt < best:
                best, best_tm = dt, tm
        row = {"ell": ell, "request_identical": same_req, "receipt_identical": ok, "receipt_len": len(got),
               "best_s": best, "phases_s": best_tm, "request_gen_s": gen_s, "device_mults": dev.counts["mul"],
               "device_keccak_f": dev.counts["keccak"]}
        res["prove"].append(row)
        print("prove", row, flush=True)
        save()
    if a.e2e:
        # The whole prover on batches of leaves: every receipt against the CPU prover's.
        res["e2e"] = []
        for item in a.e2e.split(","):
            ell, B = (int(x) for x in item.split(":"))
            exp = json.load(open(os.path.join(a.data, "expect_e2e_ell%d.json" % ell)))
            assert exp["batch"] == B
            t0 = time.perf_counter()
            reqs = [batch_request(ell, b) for b in range(B)]
            gen_s = time.perf_counter() - t0
            req_ok = [hashlib.sha3_256(encode_request(r)).hexdigest() for r in reqs] == exp["request_sha3_256"]
            row = {"ell": ell, "batch": B, "request_identical": req_ok, "request_gen_s": gen_s, "runs": []}

            def run(label, rq, streams, sync_timing, reps):
                best, ok, ph = None, True, None
                for _ in range(reps):
                    dev.counts = {"mul": 0, "keccak": 0}
                    be.sync()
                    t0 = time.perf_counter()
                    sub = max(1, len(rq) // streams) if streams > 1 else None
                    rec, _, phases = prove_batches(dev, rq, streams=streams, sync_timing=sync_timing, sub=sub)
                    dt = time.perf_counter() - t0
                    ok = ok and [hashlib.sha3_256(x).hexdigest() for x in rec] == exp["receipt_sha3_256"][:len(rq)]
                    if best is None or dt < best:
                        best, ph = dt, phases
                r = {"label": label, "proofs": len(rq), "streams": streams, "wall_s": best,
                     "per_proof_ms": 1e3 * best / len(rq), "receipts_identical": ok,
                     "device_mults": dev.counts["mul"], "device_keccak_f": dev.counts["keccak"]}
                if sync_timing:
                    r["phases_ms_per_proof"] = {k: 1e3 * v / len(rq) for k, v in ph.items()}
                row["runs"].append(r)
                print("e2e", ell, r, flush=True)
                save()

            run("phases (synchronized per stage)", reqs, 1, True, 1)
            run("single proof, latency", reqs[:1], 1, False, a.reps)
            for st in [int(x) for x in a.streams.split(",")]:
                run("batch, %d stream(s)" % st, reqs, st, False, a.reps)
            row["receipts_identical"] = all(r["receipts_identical"] for r in row["runs"]) and req_ok
            row["best_per_proof_ms"] = min(r["per_proof_ms"] for r in row["runs"] if r["proofs"] == B)
            res["e2e"].append(row)
            save()
    if a.batch:
        # Many words on one domain (columns, or many leaves of one shape): encode + commit,
        # which is all but a few percent of a proof. Checked against the one-word path.
        ell, B = a.batch_ell, a.batch
        req = production_request(ell)
        beta = be.asarray(elems_to_array(req["beta"]))
        offset = be.asarray(elems_to_array([req["offset"]]))
        l = 1 << (ell - 2)
        coeffs = rng.integers(0, 2**63, size=(B * l, 4), dtype=np.uint64) * 2 + 1
        dc = be.asarray(coeffs)
        best = None
        for rep in range(a.reps + 1):
            be.sync()
            t0 = time.perf_counter()
            words = dev.eval_subspace(dc, offset, beta, B)
            be.sync()
            t1 = time.perf_counter()
            tr = dev.tree(words, False, B)
            be.sync()
            t2 = time.perf_counter()
            if rep and (best is None or t2 - t0 < best[0]):
                best = (t2 - t0, t1 - t0, t2 - t1)
        roots = be.host(tr[0])
        same = True
        for b in sorted({0, B // 2, B - 1}):
            w1 = dev.eval_subspace(dc[b * l:(b + 1) * l], offset, beta)
            r1 = be.host(dev.tree(w1, False)[0])[0]
            same = same and bool((r1 == roots[b]).all())
        res["batch"] = {"ell": ell, "words": B, "best_s": best[0], "encode_s": best[1], "merkle_s": best[2],
                        "per_word_ms": 1e3 * best[0] / B, "keccak_f_per_s": B * (2 * (1 << ell) - 1) / best[2],
                        "roots_match_single": same}
        print("batch", res["batch"], flush=True)
        # The tree build is the better Keccak-f measurement: independent threads, one
        # permutation each, warm and synchronized, every output checked through the roots.
        if res["batch"]["keccak_f_per_s"] > res.get("keccak_f_per_s", 0):
            res["keccak_f_per_s"] = res["batch"]["keccak_f_per_s"]
            res["keccak_f_per_s_source"] = "batched Merkle trees (merkle_leaves + merkle_nodes, funnel-shift rotations)"
            if "clock_khz" in res:
                res["implied_int32_ops_per_keccak_f"] = res["sm_count"] * 64 * res["clock_khz"] * 1e3 / res["keccak_f_per_s"]
        save()
    if a.rust_bench:
        cmd = [a.rust_bench, "--ell", a.ells, "--threads", a.rust_threads, "--reps", str(a.reps)]
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=3000)
        res["rust_cpu"] = [json.loads(x) for x in p.stdout.splitlines() if x.startswith("{")]
        res["rust_cpu_rc"] = p.returncode
        res["cpu_model"] = subprocess.run("grep -m1 'model name' /proc/cpuinfo; nproc", shell=True,
                                          capture_output=True, text=True).stdout.strip()
        print("rust", res["rust_cpu"], flush=True)
        save()
    bsr = res.get("bitslice", {})
    allok = (all(bsr.get(k, 0) == 0 for k in ("bs_resident_mismatch", "bs_fused_mismatch", "bs_big_resident_mismatch",
                                               "bs_big_fused_mismatch"))
             and res["checks"]["keccak_mismatch"] == 0 and res["checks"]["mul_mismatch"] == 0
             and res["checks"]["inv_mismatch"] == 0 and all(v["identical"] for v in res["lean_vectors"])
             and all(r["receipt_identical"] and r["request_identical"] for r in res["prove"])
             and res.get("batch", {}).get("roots_match_single", True)
             and all(r["receipts_identical"] for r in res.get("e2e", [])))
    res["all_bit_exact"] = allok
    save()
    print("ALL_BIT_EXACT", allok, flush=True)
    sys.exit(0 if allok else 1)


if __name__ == "__main__":
    main()
