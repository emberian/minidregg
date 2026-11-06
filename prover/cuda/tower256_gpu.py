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
    word = c8_list()
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
    encode_nat(out, len(r["word"]))
    for x in r["word"]:
        out += x
    return bytes(out)


def splitmix(s):
    s = (s + 0x9E3779B97F4A7C15) & MASK64
    z = s
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    return s, z ^ (z >> 31)


def production_request(ell):
    """tower256_fri_fast_bench.rs production_request, from the same SplitMix stream."""
    s = 0x70430000 + ell
    out = []

    def nxt():
        nonlocal s
        s, z = splitmix(s)
        return z

    def elem():
        return b"".join(nxt().to_bytes(8, "little") for _ in range(4))

    lb = 2
    m = ell - lb - 2
    st = bytes(nxt() & 0xFF for _ in range(48))
    beta = [elem() for _ in range(ell)]
    offset = elem()
    degree = [1 << (ell - lb - j) for j in range(m + 1)]
    n = 1 << (ell - lb)
    # The word is the bulk: draw it with numpy-free Python but in one pass.
    word = [elem() for _ in range(n)]
    del out
    return dict(statement=st, ell=ell, m=m, q=148, beta=beta, offset=offset, degree=degree, word=word)


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
        self.k = {n: n + ("_full" if mul == "full" else "") for n in ("t256_mul", "ntt_scale", "ntt_butterfly", "fri_fold")}
        self.xp = be.xp
        self.one = be.asarray(np.array([[1, 0, 0, 0]], dtype=np.uint64))
        self.leaf_mid = be.asarray(np.array(PyCShake(LEAF_CUSTOM).midstate(), dtype=np.uint64))
        self.node_mid = be.asarray(np.array(PyCShake(NODE_CUSTOM).midstate(), dtype=np.uint64))
        self.counts = {"mul": 0, "keccak": 0}

    def empty(self, n):
        return self.xp.zeros((n, 4), dtype=np.uint64)

    def c(self, x):
        return self.xp.ascontiguousarray(x)

    def mul(self, a, b):
        """a * b elementwise; b may be one row (a scalar)."""
        a, b = self.c(a), self.c(b)
        out = self.empty(a.shape[0])
        self.be.call(self.k["t256_mul"], a.shape[0], a, b, out, 0 if b.shape[0] == 1 else 1)
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
        depths = []
        s, bs, block = self.c(offset), self.c(basis), l
        while block > 1 and bs.shape[0] > 0:
            b0 = bs[0:1]
            if self.is_zero_row(b0):
                assert batch == 1
                xs = self.span(offset, basis)
                out = self.empty(n)
                self.be.call("horner_points", n, self.c(coeffs[:used]), xs, out, used)
                self.counts["mul"] += n * used
                return out
            inv = self.inv(b0)
            powers = self.powers(b0, block)
            t = self.mul(s, inv)
            gamma = self.mul(bs[1:], inv) if bs.shape[0] > 1 else self.empty(0)
            z = self.span(t, gamma)
            s = self.pivot_map(t, self.one)
            bs = self.pivot_map(gamma, self.one) if gamma.shape[0] else self.empty(0)
            depths.append((powers, z))
            block //= 2
        L, N = l * batch, n * batch
        if batch == 1:
            a = self.empty(l)
            a[:used] = coeffs[:used]
        else:
            a = self.c(coeffs).copy()
        tmp = self.empty(L)
        for d, (powers, _) in enumerate(depths):
            bsz = l >> d
            self.be.call(self.k["ntt_scale"], L, a, powers, tmp, bsz)
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
            self.be.call(self.k["ntt_butterfly"], N // 2, cur, depths[d][1], nxt, size)
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
        self.be.call(self.k["fri_fold"], half, self.c(w), self.c(c), out)
        self.counts["mul"] += half
        return out


def prove_gpu(dev, r, timings=None):
    """The receipt bytes and roots for request dict r (tower256_fri_fast.rs prove_fast)."""
    be, xp = dev.be, dev.xp
    tm = timings if timings is not None else {}
    for key in ("encode", "merkle", "folds", "openings", "other", "upload"):
        tm.setdefault(key, 0.0)

    def tick():
        be.sync()
        return time.perf_counter()

    ell, m, q = r["ell"], r["m"], r["q"]
    if m > ell or ell > 24 or ell == 0:
        raise ProveError("Shape")
    if len(r["beta"]) != ell:
        raise ProveError("BasisLength")
    final_degree = r["degree"][m] if m < len(r["degree"]) else 0
    last_size = 1 << (ell - m)
    if final_degree > last_size:
        raise ProveError("FinalDegree")
    if final_degree > 16:
        raise ProveError("final degree above the device kernel's 16")
    t0 = tick()
    beta = be.asarray(elems_to_array(r["beta"]))
    offset = be.asarray(elems_to_array([r["offset"]]))
    coeffs = be.asarray(elems_to_array(r["word"]))
    t1 = tick()
    tm["upload"] += t1 - t0
    imgs, pinvs = [], []
    cur = xp.concatenate([offset, beta], axis=0)
    for j in range(m):
        p = cur[1 + (ell - 1 - j):2 + (ell - 1 - j)]
        if dev.is_zero_row(p):
            raise ProveError("ZeroPivot(%d)" % j)
        imgs.append(cur)
        pinvs.append(dev.inv(p))
        cur = dev.pivot_map(cur, p)
    imgs.append(cur)
    head = bytearray()
    envelope(head, r["statement"])
    bp = bytearray()
    tmp = bytearray()
    encode_length(tmp, ell)
    envelope(bp, tmp)
    tmp = bytearray()
    encode_length(tmp, m)
    envelope(bp, tmp)
    envelope(bp, r["offset"])
    for i, b in enumerate(r["beta"]):
        inner, tmp = bytearray(), bytearray()
        encode_length(tmp, i)
        envelope(inner, tmp)
        envelope(inner, b)
        envelope(bp, inner)
    envelope(head, bp)
    t2 = tick()
    tm["other"] += t2 - t1
    w0 = dev.eval_subspace(coeffs, offset, beta)
    t3 = tick()
    tm["encode"] += t3 - t2

    def push_root(out, n, root):
        tmp = bytearray()
        encode_length(tmp, n)
        envelope(out, tmp)
        envelope(out, root)

    words, trees, roots, challenges = [w0], [], [], []
    t0 = tick()
    tr = dev.tree(w0, m > 0)
    trees.append(tr)
    roots.append(row_bytes(be.host(tr[0])[0]))
    tm["merkle"] += tick() - t0
    for j in range(m):
        t0 = tick()
        inp = bytearray(head)
        for n_, rt in enumerate(roots[:j + 1]):
            push_root(inp, n_, rt)
        alpha_b = xof32(CHALLENGE_CUSTOM, bytes(inp))
        alpha = be.asarray(elems_to_array([alpha_b]))
        t1 = tick()
        tm["other"] += t1 - t0
        k = ell - j
        im = imgs[j]
        scaled = dev.mul(im[1:k], pinvs[j]) if k > 1 else dev.empty(0)
        c = dev.span(dev.mul(im[0:1] ^ alpha, pinvs[j]), scaled)
        nxt = dev.fold(words[j], c)
        t2 = tick()
        tm["folds"] += t2 - t1
        challenges.append(alpha_b)
        if j + 1 < m:
            tr = dev.tree(nxt, True)
            trees.append(tr)
            roots.append(row_bytes(be.host(tr[0])[0]))
            tm["merkle"] += tick() - t2
        words.append(nxt)
    t0 = tick()
    im = imgs[m]
    dom_m = dev.span(im[0:1], im[1:1 + (ell - m)])
    fd = final_degree
    fco = dev.empty(max(fd, 1))
    vals = dev.empty(last_size)
    status = xp.zeros((1,), dtype=np.uint64)
    xs = dev.c(dom_m[:max(fd, 1)])
    ys = dev.c(words[m][:max(fd, 1)])
    be.call("fri_final", 1, xs, ys, dom_m, fco, vals, status, fd, last_size)
    if int(be.host(status)[0]) != 0:
        raise ProveError("SingularInterpolation")
    fcoeffs = [row_bytes(x) for x in be.host(fco)[:fd]]
    tm["other"] += tick() - t0
    if m > 0:
        t0 = tick()
        tr = dev.tree(vals, False)
        roots.append(row_bytes(be.host(tr[0])[0]))
        tm["merkle"] += tick() - t0
    t0 = tick()
    prefix = bytearray(head)
    for n_, rt in enumerate(roots[:m + 1]):
        push_root(prefix, n_, rt)
    for cb in challenges:
        envelope(prefix, cb)
    seed_bits = ell - 1
    seeds = []
    if _pyc_cshake is not None:
        for a in range(q):
            tmp, env = bytearray(), bytearray()
            encode_length(tmp, a)
            envelope(env, tmp)
            d = xof32(QUERY_CUSTOM, bytes(prefix) + bytes(env))
            seeds.append(int.from_bytes(d[:8], "little") & ((1 << seed_bits) - 1))
    else:
        base = PyCShake(QUERY_CUSTOM).absorb(bytes(prefix))
        for a in range(q):
            tmp, env = bytearray(), bytearray()
            encode_length(tmp, a)
            envelope(env, tmp)
            d = base.clone().absorb(bytes(env)).finish32()
            seeds.append(int.from_bytes(d[:8], "little") & ((1 << seed_bits) - 1))
    out = bytearray()
    encode_nat(out, m + 1)
    for rt in roots[:m + 1]:
        encode_nat_le32(out, rt)
    encode_nat(out, m)
    for cb in challenges:
        out += cb
    encode_nat(out, q)
    for s_ in seeds:
        encode_nat(out, s_)
    t1 = tick()
    tm["other"] += t1 - t0
    encode_nat(out, m)
    for j in range(m):
        encode_nat(out, q)
        k = ell - j
        half = 1 << (k - 1)
        idx = np.array([s_ % half for s_ in seeds], dtype=np.int64)
        w = words[j]
        lo = be.host(w[be.asarray(idx).astype(np.int64)]) if q else np.zeros((0, 4), np.uint64)
        hi = be.host(w[be.asarray(idx + half).astype(np.int64)]) if q else np.zeros((0, 4), np.uint64)
        # All of this round's siblings, gathered on the device, then encoded in one call.
        rows = [trees[j][d + 1][be.asarray((idx & ((2 << d) - 1)) ^ (1 << d)).astype(np.int64)]
                for d in range(k - 1)] if q else []
        enc = encode_nat_le32_rows(be.host(xp.concatenate(rows, axis=0))) if rows else []
        sib = [enc[d * q:(d + 1) * q] for d in range(k - 1)]
        lob, hib = np.ascontiguousarray(lo, dtype="<u8"), np.ascontiguousarray(hi, dtype="<u8")
        klen = bytearray()
        encode_nat(klen, k - 1)
        for a in range(q):
            out += lob[a].tobytes()
            out += hib[a].tobytes()
            out += klen
            for d in range(k - 1):
                out += sib[d][a]
    t2 = tick()
    tm["openings"] += t2 - t1
    encode_nat(out, len(fcoeffs))
    for cb in fcoeffs:
        out += cb
    tm["other"] += tick() - t2
    return bytes(out), roots


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
    ap.add_argument("--mul", default="logexp", choices=["logexp", "full"], help="bulk multiply kernels")
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
    res["lean_vectors"] = check_lean(dev, os.path.join(a.data, "tower256_fri_vectors.json"))
    print("lean", res["lean_vectors"], flush=True)
    save()
    if a.backend == "cupy":
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
    allok = (res["checks"]["keccak_mismatch"] == 0 and res["checks"]["mul_mismatch"] == 0
             and res["checks"]["inv_mismatch"] == 0 and all(v["identical"] for v in res["lean_vectors"])
             and all(r["receipt_identical"] and r["request_identical"] for r in res["prove"])
             and res.get("batch", {}).get("roots_match_single", True))
    res["all_bit_exact"] = allok
    save()
    print("ALL_BIT_EXACT", allok, flush=True)
    sys.exit(0 if allok else 1)


if __name__ == "__main__":
    main()
