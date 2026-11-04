// The one Solana transaction shape the door's pay page sends, and nothing else: base58, SHA-256, the
// ed25519 on-curve test (for program-derived addresses), the legacy message and wire format, a decoder for
// the wallet's answer, and four JSON-RPC calls. It replaces a 484 KB general SDK so the attested surface on
// a payment page is what the page uses: no signing, no keys, no subscriptions, no other instruction codecs.
//
//   const sol = solpay                       (browser global; module.exports under node)
//   sol.PublicKey                            new PublicKey(base58 | 32 bytes); toBytes toBase58 toString equals
//   sol.ata(owner, tokenProgram, mint)       the associated token account address (a PDA of the ATA program)
//   sol.transferChecked / sol.memo           instruction records {programId, keys:[{pubkey,isSigner,isWritable}], data}
//   sol.compileMessage({feePayer, recentBlockhash, instructions}) -> message bytes, account order exactly as
//                                            @solana/web3.js 1.99 compiles a legacy Transaction
//   sol.unsignedWire(message)                -> bytes for a wallet to sign (zeroed signature slots + message)
//   sol.decodeWire(bytes)                    -> {signatures, message, feePayer, recentBlockhash, instructions}
//   new sol.Connection(rpcUrl, commitment, fetchImpl)  getAccountInfo, getTokenAccountBalance,
//                                            getLatestBlockhash, sendRawTransaction
(function (root, factory) {
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  else root.solpay = api;
})(typeof self !== "undefined" ? self : this, function () {
  // ---- base58 (Bitcoin alphabet) ----
  const ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
  const INDEX = new Map([...ALPHABET].map((c, i) => [c, i]));
  function b58encode(bytes) {
    let zeros = 0;
    while (zeros < bytes.length && bytes[zeros] === 0) zeros++;
    const digits = [];
    for (let i = zeros; i < bytes.length; i++) {
      let carry = bytes[i];
      for (let j = 0; j < digits.length; j++) { carry += digits[j] << 8; digits[j] = carry % 58; carry = (carry / 58) | 0; }
      while (carry > 0) { digits.push(carry % 58); carry = (carry / 58) | 0; }
    }
    let s = "1".repeat(zeros);
    for (let i = digits.length - 1; i >= 0; i--) s += ALPHABET[digits[i]];
    return s;
  }
  function b58decode(s) {
    let zeros = 0;
    while (zeros < s.length && s[zeros] === "1") zeros++;
    const bytes = [];
    for (let i = zeros; i < s.length; i++) {
      const v = INDEX.get(s[i]);
      if (v === undefined) throw new Error("not base58: " + JSON.stringify(s[i]));
      let carry = v;
      for (let j = 0; j < bytes.length; j++) { carry += bytes[j] * 58; bytes[j] = carry & 0xff; carry >>= 8; }
      while (carry > 0) { bytes.push(carry & 0xff); carry >>= 8; }
    }
    const out = new Uint8Array(zeros + bytes.length);
    for (let i = 0; i < bytes.length; i++) out[zeros + i] = bytes[bytes.length - 1 - i];
    return out;
  }

  // ---- SHA-256 ----
  const K = new Uint32Array([
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]);
  function sha256(data) {
    const h = new Uint32Array([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]);
    const padded = new Uint8Array(((data.length + 9 + 63) >> 6) << 6);
    padded.set(data); padded[data.length] = 0x80;
    const dv = new DataView(padded.buffer);
    dv.setUint32(padded.length - 8, Math.floor(data.length / 0x20000000), false);
    dv.setUint32(padded.length - 4, (data.length << 3) >>> 0, false);
    const w = new Uint32Array(64);
    const rotr = (x, n) => (x >>> n) | (x << (32 - n));
    for (let off = 0; off < padded.length; off += 64) {
      for (let i = 0; i < 16; i++) w[i] = dv.getUint32(off + 4 * i, false);
      for (let i = 16; i < 64; i++) {
        const s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >>> 3);
        const s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >>> 10);
        w[i] = (w[i - 16] + s0 + w[i - 7] + s1) | 0;
      }
      let [a, b, c, d, e, f, g, hh] = h;
      for (let i = 0; i < 64; i++) {
        const t1 = (hh + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & g)) + K[i] + w[i]) | 0;
        const t2 = ((rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c))) | 0;
        hh = g; g = f; f = e; e = (d + t1) | 0; d = c; c = b; b = a; a = (t1 + t2) | 0;
      }
      h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
    }
    const out = new Uint8Array(32), odv = new DataView(out.buffer);
    for (let i = 0; i < 8; i++) odv.setUint32(4 * i, h[i], false);
    return out;
  }

  // ---- ed25519 on-curve test: the point decompression of RFC 8032 5.1.3, strict (y < p; no x = 0 with the sign bit) ----
  const P = (1n << 255n) - 19n;
  const D = 37095705934669439343138083508754565189542113879843219016388785533085940283555n; // -121665/121666 mod p
  const mod = (a) => { const r = a % P; return r < 0n ? r + P : r; };
  function modpow(b, e) { let r = 1n; b = mod(b); while (e > 0n) { if (e & 1n) r = (r * b) % P; b = (b * b) % P; e >>= 1n; } return r; }
  function isOnCurve(bytes) {
    if (bytes.length !== 32) return false;
    let y = 0n;
    for (let i = 31; i >= 0; i--) y = (y << 8n) | BigInt(i === 31 ? bytes[i] & 0x7f : bytes[i]);
    if (y >= P) return false;
    const y2 = (y * y) % P;
    const u = mod(y2 - 1n), v = mod(D * y2 + 1n);
    if (v === 0n) return u === 0n && !(bytes[31] & 0x80);
    if (u === 0n) return !(bytes[31] & 0x80); // x = 0: valid only with the sign bit clear
    const r = (u * modpow(v, P - 2n)) % P;   // x^2 = u/v must be a square
    return modpow(r, (P - 1n) / 2n) === 1n;
  }

  // ---- addresses ----
  const concat = (...parts) => { const out = new Uint8Array(parts.reduce((n, p) => n + p.length, 0)); let o = 0; for (const p of parts) { out.set(p, o); o += p.length; } return out; };
  class PublicKey {
    constructor(v) {
      const bytes = typeof v === "string" ? b58decode(v) : v && typeof v.toBytes === "function" ? v.toBytes() : Uint8Array.from(v);
      if (bytes.length !== 32) throw new Error("a public key is 32 bytes, got " + bytes.length);
      this._b = Uint8Array.from(bytes);
    }
    toBytes() { return Uint8Array.from(this._b); }
    toBase58() { return b58encode(this._b); }
    toString() { return this.toBase58(); }
    equals(o) { const b = o.toBytes(); return b.length === 32 && b.every((x, i) => x === this._b[i]); }
  }
  const SYSTEM_PROGRAM = new PublicKey(new Uint8Array(32));
  const ATA_PROGRAM = new PublicKey("ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL");
  const MEMO_PROGRAM = new PublicKey("MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr");
  const PDA_TAG = new TextEncoder().encode("ProgramDerivedAddress");
  function findProgramAddress(seeds, programId) {
    for (let bump = 255; bump >= 0; bump--) {
      for (const s of seeds) if (s.length > 32) throw new Error("a seed is at most 32 bytes");
      const h = sha256(concat(...seeds, Uint8Array.of(bump), programId.toBytes(), PDA_TAG));
      if (!isOnCurve(h)) return [new PublicKey(h), bump];
    }
    throw new Error("no viable program address bump");
  }
  const ata = (owner, tokenProgram, mint) => findProgramAddress([owner.toBytes(), tokenProgram.toBytes(), mint.toBytes()], ATA_PROGRAM)[0];

  // ---- the instructions ----
  function createAtaIdempotent({ payer, ata, owner, mint, tokenProgram }) {
    return { programId: ATA_PROGRAM, data: Uint8Array.of(1), keys: [
      { pubkey: payer, isSigner: true, isWritable: true },
      { pubkey: ata, isSigner: false, isWritable: true },
      { pubkey: owner, isSigner: false, isWritable: false },
      { pubkey: mint, isSigner: false, isWritable: false },
      { pubkey: SYSTEM_PROGRAM, isSigner: false, isWritable: false },
      { pubkey: tokenProgram, isSigner: false, isWritable: false } ] };
  }
  function transferChecked({ tokenProgram, source, mint, destination, owner, amount, decimals }) {
    const data = new Uint8Array(10);
    data[0] = 12; // TransferChecked
    let v = BigInt(amount);
    if (v < 0n || v >= 1n << 64n) throw new Error("the amount is not a u64");
    for (let i = 0; i < 8; i++) { data[1 + i] = Number(v & 0xffn); v >>= 8n; }
    if (!(decimals >= 0 && decimals <= 255)) throw new Error("decimals is not a u8");
    data[9] = decimals;
    return { programId: tokenProgram, data, keys: [
      { pubkey: source, isSigner: false, isWritable: true },
      { pubkey: mint, isSigner: false, isWritable: false },
      { pubkey: destination, isSigner: false, isWritable: true },
      { pubkey: owner, isSigner: true, isWritable: false } ] };
  }
  const memo = (signer, bytes) => ({ programId: MEMO_PROGRAM, data: Uint8Array.from(bytes), keys: [{ pubkey: signer, isSigner: true, isWritable: false }] });

  // ---- legacy message and wire format ----
  function compactU16(n) { const out = []; for (;;) { const b = n & 0x7f; n >>= 7; if (n === 0) { out.push(b); return out; } out.push(b | 0x80); } }
  function readCompactU16(bytes, at) {
    let n = 0, shift = 0;
    for (let i = 0; i < 3; i++) {
      const b = bytes[at.i++];
      if (b === undefined) throw new Error("truncated");
      n |= (b & 0x7f) << shift;
      if (!(b & 0x80)) return n;
      shift += 7;
    }
    throw new Error("compact-u16 too long");
  }
  // The order of two base58 strings within an account group, as the ICU "en" collation web3.js asks for with
  // caseFirst:"lower": digits before letters, letters alphabetically ignoring case, then (only if that ties) the
  // lowercase letter first. Spelled out so the bytes do not depend on a browser's ICU.
  function b58compare(x, y) {
    const prim = (c) => (c <= "9" ? c.charCodeAt(0) - 48 : 10 + c.toLowerCase().charCodeAt(0) - 97);
    const n = Math.min(x.length, y.length);
    for (let i = 0; i < n; i++) { const d = prim(x[i]) - prim(y[i]); if (d) return d < 0 ? -1 : 1; }
    if (x.length !== y.length) return x.length < y.length ? -1 : 1;
    for (let i = 0; i < n; i++) if (x[i] !== y[i]) return x[i] === x[i].toLowerCase() ? -1 : 1;
    return 0;
  }
  function compileMessage({ feePayer, recentBlockhash, instructions }) {
    const metas = [];
    for (const ix of instructions) for (const k of ix.keys) metas.push({ pubkey: k.pubkey, isSigner: k.isSigner, isWritable: k.isWritable });
    for (const id of [...new Set(instructions.map((ix) => ix.programId.toBase58()))]) metas.push({ pubkey: new PublicKey(id), isSigner: false, isWritable: false });
    const unique = [];
    for (const m of metas) {
      const seen = unique.find((u) => u.pubkey.equals(m.pubkey));
      if (seen) { seen.isWritable = seen.isWritable || m.isWritable; seen.isSigner = seen.isSigner || m.isSigner; } else unique.push({ ...m });
    }
    unique.sort((a, b) => a.isSigner !== b.isSigner ? (a.isSigner ? -1 : 1) : a.isWritable !== b.isWritable ? (a.isWritable ? -1 : 1) : b58compare(a.pubkey.toBase58(), b.pubkey.toBase58()));
    const at = unique.findIndex((u) => u.pubkey.equals(feePayer));
    const payer = at > -1 ? unique.splice(at, 1)[0] : { pubkey: feePayer };
    payer.isSigner = true; payer.isWritable = true;
    unique.unshift(payer);
    const index = (pk) => unique.findIndex((u) => u.pubkey.equals(pk));
    const header = [0, 0, 0];
    for (const u of unique) {
      if (u.isSigner) { header[0]++; if (!u.isWritable) header[1]++; } else if (!u.isWritable) header[2]++;
    }
    const bh = b58decode(recentBlockhash);
    if (bh.length !== 32) throw new Error("a blockhash is 32 bytes");
    const parts = [Uint8Array.from(header), Uint8Array.from(compactU16(unique.length)), ...unique.map((u) => u.pubkey.toBytes()), bh, Uint8Array.from(compactU16(instructions.length))];
    for (const ix of instructions) {
      parts.push(Uint8Array.of(index(ix.programId)), Uint8Array.from(compactU16(ix.keys.length)), Uint8Array.from(ix.keys.map((k) => index(k.pubkey))),
        Uint8Array.from(compactU16(ix.data.length)), Uint8Array.from(ix.data));
    }
    return concat(...parts);
  }
  const wireWith = (signatures, message) => concat(Uint8Array.from(compactU16(signatures.length)), ...signatures, message);
  const unsignedWire = (message) => wireWith(Array.from({ length: message[0] }, () => new Uint8Array(64)), message);
  function decodeWire(bytes) {
    bytes = Uint8Array.from(bytes);
    const at = { i: 0 };
    const nsig = readCompactU16(bytes, at);
    const signatures = [];
    for (let s = 0; s < nsig; s++) { signatures.push(bytes.slice(at.i, at.i + 64)); at.i += 64; }
    const start = at.i;
    if (bytes[at.i] & 0x80) throw new Error("a versioned message; the door sends legacy only");
    const [nSigners, nRoSigned, nRoUnsigned] = [bytes[at.i++], bytes[at.i++], bytes[at.i++]];
    const nkeys = readCompactU16(bytes, at);
    const keys = [];
    for (let k = 0; k < nkeys; k++) { keys.push(new PublicKey(bytes.slice(at.i, at.i + 32))); at.i += 32; }
    const recentBlockhash = b58encode(bytes.slice(at.i, at.i + 32)); at.i += 32;
    const nix = readCompactU16(bytes, at);
    const instructions = [];
    const meta = (i) => { if (i >= nkeys) throw new Error("an account index past the table"); return { pubkey: keys[i], isSigner: i < nSigners, isWritable: i < nSigners ? i < nSigners - nRoSigned : i < nkeys - nRoUnsigned }; };
    for (let n = 0; n < nix; n++) {
      const programId = keys[bytes[at.i++]];
      const na = readCompactU16(bytes, at);
      const ixKeys = []; for (let a = 0; a < na; a++) ixKeys.push(meta(bytes[at.i++]));
      const nd = readCompactU16(bytes, at);
      instructions.push({ programId, keys: ixKeys, data: bytes.slice(at.i, at.i + nd) }); at.i += nd;
    }
    if (at.i !== bytes.length) throw new Error("trailing bytes after the message");
    if (nsig !== nSigners) throw new Error("the signature count is not the header's");
    return { signatures, message: bytes.slice(start), feePayer: keys[0], recentBlockhash, instructions };
  }

  // ---- the cluster: four JSON-RPC calls ----
  class Connection {
    constructor(rpc, commitment, fetchImpl) { this.rpc = rpc; this.commitment = commitment || "confirmed"; this.fetch = fetchImpl || ((u, o) => fetch(u, o)); this.n = 0; }
    async call(method, params) {
      const res = await this.fetch(this.rpc, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify({ jsonrpc: "2.0", id: ++this.n, method, params }) });
      if (!res.ok) throw new Error("the cluster answered " + res.status + " to " + method);
      const j = await res.json();
      if (j.error) throw new Error(method + ": " + (j.error.message || JSON.stringify(j.error)));
      return j.result;
    }
    async getAccountInfo(pk) {
      const r = await this.call("getAccountInfo", [pk.toBase58(), { encoding: "base64", commitment: this.commitment }]);
      return r && r.value ? { lamports: r.value.lamports, owner: r.value.owner } : null;
    }
    async getTokenAccountBalance(pk) {
      const r = await this.call("getTokenAccountBalance", [pk.toBase58(), { commitment: this.commitment }]);
      return { value: r.value };
    }
    async getLatestBlockhash(commitment) {
      const r = await this.call("getLatestBlockhash", [{ commitment: commitment || this.commitment }]);
      return r.value;
    }
    async sendRawTransaction(raw, options) {
      let s = ""; for (let i = 0; i < raw.length; i++) s += String.fromCharCode(raw[i]);
      return this.call("sendTransaction", [btoa(s), { encoding: "base64", skipPreflight: !!(options && options.skipPreflight), preflightCommitment: this.commitment }]);
    }
  }

  return { b58encode, b58decode, sha256, isOnCurve, PublicKey, SYSTEM_PROGRAM, ATA_PROGRAM, MEMO_PROGRAM, findProgramAddress, ata, createAtaIdempotent, transferChecked, memo,
    compileMessage, unsignedWire, wireWith, decodeWire, Connection };
});
