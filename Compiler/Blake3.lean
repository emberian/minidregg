/-
# Compiler.Blake3 — BLAKE3-256 (hash mode) in Lean

The frame trailer of fn's wire grammar (`Compiler.FnWireGrammar`, fn §2 `:frame`) is
BLAKE3-256 of the frame's protected prefix. This is that hash: the reference
implementation's compression, chunk chaining and subtree-merge stack at 32-bit words,
ported from Bread `metatheory/Dregg2/Crypto/Blake3Compute.lean` (hash mode only; keyed,
derive-key and extended output are not used by anything in Mini and are not carried).

`hash` returns the 32-octet digest as the eight little-endian words of the root
compression, so `length_hash` is a definitional fact and the grammar's round-trip
theorems use the hash only through it.

TRUST CLASS: the identity "this function is BLAKE3" is established by compiled
evaluation against the BLAKE3 team's official vectors and fn's frame trailers
(`Compiler.Blake3Kat`, `native_decide` + `#assert_compiled`); it is an identity claim
about a function, never a property of the hash.
-/

namespace Minidregg.Compiler.Blake3

/-! ## §1 — Constants (BLAKE3 §2.1). -/

/-- Compression-function block length in bytes. -/
def BLOCK_LEN : Nat := 64
/-- Chunk length in bytes; a chunk is the unit the tree's leaves cover. -/
def CHUNK_LEN : Nat := 1024

/-- Flag: this block is the first of its chunk. -/
def CHUNK_START : UInt32 := 1
/-- Flag: this block is the last of its chunk. -/
def CHUNK_END : UInt32 := 2
/-- Flag: this compression is an interior tree node, not a chunk block. -/
def PARENT : UInt32 := 4
/-- Flag: this compression produces the extended output of the root node. -/
def ROOT : UInt32 := 8

/-- The BLAKE3 initialisation vector (the SHA-256 IV). -/
def IV : Array UInt32 :=
  #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

/-- The message-word permutation applied between rounds. -/
def MSG_PERMUTATION : Array Nat :=
  #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

/-! ## §2 — Word plumbing. -/

/-- Rotate a 32-bit word right by `n` (used only at `n ∈ {7, 8, 12, 16}`). -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Byte `i` of a `ByteArray`, or `0` at or past `stop` — the zero padding a short final block gets. -/
@[inline] def byteAt (b : ByteArray) (stop i : Nat) : UInt8 :=
  if i < stop && i < b.size then b.get! i else 0

/-- The sixteen little-endian message words of the 64-byte block at `off`, zero-padded past `stop`. -/
def wordsFrom (b : ByteArray) (off stop : Nat) : Array UInt32 :=
  Array.ofFn (n := 16) fun i =>
    let j := off + 4 * i.val
    (byteAt b stop j).toUInt32
      ||| ((byteAt b stop (j + 1)).toUInt32 <<< 8)
      ||| ((byteAt b stop (j + 2)).toUInt32 <<< 16)
      ||| ((byteAt b stop (j + 3)).toUInt32 <<< 24)

/-! ## §3 — The compression function. -/

/-- The `g` mixing function on state positions `a b c d` with message words `mx my`. -/
@[inline] def g (st : Array UInt32) (a b c d : Nat) (mx my : UInt32) : Array UInt32 :=
  let va := st[a]!; let vb := st[b]!; let vc := st[c]!; let vd := st[d]!
  let va := va + vb + mx
  let vd := rotr (vd ^^^ va) 16
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 12
  let va := va + vb + my
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((st.set! a va).set! b vb).set! c vc).set! d vd

/-- One round: four column mixes then four diagonal mixes. -/
def roundFn (st : Array UInt32) (m : Array UInt32) : Array UInt32 :=
  let st := g st 0 4 8  12 m[0]!  m[1]!
  let st := g st 1 5 9  13 m[2]!  m[3]!
  let st := g st 2 6 10 14 m[4]!  m[5]!
  let st := g st 3 7 11 15 m[6]!  m[7]!
  let st := g st 0 5 10 15 m[8]!  m[9]!
  let st := g st 1 6 11 12 m[10]! m[11]!
  let st := g st 2 7 8  13 m[12]! m[13]!
  g st 3 4 9 14 m[14]! m[15]!

/-- The between-rounds message permutation. -/
def permute (m : Array UInt32) : Array UInt32 :=
  MSG_PERMUTATION.map (fun i => m[i]!)

/-- `n` rounds, permuting the message between them. -/
def rounds : Nat → Array UInt32 → Array UInt32 → Array UInt32
  | 0,     st, _ => st
  | (n+1), st, m => rounds n (roundFn st m) (permute m)

/-- The BLAKE3 compression function: sixteen output words (the first eight are the chaining value;
all sixteen are used on the root/extended-output path). -/
def compress (cv : Array UInt32) (block : Array UInt32)
    (counter : UInt64) (blockLen flags : UInt32) : Array UInt32 :=
  let st : Array UInt32 :=
    #[cv[0]!, cv[1]!, cv[2]!, cv[3]!, cv[4]!, cv[5]!, cv[6]!, cv[7]!,
      IV[0]!, IV[1]!, IV[2]!, IV[3]!,
      counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags]
  let st := rounds 7 st block
  (List.range 8).foldl
    (fun (s : Array UInt32) i => (s.set! i (s[i]! ^^^ s[i + 8]!)).set! (i + 8) (s[i + 8]! ^^^ cv[i]!))
    st

/-! ## §4 — Nodes.

An `Output` is a node's *deferred* compression: the reference implementation keeps the last block
rather than its chaining value, because the root node is compressed a second time with `ROOT` set
(and once more per 64 bytes of extended output). Collapsing it to a chaining value early is the
classic way to get a correct-looking implementation that is wrong at the root. -/

/-- A node whose compression has not been performed yet. -/
structure Output where
  /-- Chaining value entering this compression. -/
  inputCv : Array UInt32
  /-- The sixteen message words of this node's block. -/
  blockWords : Array UInt32
  /-- Chunk index (chunk nodes) or `0` (parent nodes). -/
  counter : UInt64
  /-- Number of input bytes in this block (`64` except for a chunk's short final block). -/
  blockLen : UInt32
  /-- Flags for this compression, without `ROOT`. -/
  flags : UInt32

/-- The eight-word chaining value this node hands to its parent. -/
def Output.chainingValue (o : Output) : Array UInt32 :=
  (compress o.inputCv o.blockWords o.counter o.blockLen o.flags).extract 0 8

/-- A parent node over two child chaining values. -/
def parentOutput (l r key : Array UInt32) (flags : UInt32) : Output :=
  { inputCv := key, blockWords := l ++ r, counter := 0,
    blockLen := UInt32.ofNat BLOCK_LEN, flags := flags ||| PARENT }

/-- One chunk of `input[start, start+len)` as a node. `len = 0` is legal only for the single chunk of
an empty input, and produces the empty block flagged `CHUNK_START ||| CHUNK_END`. -/
def chunkOutput (key : Array UInt32) (baseFlags : UInt32) (counter : UInt64)
    (input : ByteArray) (start len : Nat) : Output :=
  if len == 0 then
    { inputCv := key, blockWords := wordsFrom ByteArray.empty 0 0, counter := counter,
      blockLen := 0, flags := baseFlags ||| CHUNK_START ||| CHUNK_END }
  else
    let stop := start + len
    let nBlocks := (len + 63) / 64
    let lastIdx := nBlocks - 1
    let cv := (List.range lastIdx).foldl
      (fun cv i =>
        let f := baseFlags ||| (if i == 0 then CHUNK_START else 0)
        (compress cv (wordsFrom input (start + 64 * i) stop) counter
          (UInt32.ofNat BLOCK_LEN) f).extract 0 8)
      key
    { inputCv := cv
      blockWords := wordsFrom input (start + 64 * lastIdx) stop
      counter := counter
      blockLen := UInt32.ofNat (len - 64 * lastIdx)
      flags := baseFlags ||| (if lastIdx == 0 then CHUNK_START else 0) ||| CHUNK_END }

/-- The reference implementation's subtree-stack merge rule: after chunk number `total`, merge while
`total` is even. `fuel` bounds the loop (`total` halves each step, so `64` can never be reached). -/
def mergeStack (key : Array UInt32) (flags : UInt32) :
    Nat → Array (Array UInt32) → Array UInt32 → UInt64 → Array (Array UInt32)
  | 0,     stack, cv, _ => stack.push cv
  | (f+1), stack, cv, total =>
    if (total &&& 1) == 0 && stack.size > 0 then
      let left := stack[stack.size - 1]!
      mergeStack key flags f stack.pop ((parentOutput left cv key flags).chainingValue) (total >>> 1)
    else stack.push cv

/-- The whole tree, as the still-uncompressed root node. `key`/`baseFlags` select the mode. -/
def hashInternal (key : Array UInt32) (baseFlags : UInt32) (input : ByteArray) : Output :=
  let n := input.size
  let nChunks := if n == 0 then 1 else (n + CHUNK_LEN - 1) / CHUNK_LEN
  let lastIdx := nChunks - 1
  let stack := (List.range lastIdx).foldl
    (fun stack i =>
      let out := chunkOutput key baseFlags (UInt64.ofNat i) input (i * CHUNK_LEN) CHUNK_LEN
      mergeStack key baseFlags 64 stack out.chainingValue (UInt64.ofNat (i + 1)))
    #[]
  let root := chunkOutput key baseFlags (UInt64.ofNat lastIdx) input
    (lastIdx * CHUNK_LEN) (n - lastIdx * CHUNK_LEN)
  (List.range stack.size).foldl
    (fun o k => parentOutput stack[stack.size - 1 - k]! o.chainingValue key baseFlags) root

/-! ## The digest -/

/-- A 32-bit word as four little-endian octets. -/
def wordBytes (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

/-- The 32-octet digest of a node as the root: its compression with `ROOT` set, output
block counter 0, first eight words. -/
def Output.rootDigest (o : Output) : List UInt8 :=
  let s := compress o.inputCv o.blockWords 0 o.blockLen (o.flags ||| ROOT)
  wordBytes s[0]! ++ wordBytes s[1]! ++ wordBytes s[2]! ++ wordBytes s[3]! ++
    wordBytes s[4]! ++ wordBytes s[5]! ++ wordBytes s[6]! ++ wordBytes s[7]!

/-- BLAKE3-256, hash mode: `blake3::hash`. -/
def hash (input : List UInt8) : List UInt8 :=
  (hashInternal IV 0 input.toByteArray).rootDigest

theorem length_hash (input : List UInt8) : (hash input).length = 32 := by
  simp [hash, Output.rootDigest, wordBytes]

/-- Lower-case hex. -/
def toHex (b : List UInt8) : String :=
  let digit (v : Nat) : Char := if v < 10 then Char.ofNat (48 + v) else Char.ofNat (87 + v)
  String.ofList (b.flatMap (fun x : UInt8 => [digit (x.toNat / 16), digit (x.toNat % 16)]))

end Minidregg.Compiler.Blake3
