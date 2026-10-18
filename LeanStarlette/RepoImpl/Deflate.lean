/-!
# RepoImpl: DEFLATE and gzip, compressing (RFC 1951, RFC 1952)

`GZipMiddleware` needs a compressor; Python's comes from zlib. This one is
LZ77 over a 32 KiB window (hash chains on three-byte prefixes, at most
`maxChain` candidates, greedy) with the fixed Huffman codes, falling back to
a stored block when a block would not shrink. Its bytes differ from
zlib's, as any two compressors' do; what is fixed is the decompressed
body, which the property tests check through lean-httpx's inflater and the
conformance cases through the client.

* `deflate src final` writes `src` as blocks: the last one final when
  `final`, otherwise followed by an empty stored block (zlib's
  `Z_SYNC_FLUSH`), so pieces concatenate into one stream.
* `crc32Update` is the gzip check value, by a 256-entry table.
* `gzipHeader` is zlib's for `wbits=16+MAX_WBITS` at level 9: no name, no
  time, `XFL=2`, `OS=3`.

All loops are bounded `for` loops: the definitions are total.
-/

namespace LeanStarlette.Deflate

/-! ## CRC-32 -/

/-- The CRC-32 table (polynomial `0xEDB88320`). -/
def crcTable : Array UInt32 := Id.run do
  let mut t : Array UInt32 := Array.mkEmpty 256
  for n in [0:256] do
    let mut c : UInt32 := n.toUInt32
    for _ in [0:8] do
      c := if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
    t := t.push c
  return t

/-- Continue a CRC-32 over more bytes (start from `0`). -/
def crc32Update (crc : UInt32) (data : ByteArray) : UInt32 := Id.run do
  let t := crcTable
  let mut c : UInt32 := crc ^^^ 0xFFFFFFFF
  for i in [0:data.size] do
    let b := data[i]!
    c := t[((c ^^^ b.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)
  return c ^^^ 0xFFFFFFFF

/-! ## Bits, least significant first -/

structure BitWriter where
  out : ByteArray
  acc : UInt64 := 0
  /-- Pending bits in `acc` (below 8 between writes). -/
  n : Nat := 0

/-- Append `len ≤ 32` bits. -/
@[inline] def BitWriter.put (w : BitWriter) (bits : UInt64) (len : Nat) : BitWriter := Id.run do
  let mut acc := w.acc ||| (bits <<< w.n.toUInt64)
  let mut n := w.n + len
  let mut out := w.out
  for _ in [0:5] do
    if n ≥ 8 then
      out := out.push (acc &&& 0xFF).toUInt8
      acc := acc >>> 8
      n := n - 8
  return { out, acc, n }

/-- Pad to a byte boundary with zero bits. -/
def BitWriter.align (w : BitWriter) : BitWriter :=
  if w.n == 0 then w else { out := w.out.push (w.acc &&& 0xFF).toUInt8, acc := 0, n := 0 }

/-- The low `len` bits of `c`, reversed (Huffman codes are sent from their
most significant bit). -/
def reverseBits (c : Nat) (len : Nat) : Nat := Id.run do
  let mut r := 0
  let mut c := c
  for _ in [0:len] do
    r := r * 2 + c % 2
    c := c / 2
  return r

/-! ## The fixed codes (RFC 1951 §3.2.6) -/

/-- Literal/length symbol `s`: its reversed code and length. -/
def fixedLitCode (s : Nat) : UInt64 × Nat :=
  if s < 144 then ((reverseBits (0x30 + s) 8).toUInt64, 8)
  else if s < 256 then ((reverseBits (0x190 + (s - 144)) 9).toUInt64, 9)
  else if s < 280 then ((reverseBits (s - 256) 7).toUInt64, 7)
  else ((reverseBits (0xC0 + (s - 280)) 8).toUInt64, 8)

def litTable : Array (UInt64 × Nat) := (Array.range 288).map fixedLitCode

def distCodes : Array UInt64 := (Array.range 30).map fun d => (reverseBits d 5).toUInt64

/-- Length bases and extra bits, symbols 257–285. -/
def lenBase : Array Nat := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
  67, 83, 99, 115, 131, 163, 195, 227, 258]
def lenExtra : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]
/-- Distance bases and extra bits, codes 0–29. -/
def distBase : Array Nat := #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769,
  1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]
def distExtra : Array Nat := #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
  11, 11, 12, 12, 13, 13]

/-- The last index whose base is at most `v`. -/
def lastAtMost (bases : Array Nat) (v : Nat) : Nat := Id.run do
  let mut k := 0
  for i in [0:bases.size] do
    if bases[i]! ≤ v then k := i
  return k

/-- For each length 0–258: its code index (into `lenBase`). -/
def lenIndex : Array Nat := (Array.range 259).map fun l => if l < 3 then 0 else lastAtMost lenBase l

/-- For each distance 1–512, and for `(d - 1) / 128` above: its code. -/
def distSmall : Array Nat := (Array.range 513).map fun d => if d = 0 then 0 else lastAtMost distBase d

def distCode (d : Nat) : Nat := if d ≤ 512 then distSmall[d]! else lastAtMost distBase d

/-! ## Tokens and blocks -/

/-- A token: a literal byte `< 256`, or `256 + length * 65536 + distance`
for a match. -/
abbrev Token := Nat

/-- The fixed-code size of a token, in bits. -/
def tokenBits (t : Token) : Nat :=
  if t < 256 then (litTable[t]!).2 else
  let len := (t - 256) / 65536
  let dist := (t - 256) % 65536
  let li := lenIndex[len]!
  (litTable[257 + li]!).2 + lenExtra[li]! + 5 + distExtra[distCode dist]!

/-- Write a token with the fixed codes. -/
def putToken (w : BitWriter) (t : Token) : BitWriter :=
  if t < 256 then let (c, l) := litTable[t]!; w.put c l else
  let len := (t - 256) / 65536
  let dist := (t - 256) % 65536
  let li := lenIndex[len]!
  let (c, l) := litTable[257 + li]!
  let w := w.put c l
  let w := w.put (len - lenBase[li]!).toUInt64 lenExtra[li]!
  let dc := distCode dist
  let w := w.put distCodes[dc]! 5
  w.put (dist - distBase[dc]!).toUInt64 distExtra[dc]!

/-- A stored block of `src[start, stop)` (at most 65535 bytes). -/
def putStored (w : BitWriter) (src : ByteArray) (start stop : Nat) (final : Bool) : BitWriter :=
  let w := (w.put (if final then 1 else 0) 3).align
  let len := stop - start
  let out := w.out.push (len % 256).toUInt8 |>.push (len / 256).toUInt8
    |>.push ((65535 - len) % 256).toUInt8 |>.push ((65535 - len) / 256).toUInt8
  { w with out := src.copySlice start out out.size len }

/-- Hash chains: candidates at most `maxChain` deep. -/
def maxChain : Nat := 32

def windowSize : Nat := 32768

/-- The block size, in input bytes. -/
def blockSize : Nat := 65535

/-- The length of the common prefix of `src[a…]` and `src[b…]`, at most `max`. -/
def matchLen (src : ByteArray) (a b max : Nat) : Nat := go max 0
where
  go : Nat → Nat → Nat
    | 0, l => l
    | k + 1, l => if src[a + l]! == src[b + l]! then go k (l + 1) else l

@[inline] def hash3 (src : ByteArray) (i : Nat) : Nat :=
  (((src[i]!.toUInt32 <<< 10) ^^^ (src[i + 1]!.toUInt32 <<< 5) ^^^ src[i + 2]!.toUInt32) &&& 0x7FFF).toNat

/-- LZ77 state across blocks: chain heads and links (positions plus one). -/
structure Chains where
  head : Array Nat := Array.replicate 32768 0
  prev : Array Nat := Array.replicate 32768 0

@[inline] def Chains.insert (c : Chains) (src : ByteArray) (i : Nat) : Chains :=
  if i + 2 < src.size then
    let h := hash3 src i
    match c with
    | ⟨head, prev⟩ =>
      -- read before writing, so each array stays unshared and is updated in place
      let old := head[h]!
      ⟨head.set! h (i + 1), prev.set! (i % 32768) old⟩
  else c

/-- The longest match for position `i` within `[i, stop)`, packed as
`length * 65536 + distance` (`0`: none): walk the chain from the newest
candidate, at most `maxChain` deep, inside the window. -/
def Chains.best (c : Chains) (src : ByteArray) (i stop : Nat) : Nat :=
  if i + 2 ≥ stop then 0 else
  let max := min 258 (stop - i)
  go maxChain c.head[hash3 src i]! 0 max
where
  go : Nat → Nat → Nat → Nat → Nat
    | 0, _, b, _ => b
    | k + 1, cand, b, max =>
      if cand == 0 then b else
      let p := cand - 1
      if p ≥ i || i - p > windowSize then b else
      let l := matchLen src p i max
      let b := if l > b / 65536 then l * 65536 + (i - p) else b
      if l == max then b else
      let next := c.prev[p % 32768]!
      if next == 0 || next - 1 ≥ p then b else go k next b max

/-- Insert positions `[i, i + k)` into the chains. -/
def Chains.insertRun (c : Chains) (src : ByteArray) : Nat → Nat → Chains
  | 0, _ => c
  | k + 1, i => (c.insert src i).insertRun src k (i + 1)

/-- Inside a match longer than this, only its last `longTail` positions
are inserted (the newest are the ones later matches use). -/
def longMatch : Nat := 32
def longTail : Nat := 4

/-- Tokens for `src[start, stop)`, and the chains after it. -/
def tokenize (c : Chains) (src : ByteArray) (start stop : Nat) : Array Token × Chains :=
  go (stop - start) c (Array.mkEmpty (stop - start)) start
where
  go : Nat → Chains → Array Token → Nat → Array Token × Chains
    | 0, c, toks, _ => (toks, c)
    | fuel + 1, c, toks, i =>
      if i ≥ stop then (toks, c) else
      let b := c.best src i stop
      let l := b / 65536
      if l ≥ 3 then
        let c := if l > longMatch then (c.insert src i).insertRun src longTail (i + l - longTail)
          else c.insertRun src l i
        go fuel c (toks.push (256 + b)) (i + l)
      else go fuel (c.insert src i) (toks.push src[i]!.toNat) (i + 1)

/-- **Compress `src` as DEFLATE blocks**: the last final when `final`,
otherwise ending in an empty stored block (byte-aligned, `Z_SYNC_FLUSH`). -/
def deflate (src : ByteArray) (final : Bool) : ByteArray := Id.run do
  let mut w : BitWriter := { out := ByteArray.emptyWithCapacity (src.size / 2 + 64) }
  let mut c : Chains := {}
  let nBlocks := (src.size + blockSize - 1) / blockSize
  for b in [0:nBlocks] do
    let start := b * blockSize
    let stop := min src.size (start + blockSize)
    let last := final && b + 1 == nBlocks
    let (toks, c') := tokenize c src start stop
    c := c'
    let bits := toks.foldl (fun a t => a + tokenBits t) (3 + 7)
    if bits > (stop - start + 5) * 8 then
      w := putStored w src start stop last
    else
      w := w.put (if last then 3 else 2) 3
      w := toks.foldl putToken w
      w := w.put 0 7
  if nBlocks == 0 && final then
    w := w.put 3 3
    w := w.put 0 7
  if !final then
    w := (w.put 0 3).align
    w := { w with out := w.out.push 0 |>.push 0 |>.push 0xFF |>.push 0xFF }
  return (w.align).out

/-! ## gzip -/

/-- zlib's gzip header at level 9. -/
def gzipHeader : ByteArray := ⟨#[0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 2, 3]⟩

/-- Four bytes, little-endian. -/
def le32 (n : Nat) : ByteArray :=
  ⟨#[(n % 256).toUInt8, (n / 256 % 256).toUInt8, (n / 65536 % 256).toUInt8, (n / 16777216 % 256).toUInt8]⟩

/-- The gzip trailer: CRC-32 and the size modulo 2³². -/
def gzipTrailer (crc : UInt32) (size : Nat) : ByteArray := le32 crc.toNat ++ le32 (size % 4294967296)

/-- **`gzip.compress(body)`**, as one member. -/
def gzip (src : ByteArray) : ByteArray :=
  gzipHeader ++ deflate src true ++ gzipTrailer (crc32Update 0 src) src.size

end LeanStarlette.Deflate
