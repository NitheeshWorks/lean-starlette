/-!
# RepoImpl: DEFLATE and gzip, compressing (RFC 1951, RFC 1952)

`GZipMiddleware` needs a compressor; Python's comes from zlib. This one is
LZ77 over a 32 KiB window (hash chains on three-byte prefixes, at most
`maxChain` candidates, zlib's lazy evaluation and `TOO_FAR` rule), then per
block of 65535 input bytes the smallest of a dynamic-code block (its own
Huffman codes, at most 15 bits), a fixed-code block and a stored block. Its bytes differ from
zlib's, as any two compressors' do; what is fixed is the decompressed
body, which the property tests check through lean-httpx's inflater and the
conformance cases through the client.

* `deflate src final` writes `src` as blocks: the last one final when
  `final`, otherwise followed by an empty stored block (zlib's
  `Z_SYNC_FLUSH`), so pieces concatenate into one stream.
* `crc32Update` is the gzip check value, eight bytes a step (slicing-by-8).
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

/-- Slicing-by-8 tables: entry `k * 256 + b` is the CRC of byte `b`
followed by `k` zero bytes. -/
def crcTables : Array UInt32 := Id.run do
  let t0 := crcTable
  let mut t := t0
  for k in [1:8] do
    for b in [0:256] do
      let prev := t[(k - 1) * 256 + b]!
      t := t.push (t0[(prev &&& 0xFF).toNat]! ^^^ (prev >>> 8))
  return t

/-- Continue a CRC-32 over more bytes (start from `0`): eight bytes a step
by `crcTables`, then one at a time. -/
def crc32Update (crc : UInt32) (data : ByteArray) : UInt32 := Id.run do
  let t := crcTables
  let mut c : UInt32 := crc ^^^ 0xFFFFFFFF
  let n8 := data.size / 8
  for h : j in [0:n8] do
    have : j * 8 + 7 < data.size := by have := h.upper; simp at this; omega
    let lo := c ^^^ ((data[j * 8]'(by omega)).toUInt32 ||| ((data[j * 8 + 1]'(by omega)).toUInt32 <<< 8) |||
      ((data[j * 8 + 2]'(by omega)).toUInt32 <<< 16) ||| ((data[j * 8 + 3]'(by omega)).toUInt32 <<< 24))
    let hi := (data[j * 8 + 4]'(by omega)).toUInt32 ||| ((data[j * 8 + 5]'(by omega)).toUInt32 <<< 8) |||
      ((data[j * 8 + 6]'(by omega)).toUInt32 <<< 16) ||| ((data[j * 8 + 7]'(by omega)).toUInt32 <<< 24)
    c := t[1792 + (lo &&& 0xFF).toNat]! ^^^ t[1536 + ((lo >>> 8) &&& 0xFF).toNat]! ^^^
      t[1280 + ((lo >>> 16) &&& 0xFF).toNat]! ^^^ t[1024 + (lo >>> 24).toNat]! ^^^
      t[768 + (hi &&& 0xFF).toNat]! ^^^ t[512 + ((hi >>> 8) &&& 0xFF).toNat]! ^^^
      t[256 + ((hi >>> 16) &&& 0xFF).toNat]! ^^^ t[(hi >>> 24).toNat]!
  for i in [n8 * 8:data.size] do
    c := t[((c ^^^ data[i]!.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)
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

/-- Write a token with the given codes (reversed) and lengths. -/
@[inline] def putTokenWith (litC : Array UInt64) (litL : Array Nat) (dC : Array UInt64) (dL : Array Nat)
    (w : BitWriter) (t : Token) : BitWriter :=
  if t < 256 then w.put litC[t]! litL[t]! else
  let len := (t - 256) / 65536
  let dist := (t - 256) % 65536
  let li := lenIndex[len]!
  let w := w.put litC[257 + li]! litL[257 + li]!
  let w := w.put (len - lenBase[li]!).toUInt64 lenExtra[li]!
  let dc := distCode dist
  let w := w.put dC[dc]! dL[dc]!
  w.put (dist - distBase[dc]!).toUInt64 distExtra[dc]!

def fixedLitCodes : Array UInt64 := litTable.map (·.1)
def fixedLitLens : Array Nat := litTable.map (·.2)
def fixedDistLens : Array Nat := Array.replicate 30 5

/-- Write a token with the fixed codes. -/
def putToken (w : BitWriter) (t : Token) : BitWriter :=
  putTokenWith fixedLitCodes fixedLitLens distCodes fixedDistLens w t

/-- A stored block of `src[start, stop)` (at most 65535 bytes). -/
def putStored (w : BitWriter) (src : ByteArray) (start stop : Nat) (final : Bool) : BitWriter :=
  let w := (w.put (if final then 1 else 0) 3).align
  let len := stop - start
  let out := w.out.push (len % 256).toUInt8 |>.push (len / 256).toUInt8
    |>.push ((65535 - len) % 256).toUInt8 |>.push ((65535 - len) / 256).toUInt8
  { w with out := src.copySlice start out out.size len }

/-! ## Dynamic codes (RFC 1951 §3.2.7) -/

/-- Huffman code lengths for the used symbols of `f` (two queues: sorted
leaves, and internal nodes in the order made). One used symbol gets
length 1. -/
def huffBuild (f : Array Nat) : Array Nat := Id.run do
  let leaves := ((Array.range f.size).filter (f[·]! > 0)).qsort
    (fun a b => f[a]! < f[b]! || (f[a]! == f[b]! && a < b))
  let m := leaves.size
  if m == 0 then return Array.replicate f.size 0
  if m == 1 then return (Array.replicate f.size 0).set! leaves[0]! 1
  let mut weight : Array Nat := leaves.map (f[·]!)
  let mut parent : Array Nat := Array.replicate (2 * m - 1) 0
  let mut qa := 0
  let mut qb := m
  for _ in [0:m - 1] do
    let mut picks : Array Nat := #[]
    for _ in [0:2] do
      if qa < m && (qb ≥ weight.size || weight[qa]! ≤ weight[qb]!) then
        picks := picks.push qa
        qa := qa + 1
      else
        picks := picks.push qb
        qb := qb + 1
    let id := weight.size
    weight := weight.push (weight[picks[0]!]! + weight[picks[1]!]!)
    parent := parent.set! picks[0]! id
    parent := parent.set! picks[1]! id
  let mut depth : Array Nat := Array.replicate (2 * m - 1) 0
  for j in [0:2 * m - 2] do
    let i := 2 * m - 3 - j
    depth := depth.set! i (depth[parent[i]!]! + 1)
  let mut lens := Array.replicate f.size 0
  for k in [0:m] do
    lens := lens.set! leaves[k]! depth[k]!
  return lens

/-- Code lengths of at most `limit` bits for frequencies `f`: while the
longest is over `limit`, halve the frequencies (used symbols stay used).
Fewer than two used symbols are completed with symbols `0` and `1`, so
every code is complete. -/
def huffLengths (freqs : Array Nat) (limit : Nat) : Array Nat := Id.run do
  let mut f := freqs
  if (f.filter (· > 0)).size < 2 then
    for s in [0:min 2 f.size] do
      if f[s]! == 0 then f := f.set! s 1
  for _ in [0:24] do
    let lens := huffBuild f
    if lens.foldl max 0 ≤ limit then return lens
    f := f.map fun x => if x == 0 then 0 else max 1 (x / 2)
  return huffBuild f

/-- Canonical codes for code lengths, bit-reversed for writing. -/
def canonCodes (lens : Array Nat) : Array UInt64 := Id.run do
  let mut count : Array Nat := Array.replicate 16 0
  for l in lens do
    if l > 0 then count := count.modify l (· + 1)
  let mut next : Array Nat := Array.replicate 16 0
  let mut code := 0
  for b in [1:16] do
    code := (code + count[b - 1]!) * 2
    next := next.set! b code
  let mut out : Array UInt64 := Array.replicate lens.size 0
  for s in [0:lens.size] do
    let l := lens[s]!
    if l > 0 then
      out := out.set! s (reverseBits next[l]! l).toUInt64
      next := next.modify l (· + 1)
  return out

/-- Code lengths run-length coded: `(symbol, extra)` with `16` (repeat the
previous 3–6 times), `17` (3–10 zeros), `18` (11–138 zeros). -/
def rleLens (ls : Array Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut i := 0
  for _ in [0:ls.size] do
    if i ≥ ls.size then break
    let v := ls[i]!
    let mut run := 0
    for j in [i:ls.size] do
      if ls[j]! == v && run < 138 then run := run + 1 else break
    if v == 0 then
      if run ≥ 11 then
        out := out.push (18, run - 11); i := i + run
      else if run ≥ 3 then
        out := out.push (17, run - 3); i := i + run
      else
        out := out.push (0, 0); i := i + 1
    else
      out := out.push (v, 0)
      let k := min (run - 1) 6
      if k ≥ 3 then
        out := out.push (16, k - 3); i := i + 1 + k
      else i := i + 1
  return out

/-- Extra bits after a code-length symbol. -/
def clExtra (s : Nat) : Nat := if s == 16 then 2 else if s == 17 then 3 else if s == 18 then 7 else 0

/-- The order code-length code lengths are sent in. -/
def clOrder : Array Nat := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- One past the last nonzero entry. -/
def usedPrefix (ls : Array Nat) : Nat := Id.run do
  let mut n := 0
  for i in [0:ls.size] do
    if ls[i]! > 0 then n := i + 1
  return n

/-- A block's dynamic codes and its size in bits with them. -/
structure Dynamic where
  litLens : Array Nat
  distLens : Array Nat
  clLens : Array Nat
  rle : Array (Nat × Nat)
  hlit : Nat
  hdist : Nat
  hclen : Nat
  bits : Nat

/-- Dynamic codes for a block's tokens (lengths at most 15, code-length
code at most 7). -/
def dynamicCodes (toks : Array Token) : Dynamic := Id.run do
  let mut lf : Array Nat := Array.replicate 286 0
  let mut df : Array Nat := Array.replicate 30 0
  for t in toks do
    if t < 256 then lf := lf.modify t (· + 1) else
      lf := lf.modify (257 + lenIndex[(t - 256) / 65536]!) (· + 1)
      df := df.modify (distCode ((t - 256) % 65536)) (· + 1)
  lf := lf.modify 256 (· + 1)
  let ll := huffLengths lf 15
  let dl := huffLengths df 15
  let hlit := max 257 (usedPrefix ll)
  let hdist := max 1 (usedPrefix dl)
  let rle := rleLens (ll.extract 0 hlit ++ dl.extract 0 hdist)
  let mut cf : Array Nat := Array.replicate 19 0
  for (s, _) in rle do cf := cf.modify s (· + 1)
  let cl := huffLengths cf 7
  let mut hclen := 19
  for _ in [0:15] do
    if hclen > 4 && cl[clOrder[hclen - 1]!]! == 0 then hclen := hclen - 1
  let mut bits := 3 + 14 + 3 * hclen
  for (s, _) in rle do bits := bits + cl[s]! + clExtra s
  for i in [0:286] do
    if i ≥ 257 then bits := bits + lf[i]! * (ll[i]! + lenExtra[i - 257]!) else bits := bits + lf[i]! * ll[i]!
  for i in [0:30] do bits := bits + df[i]! * (dl[i]! + distExtra[i]!)
  return { litLens := ll, distLens := dl, clLens := cl, rle, hlit, hdist, hclen, bits }

/-- Write a block with dynamic codes. -/
def putDynamic (w : BitWriter) (d : Dynamic) (toks : Array Token) (last : Bool) : BitWriter := Id.run do
  let mut w := w.put (if last then 5 else 4) 3
  w := w.put (d.hlit - 257).toUInt64 5
  w := w.put (d.hdist - 1).toUInt64 5
  w := w.put (d.hclen - 4).toUInt64 4
  for j in [0:d.hclen] do
    w := w.put d.clLens[clOrder[j]!]!.toUInt64 3
  let clC := canonCodes d.clLens
  for (s, x) in d.rle do
    w := w.put clC[s]! d.clLens[s]!
    w := w.put x.toUInt64 (clExtra s)
  let litC := canonCodes d.litLens
  let dC := canonCodes d.distLens
  w := toks.foldl (putTokenWith litC d.litLens dC d.distLens) w
  return w.put litC[256]! d.litLens[256]!

/-- Hash chains: candidates at most `maxChain` deep. -/
def maxChain : Nat := 32

def windowSize : Nat := 32768

/-- The block size, in input bytes. -/
def blockSize : Nat := 65535

/-- The length of the common prefix of `src[a…]` and `src[b…]` for `a ≤ b`,
at most `max` (and within `src`). -/
def matchLen (src : ByteArray) (a b max : Nat) (hab : a ≤ b) : Nat :=
  if hb : b ≤ src.size then go (min max (src.size - b)) (by omega) 0 else 0
where
  go (lim : Nat) (hlim : b + lim ≤ src.size) (l : Nat) : Nat :=
    if h : l < lim then
      if src[a + l]'(by omega) == src[b + l]'(by omega) then go lim hlim (l + 1) else l
    else l
  termination_by lim - l

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
      if hp : p ≥ i then b else
      if i - p > windowSize then b else
      let bl := b / 65536
      -- a candidate that differs at the current best length cannot beat it
      let l := if bl > 0 && src[p + bl]! != src[i + bl]! then 0 else matchLen src p i max (by omega)
      let b := if l > bl then l * 65536 + (i - p) else b
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

/-- zlib's `TOO_FAR`: a 3-byte match farther back than this costs more
than its literals. -/
def tooFar : Nat := 4096

/-- After this many literals in a row, positions are searched less often
(one in `1 + misses / accelEvery`, at most `maxStep`): incompressible
input costs little, and a match ends the run. -/
def accelEvery : Nat := 256
def maxStep : Nat := 8

/-- `best`, less 3-byte matches beyond `tooFar`. -/
@[inline] def Chains.bestAt (c : Chains) (src : ByteArray) (i stop : Nat) : Nat :=
  let b := c.best src i stop
  if b / 65536 == 3 && b % 65536 > tooFar then 0 else b

/-- Tokens for `src[start, stop)`, and the chains after it: zlib's lazy
evaluation (a match is taken only if the next position's is no longer). -/
def tokenize (c : Chains) (src : ByteArray) (start stop : Nat) : Array Token × Chains :=
  go (stop - start + 1) c (Array.mkEmpty (stop - start)) start 0 0
where
  /-- `cached` is one more than position `i`'s best match, already computed
  with `i` inserted (`0`: not yet); `miss` counts literals in a row. -/
  go : Nat → Chains → Array Token → Nat → Nat → Nat → Array Token × Chains
    | 0, c, toks, _, _, _ => (toks, c)
    | fuel + 1, c, toks, i, cached, miss =>
      if i ≥ stop then (toks, c) else
      let b := if cached != 0 then cached - 1 else c.bestAt src i stop
      let c := if cached != 0 then c else c.insert src i
      let l := b / 65536
      if l ≥ 3 then
        let b2 := if l < 258 && i + 1 < stop then c.bestAt src (i + 1) stop else 0
        if b2 / 65536 > l then
          go fuel (c.insert src (i + 1)) (toks.push src[i]!.toNat) (i + 1) (b2 + 1) 0
        else
          let c := if l > longMatch then c.insertRun src longTail (i + l - longTail)
            else c.insertRun src (l - 1) (i + 1)
          go fuel c (toks.push (256 + b)) (i + l) 0 0
      else
        let step := min (min maxStep (1 + miss / accelEvery)) (stop - i)
        let toks := (List.range step).foldl (fun t k => t.push src[i + k]!.toNat) toks
        go fuel c toks (i + step) 0 (miss + step)

/-- **Compress `src` as DEFLATE blocks**: each block stored, with the fixed
codes or with its own codes, whichever is smallest; the last final when
`final`, otherwise ending in an empty stored block (byte-aligned,
`Z_SYNC_FLUSH`). -/
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
    let fixed := toks.foldl (fun a t => a + tokenBits t) (3 + 7)
    let stored := (stop - start + 5) * 8
    let dyn := dynamicCodes toks
    if dyn.bits < fixed && dyn.bits ≤ stored then
      w := putDynamic w dyn toks last
    else if fixed ≤ stored then
      w := w.put (if last then 3 else 2) 3
      w := toks.foldl putToken w
      w := w.put 0 7
    else
      w := putStored w src start stop last
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
