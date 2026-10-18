import LeanStarlette.RepoImpl.Chunked
import LeanHttpx.Proofs.H1

/-!
# Proofs: the chunked-body decoder

`decodeChunkedBody` runs lean-httpx's chunked codec parsers for every
chunk-size line and for the last chunk, and takes each chunk's data as one
slice where the codec reads it byte by byte. On any chunk-encoded body
(followed by anything) it returns exactly the chunks' data, and the position
after the body (`decodeChunkedBody_encode`); with lean-httpx's
`chunked_decode_encode`, that is the codec's own answer
(`decodeChunkedBody_agrees`).
-/

namespace LeanStarlette

open LeanHttpx LeanHttpx.H1 Keel

/-- If the tokens from `pos` are `P ++ T`, the tokens from `size - |T|` are `T`. -/
private theorem rest_suffix {b : ByteArray} {pos : Nat} {P T : List UInt8} (hp : pos ≤ b.size)
    (h : Input.rest b pos = P ++ T) : Input.rest b (b.size - T.length) = T ∧
      b.size - T.length = pos + P.length := by
  have hl : (Input.rest b pos).length = P.length + T.length := by rw [h]; simp
  rw [Input.length_rest] at hl
  have hs : Input.size b = b.size := rfl
  have he : b.size - T.length = pos + P.length := by omega
  refine ⟨?_, he⟩
  rw [he]
  have : Input.rest b (pos + P.length) = (Input.rest b pos).drop P.length := by
    simp [Input.rest, List.drop_drop]
  rw [this, h]; simp

/-- Appending to a fold of appends. -/
theorem foldl_append_left (l : List ByteArray) (a b : ByteArray) :
    l.foldl (· ++ ·) (a ++ b) = a ++ l.foldl (· ++ ·) b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons, ByteArray.append_assoc, ih]

theorem concatChunks_cons (c : ByteArray) (cs : List ByteArray) :
    concatChunks (c :: cs) = c ++ concatChunks cs := by
  simp only [concatChunks, List.foldl_cons, ByteArray.empty_append]
  rw [← foldl_append_left, ByteArray.append_empty]

/-- The decoder on chunk-encoded input: from a position where the buffer
holds the encoding of `cs`, the last chunk and then `r`, it appends the
chunks to `acc` and returns the position where `r` starts. -/
theorem decodeChunksInto_encode (b : ByteArray) (r : List UInt8) :
    ∀ (cs : List ByteArray), (∀ c ∈ cs, 0 < c.size ∧ c.size < maxChunkSize) →
    ∀ (fuel pos : Nat) (acc : ByteArray), pos ≤ b.size → cs.length < fuel →
      Input.rest b pos = cs.flatMap encodeChunk ++ (lastChunkBytes ++ r) →
      decodeChunksInto b fuel pos acc = some (acc ++ concatChunks cs, b.size - r.length)
  | [], _, fuel, pos, acc, hp, hf, h => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have e : Input.rest b pos = hexDigits 0 ++ (crlf ++ (crlf ++ r)) := by
      rw [h]; simp [lastChunkBytes, List.append_assoc]
    have h1 := Parser.run_eq_of_parse (chunkSizeLine (ε := Unit)) (s := b)
      (by rw [e]; exact parse_chunkSizeLine 0 (by decide) _) hp
    have h2 := Parser.run_eq_of_parse (lastChunk (ε := Unit)) (s := b)
      (by rw [h]; exact parse_lastChunk r) hp
    simp only [decodeChunksInto, h1, h2, ite_true]
    simp [concatChunks]; rfl
  | c :: cs, hv, fuel, pos, acc, hp, hf, h => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hc := hv c (by simp)
    have hn : c.size ≠ 0 := by omega
    let R := cs.flatMap encodeChunk ++ (lastChunkBytes ++ r)
    let T := c.data.toList ++ (crlf ++ R)
    have e : Input.rest b pos = hexDigits c.size ++ (crlf ++ T) := by
      rw [h]; simp [T, R, encodeChunk, List.append_assoc]
    have h1 := Parser.run_eq_of_parse (chunkSizeLine (ε := Unit)) (s := b)
      (by rw [e]; exact parse_chunkSizeLine c.size hc.2 _) hp
    have e' : Input.rest b pos = (hexDigits c.size ++ crlf) ++ T := by rw [e]; simp
    obtain ⟨hT, hjT⟩ := rest_suffix hp e'
    have hs : Input.size b = b.size := rfl
    rw [hs] at h1
    -- the chunk's data, then CR LF, from `j`
    have hdl : c.data.toList.length = c.size := by simp
    have hcl : crlf.length = 2 := rfl
    have hcr : b[b.size - T.length + c.size]? = some CR := by
      have h0 := Input.get?_rest b (b.size - T.length) c.size
      rw [hT] at h0
      have hT0 : T[c.size]? = some CR := by
        simp only [T, crlf]; rw [List.getElem?_append_right (by omega), hdl, Nat.sub_self]; rfl
      rw [hT0] at h0
      exact h0.symm
    have hlf : b[b.size - T.length + c.size + 1]? = some LF := by
      have h0 := Input.get?_rest b (b.size - T.length) (c.size + 1)
      rw [hT] at h0
      have hT0 : T[c.size + 1]? = some LF := by
        simp only [T, crlf]; rw [List.getElem?_append_right (by omega), hdl,
          show c.size + 1 - c.size = 1 by omega]; rfl
      rw [hT0] at h0
      exact h0.symm
    have hx : b.extract (b.size - T.length) (b.size - T.length + c.size) = c := by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      apply Array.toList_inj.mp
      rw [Array.toList_extract, List.extract_eq_take_drop, show b.size - T.length + c.size - (b.size - T.length) = c.size by omega]
      have : b.data.toList.drop (b.size - T.length) = T := hT
      rw [this]
      simp [T, hdl]
    have eR : Input.rest b pos = (hexDigits c.size ++ crlf ++ c.data.toList ++ crlf) ++ R := by
      rw [h]; simp [R, encodeChunk, List.append_assoc]
    obtain ⟨hR, hjR⟩ := rest_suffix hp eR
    have hTl : T.length = c.size + 2 + R.length := by simp [T, crlf, hdl]; omega
    have hnext : b.size - T.length + c.size + 2 = b.size - R.length := by
      simp only [List.length_append, hdl, hcl] at hjR hjT; omega
    have ih := decodeChunksInto_encode b r cs (fun c' hc' => hv c' (by simp [hc'])) f
      (b.size - T.length + c.size + 2) (acc ++ c) (by omega) (by simp at hf; omega)
      (by rw [hnext, hR])
    simp only [decodeChunksInto, h1, hn, ite_false, hcr, hlf, and_self, ite_true, hx]
    rw [ih, concatChunks_cons, ByteArray.append_assoc]

/-- **The decoder agrees with the chunked coding**: on the chunk encoding of
`cs` (non-empty chunks under h11's 20-hex-digit bound) followed by anything,
`decodeChunkedBody` appends exactly the chunks' data to `into` and returns
the end of the encoding. -/
theorem decodeChunkedBody_encode (cs : List ByteArray) (hv : ∀ c ∈ cs, 0 < c.size ∧ c.size < maxChunkSize)
    (rest into : ByteArray) :
    decodeChunkedBody (encodeChunked cs ++ rest) 0 into =
      some (into ++ concatChunks cs, (encodeChunked cs).size) := by
  have hrest : Input.rest (encodeChunked cs ++ rest) 0 = cs.flatMap encodeChunk ++ (lastChunkBytes ++ rest.data.toList) := by
    simp [Input.rest, encodeChunked, chunks, Codec.encodeBytes, ByteArray.data_append, List.append_assoc]
  have hlen : cs.length < (encodeChunked cs ++ rest).size + 1 := by
    have : cs.length ≤ (cs.flatMap encodeChunk).length := by
      clear hrest hv
      induction cs with
      | nil => simp
      | cons c cs ih =>
        have := hexDigits_ne_nil c.size
        have : 0 < (hexDigits c.size).length := List.length_pos_iff.mpr this
        simp only [List.flatMap_cons, List.length_append, List.length_cons, encodeChunk] at ih ⊢
        omega
    have hs : (encodeChunked cs ++ rest).size = (cs.flatMap encodeChunk ++ (lastChunkBytes ++ rest.data.toList)).length := by
      rw [← hrest, Input.length_rest]; rfl
    simp only [List.length_append] at hs
    omega
  have := decodeChunksInto_encode (encodeChunked cs ++ rest) rest.data.toList cs hv _ 0 into (by omega) hlen hrest
  unfold decodeChunkedBody
  rw [this]
  simp [ByteArray.size_append]

/-- With lean-httpx's `chunked_decode_encode`: on every chunk-encoded body,
`decodeChunkedBody` gives the codec's chunks, and the position where the
codec's remainder starts. -/
theorem decodeChunkedBody_agrees (cs : List ByteArray) (hv : ∀ c ∈ cs, 0 < c.size ∧ c.size < maxChunkSize)
    (rest : ByteArray) :
    let b := encodeChunked cs ++ rest
    (decodeChunked b).map (fun p => (concatChunks p.1, b.size - p.2.size)) = decodeChunkedBody b 0 := by
  simp only [chunked_decode_encode cs hv rest, decodeChunkedBody_encode cs hv rest, Option.map_some,
    ByteArray.size_append, ByteArray.empty_append]
  congr 2; omega

end LeanStarlette
