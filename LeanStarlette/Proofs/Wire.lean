import LeanStarlette.RepoImpl.Wire
import LeanHttpx.Proofs.H1

/-!
# Proofs: responses on the wire

* `wire_chunked_decode`: the frames the transport writes for a streamed
  body (one per non-empty piece, then the last chunk) decode, with
  lean-httpx's verified decoder, back to the non-empty pieces.
* `wire_close`: a request that does not keep the connection gets
  `Connection: close` in the response, and the connection is not kept.
* `wire_no_body`: a response to `HEAD`, a `204` and a `304` have no body
  bytes on the wire.
-/

namespace LeanStarlette

open LeanHttpx LeanHttpx.H1

theorem chunkFrame_toList (c : ByteArray) :
    (chunkFrame c).data.toList = if c.size = 0 then [] else encodeChunk c := by
  unfold chunkFrame; split <;> simp

theorem foldl_frames (cs : List ByteArray) (acc : ByteArray) :
    (cs.foldl (fun acc c => acc ++ chunkFrame c) acc).data.toList =
      acc.data.toList ++ (cs.filter (0 < ·.size)).flatMap encodeChunk := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    by_cases h : c.size = 0
    · simp [ByteArray.data_append, chunkFrame_toList, h]
    · simp [ByteArray.data_append, chunkFrame_toList, h, Nat.pos_of_ne_zero h]

theorem wireChunked_eq (cs : List ByteArray) : wireChunked cs = encodeChunked (cs.filter (0 < ·.size)) := by
  apply ByteArray.ext
  apply Array.ext'
  simp only [wireChunked, ByteArray.data_append, Array.toList_append, foldl_frames, lastChunkFrame,
    encodeChunked, Keel.Codec.encodeBytes, chunks]
  simp

/-- **The chunked frames decode back to the pieces sent** (the non-empty
ones), leaving what follows. -/
theorem wire_chunked_decode (cs : List ByteArray) (h : ∀ c ∈ cs, c.size < maxChunkSize) (rest : ByteArray) :
    decodeChunked (wireChunked cs ++ rest) = some (cs.filter (0 < ·.size), rest) := by
  rw [wireChunked_eq]
  apply chunked_decode_encode
  intro c hc
  simp only [List.mem_filter, decide_eq_true_eq] at hc
  exact ⟨hc.2, h c hc.1⟩

theorem mem_insertSorted (x : String) : ∀ l : List String, x ∈ insertSorted x l
  | [] => by simp [insertSorted]
  | y :: ys => by
    unfold insertSorted
    split
    · next h => simp [beq_iff_eq.1 h]
    · split
      · simp
      · exact List.mem_cons_of_mem _ (mem_insertSorted x ys)

/-- **A request that does not keep the connection** (HTTP/1.0, or a
`close` token in `Connection`) **gets `Connection: close`, and the
connection is closed after the response.** -/
theorem wire_close (rq : WireRequest) (d : List (String × String)) (status : Nat) (hs : List (String × String))
    (h : rq.keepAlive = false) :
    ("Connection", "close") ∈ (wireHead rq d status hs).fields ∧ (wireHead rq d status hs).keepAlive = false := by
  simp only [wireHead, h, Bool.not_false, Bool.true_or, ite_true, Bool.false_and, and_true]
  apply List.mem_append_right
  exact List.mem_map.2 ⟨"close", mem_insertSorted _ _, rfl⟩

/-- **No body for `HEAD`, `204` or `304`.** -/
theorem wire_no_body (rq : WireRequest) (d : List (String × String)) (status : Nat) (hs : List (String × String))
    (h : rq.method = "HEAD" ∨ status = 204 ∨ status = 304) : (wireHead rq d status hs).body = .none := by
  rcases h with h | h | h <;> simp [wireHead, h]

end LeanStarlette
