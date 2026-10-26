import Ember.Spec.Slip
import Ember.Proof.Bytes

/-!
# Ember.Proof.Slip — SLIP decode ∘ encode = id (plan M5.2)

`Slip.encode p` is `END`, the escaped bytes of `p`, `END`
(`toList_encode`).  `Slip.decodeAll` is a left fold of the byte-at-a-time
decoder `Dec.feed` (`decodeAll_eq_foldl`).  Feeding an encoded frame to
the decoder — in any state, since the leading `END` resets it — leaves it
in its initial state and delivers exactly the frame, provided the frame
is not empty (the decoder ignores empty frames) and fits the MTU
(`feed_encode`, `decodeAll_encode`); the same for a stream of frames
(`decodeAll_encode_stream`).
-/

namespace Ember.Spec.Slip
open Ember

/-! ## `ByteArray.toList` and pushing a list of bytes -/

private theorem toList_loop (b : ByteArray) :
    ∀ (n i : Nat) (r : List UInt8), b.size - i = n →
      ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  have hsz : b.data.toList.length = b.size := Array.length_toList
  intro n
  induction n with
  | zero =>
    intro i r h
    have hi : ¬ i < b.size := by omega
    rw [ByteArray.toList.loop, if_neg hi, List.drop_eq_nil_of_le (by omega)]
    simp
  | succ n ih =>
    intro i r h
    have hi : i < b.size := by omega
    have hi' : i < b.data.toList.length := by omega
    have hi'' : i < b.data.size := hi
    rw [ByteArray.toList.loop, if_pos hi, ih _ _ (by omega), List.drop_eq_getElem_cons hi']
    have : b.get! i = b.data.toList[i] := by
      show b.data[i]! = _
      rw [getElem!_pos b.data i hi'']
      simp
    simp [this]

/-- `ByteArray.toList` lists the bytes of the array. -/
theorem toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  simp [ByteArray.toList, toList_loop b _ 0 [] rfl]

theorem toList_foldl_push (l : List UInt8) (out : ByteArray) :
    (l.foldl ByteArray.push out).toList = out.toList ++ l := by
  induction l generalizing out with
  | nil => simp
  | cons x t ih => simp [ih, toList_eq, ByteArray.push]

/-- Pushing the bytes of `p` onto an empty array rebuilds `p`. -/
theorem foldl_push_toList (p : ByteArray) : p.toList.foldl ByteArray.push .empty = p := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← toList_eq, toList_foldl_push, toList_eq, toList_eq]
  simp

theorem toList_append (a b : ByteArray) : (a ++ b).toList = a.toList ++ b.toList := by
  simp [toList_eq, ByteArray.data_append]

/-! ## The encoder -/

theorem toList_push (out : ByteArray) (e : UInt8) : (out.push e).toList = out.toList ++ [e] :=
  toList_foldl_push [e] out

/-- The bytes `encode` produces: `END`, each payload byte escaped, `END`. -/
theorem toList_encode (p : ByteArray) :
    (encode p).toList = END :: p.toList.flatMap encodeByte ++ [END] := by
  have outer : ∀ (l : List UInt8) (out : ByteArray),
      (l.foldl (fun b a => (encodeByte a).foldl (fun b a => b.push a) b) out).toList
        = out.toList ++ l.flatMap encodeByte := by
    intro l
    induction l with
    | nil => simp
    | cons x t ih =>
      intro out
      have := toList_foldl_push (encodeByte x) out
      simp only [List.foldl_cons, ih, List.flatMap_cons, ← List.append_assoc]
      exact congrArg (· ++ _) this
  unfold encode
  simp
  rw [toList_push, outer, toList_push]
  simp [ByteArray.toList_empty]

/-! ## The decoder as a fold -/

/-- One step of `decodeAll`: feed a byte, collect a completed frame. -/
def feedStep (maxLen : Nat) (s : Dec × Array ByteArray) (c : UInt8) : Dec × Array ByteArray :=
  match s.1.feed c maxLen with
  | (d', .frame f) => (d', s.2.push f)
  | (d', _) => (d', s.2)

/-- `decodeAll` folds `Dec.feed` over the stream, from the initial decoder. -/
theorem decodeAll_eq_foldl (s : ByteArray) (maxLen : Nat) :
    decodeAll s maxLen = (s.toList.foldl (feedStep maxLen) ({}, #[])).2.toList := by
  have body : ∀ (c : UInt8) (st : Dec × Array ByteArray),
      (match st.fst.feed c maxLen with
        | (d', r) =>
          match r with
          | Result.frame f => (pure (ForInStep.yield (d', st.snd.push f)) : Id _)
          | _ => pure (ForInStep.yield (d', st.snd)))
        = pure (ForInStep.yield (feedStep maxLen st c)) := by
    intro c st
    unfold feedStep
    rcases st.fst.feed c maxLen with ⟨d', r⟩
    cases r <;> rfl
  have key : ∀ (l : List UInt8) (st : Dec × Array ByteArray),
      (forIn (m := Id) l st fun c st =>
          match st.fst.feed c maxLen with
          | (d', r) =>
            match r with
            | Result.frame f => pure (ForInStep.yield (d', st.snd.push f))
            | _ => pure (ForInStep.yield (d', st.snd)))
        = pure (l.foldl (feedStep maxLen) st) := by
    intro l
    induction l with
    | nil => intro st; rfl
    | cons c t ih =>
      intro st
      rw [List.forIn_cons, body c st, pure_bind]
      exact ih _
  unfold decodeAll
  exact congrArg (fun (x : Id (Dec × Array ByteArray)) => x.run.2.toList) (key s.toList ({}, #[]))

/-! ## Feeding an encoded frame -/

theorem ext_dec {d e : Dec} (h1 : d.buf = e.buf) (h2 : d.esc = e.esc) (h3 : d.over = e.over) :
    d = e := by
  cases d; cases e; simp_all

/-- `END` resets the decoder, whatever its state. -/
theorem feed_END (d : Dec) (maxLen : Nat) : (d.feed END maxLen).1 = {} := by
  simp [Dec.feed]

/-- The escaped form of one payload byte stores that byte. -/
theorem foldl_feedStep_encodeByte (maxLen : Nat) (b : UInt8) (d : Dec) (out : Array ByteArray)
    (hesc : d.esc = false) (hover : d.over = false) (hsize : d.buf.size < maxLen) :
    (encodeByte b).foldl (feedStep maxLen) (d, out)
      = ({ buf := d.buf.push b, esc := false, over := false }, out) := by
  unfold encodeByte
  by_cases h1 : b = END
  · subst h1
    simp [feedStep, Dec.feed, Dec.store, hesc, hover, hsize, END, ESC, ESC_END]
  · by_cases h2 : b = ESC
    · subst h2
      simp [feedStep, Dec.feed, Dec.store, hesc, hover, hsize, END, ESC, ESC_END, ESC_ESC]
    · simp [feedStep, Dec.feed, Dec.store, hesc, hover, hsize, h1, h2]

/-- The escaped payload stores the payload, as long as it fits. -/
theorem foldl_feedStep_payload (maxLen : Nat) (l : List UInt8) (d : Dec) (out : Array ByteArray)
    (hesc : d.esc = false) (hover : d.over = false) (hsize : d.buf.size + l.length ≤ maxLen) :
    (l.flatMap encodeByte).foldl (feedStep maxLen) (d, out)
      = ({ buf := l.foldl ByteArray.push d.buf, esc := false, over := false }, out) := by
  induction l generalizing d with
  | nil => simp; exact ext_dec rfl hesc hover
  | cons x t ih =>
    simp only [List.flatMap_cons, List.foldl_append, List.length_cons] at hsize ⊢
    rw [foldl_feedStep_encodeByte maxLen x d out hesc hover (by omega),
      ih _ rfl rfl (by show (d.buf.push x).size + t.length ≤ maxLen; rw [ByteArray.size_push]; omega)]
    rfl

/-- Feeding `encode p` to the decoder in any state `d`: whatever `d` held
is flushed by the leading `END` (one `feedStep`), then exactly `p` is
delivered and the decoder is back in its initial state. -/
theorem feed_encode (maxLen : Nat) (p : ByteArray) (h0 : 0 < p.size) (hmax : p.size ≤ maxLen)
    (d : Dec) (out : Array ByteArray) :
    (encode p).toList.foldl (feedStep maxLen) (d, out)
      = ({}, (feedStep maxLen (d, out) END).2.push p) := by
  have hlen : p.toList.length = p.size := by rw [toList_eq]; exact Array.length_toList
  have hstart : feedStep maxLen (d, out) END = ({}, (feedStep maxLen (d, out) END).2) := by
    have : (feedStep maxLen (d, out) END).1 = {} := by
      simp only [feedStep]
      have := feed_END d maxLen
      split <;> simp_all
    exact Prod.ext this rfl
  rw [toList_encode, List.cons_append, List.foldl_cons, List.foldl_append, hstart,
    foldl_feedStep_payload maxLen p.toList {} _ rfl rfl (by rw [hlen]; simpa using hmax)]
  have hbuf : p.toList.foldl ByteArray.push ({} : Dec).buf = p := foldl_push_toList p
  have hne : ¬ p.size = 0 := by omega
  simp [hbuf, feedStep, Dec.feed, hne]

/-- M5.2, SLIP: decoding an encoded frame gives back that frame, for a
non-empty frame that fits the MTU. -/
theorem decodeAll_encode (p : ByteArray) (maxLen : Nat) (h0 : 0 < p.size) (hmax : p.size ≤ maxLen) :
    decodeAll (encode p) maxLen = [p] := by
  rw [decodeAll_eq_foldl, feed_encode maxLen p h0 hmax]
  simp [feedStep, Dec.feed]

/-- An empty frame encodes to `END END`, which the decoder ignores. -/
theorem decodeAll_encode_empty (maxLen : Nat) : decodeAll (encode .empty) maxLen = [] := by
  rw [decodeAll_eq_foldl, toList_encode]
  simp [ByteArray.toList_empty, feedStep, Dec.feed]

/-- A payload byte arriving at a full buffer switches to the oversize state. -/
theorem foldl_feedStep_encodeByte_full (maxLen : Nat) (b : UInt8) (d : Dec) (out : Array ByteArray)
    (hesc : d.esc = false) (hover : d.over = false) (hsize : ¬ d.buf.size < maxLen) :
    (encodeByte b).foldl (feedStep maxLen) (d, out)
      = ({ buf := .empty, esc := false, over := true }, out) := by
  unfold encodeByte
  by_cases h1 : b = END
  · subst h1
    simp [feedStep, Dec.feed, Dec.store, hesc, hover, hsize, END, ESC, ESC_END]
  · by_cases h2 : b = ESC
    · subst h2
      simp [feedStep, Dec.feed, Dec.store, hesc, hover, hsize, END, ESC, ESC_ESC]
    · simp [feedStep, Dec.feed, Dec.store, hesc, hover, hsize, h1, h2]

/-- In the oversize state payload bytes are discarded. -/
theorem foldl_feedStep_payload_over (maxLen : Nat) (l : List UInt8) (d : Dec) (out : Array ByteArray)
    (hesc : d.esc = false) (hover : d.over = true) :
    (l.flatMap encodeByte).foldl (feedStep maxLen) (d, out) = (d, out) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have step : (encodeByte x).foldl (feedStep maxLen) (d, out) = (d, out) := by
      unfold encodeByte
      by_cases h1 : x = END
      · subst h1
        simp [feedStep, Dec.feed, Dec.store, hesc, hover, END, ESC, ESC_END]
        exact ext_dec rfl hesc.symm hover.symm
      · by_cases h2 : x = ESC
        · subst h2
          simp [feedStep, Dec.feed, Dec.store, hesc, hover, END, ESC, ESC_ESC]
          exact ext_dec rfl hesc.symm hover.symm
        · simp [feedStep, Dec.feed, Dec.store, hesc, hover, h1, h2]
          exact ext_dec rfl hesc.symm hover.symm
    rw [List.flatMap_cons, List.foldl_append, step, ih]

/-- A frame longer than the MTU is dropped as a whole. -/
theorem decodeAll_encode_oversize (p : ByteArray) (maxLen : Nat) (hbig : maxLen < p.size) :
    decodeAll (encode p) maxLen = [] := by
  have hlen : p.toList.length = p.size := by rw [toList_eq]; exact Array.length_toList
  obtain ⟨x, rest, hdrop⟩ : ∃ x rest, p.toList.drop maxLen = x :: rest := by
    cases h : p.toList.drop maxLen with
    | nil => have := congrArg List.length h; simp at this; omega
    | cons x rest => exact ⟨x, rest, rfl⟩
  have hsplit : p.toList = p.toList.take maxLen ++ x :: rest := by
    rw [← hdrop, List.take_append_drop]
  have htake : (p.toList.take maxLen).length = maxLen := by simp; omega
  have hfull : ¬ ((p.toList.take maxLen).foldl ByteArray.push ByteArray.empty).size < maxLen := by
    have := congrArg List.length (toList_foldl_push (p.toList.take maxLen) .empty)
    rw [toList_eq, Array.length_toList] at this
    have h2 : (List.foldl ByteArray.push ByteArray.empty (List.take maxLen p.toList)).size
        = (List.foldl ByteArray.push ByteArray.empty (List.take maxLen p.toList)).data.size := rfl
    rw [h2, this, ByteArray.toList_empty]
    simp; omega
  rw [decodeAll_eq_foldl, toList_encode, List.cons_append, List.foldl_cons, List.foldl_append, hsplit,
    List.flatMap_append, List.flatMap_cons, List.foldl_append, List.foldl_append]
  have h0 : feedStep maxLen ({}, #[]) END = ({}, #[]) := by simp [feedStep, Dec.feed]
  rw [h0, foldl_feedStep_payload maxLen _ {} _ rfl rfl (by rw [htake]; simp),
    foldl_feedStep_encodeByte_full maxLen x _ _ rfl rfl hfull,
    foldl_feedStep_payload_over maxLen rest _ _ rfl rfl]
  simp [feedStep, Dec.feed]

/-- SLIP, complete: what the decoder makes of one encoded frame. -/
theorem decodeAll_encode_eq (p : ByteArray) (maxLen : Nat) :
    decodeAll (encode p) maxLen = if 0 < p.size ∧ p.size ≤ maxLen then [p] else [] := by
  by_cases h0 : 0 < p.size
  · by_cases h1 : p.size ≤ maxLen
    · rw [if_pos ⟨h0, h1⟩, decodeAll_encode p maxLen h0 h1]
    · rw [if_neg (fun h => h1 h.2), decodeAll_encode_oversize p maxLen (by omega)]
  · have : p = .empty := ByteArray.size_eq_zero_iff.mp (by omega)
    rw [if_neg (fun h => h0 h.1), this, decodeAll_encode_empty]

/-- A stream of encoded frames decodes to the frames, in order. -/
theorem decodeAll_encode_stream (ps : List ByteArray) (maxLen : Nat)
    (h : ∀ p ∈ ps, 0 < p.size ∧ p.size ≤ maxLen) :
    decodeAll (ps.foldl (fun acc p => acc ++ encode p) .empty) maxLen = ps := by
  have key : ∀ (ps : List ByteArray) (acc : ByteArray) (out : Array ByteArray),
      (∀ p ∈ ps, 0 < p.size ∧ p.size ≤ maxLen) →
      acc.toList.foldl (feedStep maxLen) ({}, #[]) = ({}, out) →
      (ps.foldl (fun acc p => acc ++ encode p) acc).toList.foldl (feedStep maxLen) ({}, #[])
        = ({}, out ++ ps.toArray) := by
    intro ps
    induction ps with
    | nil => intro acc out _ hacc; simpa using hacc
    | cons p t ih =>
      intro acc out hp hacc
      have ⟨hp0, hpm⟩ := hp p (by simp)
      rw [List.foldl_cons, ih (acc ++ encode p) (out.push p) (fun q hq => hp q (by simp [hq]))]
      · simp
      · rw [toList_append, List.foldl_append, hacc, feed_encode maxLen p hp0 hpm]
        simp [feedStep, Dec.feed]
  rw [decodeAll_eq_foldl, key ps .empty #[] h (by simp [ByteArray.toList_empty])]
  simp

/-! ## Axioms -/

/-- info: 'Ember.Spec.Slip.decodeAll_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decodeAll_encode

/-- info: 'Ember.Spec.Slip.decodeAll_encode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decodeAll_encode_eq

/-- info: 'Ember.Spec.Slip.decodeAll_encode_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decodeAll_encode_stream

end Ember.Spec.Slip
