import Ember.Proof.TcpSim

/-!
# Ember.Proof.TcpSimParse — TCP: parsing against the Spec (plan M5.5, second layer)

`tcp_input` checks and parses the segment in the packet buffer; the
Spec's `Tcp.parse` does the same on the segment's bytes.  Here:

* `parseMss_iter`: the Spec's option loop as an iteration (`spIter`);
* `mss_rel`: the stack's loop (`mssIter`, 16-bit indices into the packet
  buffer) computes the same;
* `parse_rel`: what `tcp_input` leaves in `sg` is the Spec's parsed
  segment (`SegRel`), and the two reject the same segments for the same
  reason;
* `tcp_input_sim`: `tcp_input` is `Tcp.parse` then `Tcp.input`;
* `tcp_tick_sim`: `tcp_tick` is `Tcp.tick`.

The last two are the statements of this layer.  Their hypotheses: the
two states agree (`Sim`), the packet buffer holds the segment
(`20 + n ≤ b.size < 65536`), and for the tick the Spec's invariant
(`Spec.Tcp.Inv`, proven preserved in `Proof/Tcp.lean`) and that the idle
and retry counters are below 255 (they stay below 60 and 9; that bound
is not proven here).
-/

set_option linter.unusedSimpArgs false

namespace Ember.Proof.Refine
open Ember Ember.Lang Ember.Lang.Sem

/-! ## The MSS option -/

/-- One round of `Spec.Tcp.parseMss` (`none`: the loop ends). -/
def spStep (p : ByteArray) (off : Nat) (s : Nat × Option UInt16) : Option (Nat × Option UInt16) :=
  if s.1 ≥ off then none
  else if (Bytes.get p s.1 == 0) = true then none
  else if (Bytes.get p s.1 == 1) = true then some (s.1 + 1, s.2)
  else if s.1 + 1 ≥ off then none
  else if (decide ((Bytes.get p (s.1 + 1)).toNat < 2) || decide (s.1 + (Bytes.get p (s.1 + 1)).toNat > off)) = true
    then none
  else if (Bytes.get p s.1 == 2 && (Bytes.get p (s.1 + 1)).toNat == 4) = true then
    some (s.1 + (Bytes.get p (s.1 + 1)).toNat, some (Bytes.get16 p (s.1 + 2)))
  else some (s.1 + (Bytes.get p (s.1 + 1)).toNat, s.2)

def spIter (p : ByteArray) (off : Nat) : Nat → Nat × Option UInt16 → Nat × Option UInt16
  | 0, s => s
  | n + 1, s =>
    match spStep p off s with
    | none => s
    | some s' => spIter p off n s'

theorem parseMss_iter (p : ByteArray) (off : Nat) :
    Spec.Tcp.parseMss p off = (spIter p off 40 (20, none)).2 := by
  unfold Spec.Tcp.parseMss
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run]
  have key : ∀ (l : List Nat) (s : Nat × Option UInt16),
      (forIn (m := Id) l s fun _ __s =>
            if __s.fst ≥ off then pure (ForInStep.done (__s.fst, __s.snd))
            else
              if (Bytes.get p __s.fst == 0) = true then pure (ForInStep.done (__s.fst, __s.snd))
              else
                if (Bytes.get p __s.fst == 1) = true then pure (ForInStep.yield (__s.fst + 1, __s.snd))
                else
                  if __s.fst + 1 ≥ off then pure (ForInStep.done (__s.fst, __s.snd))
                  else
                    if
                        (decide ((Bytes.get p (__s.fst + 1)).toNat < 2) ||
                            decide (__s.fst + (Bytes.get p (__s.fst + 1)).toNat > off)) =
                          true then
                      pure (ForInStep.done (__s.fst, __s.snd))
                    else
                      if (Bytes.get p __s.fst == 2 && (Bytes.get p (__s.fst + 1)).toNat == 4) = true then
                        pure
                          (ForInStep.yield
                            (__s.fst + (Bytes.get p (__s.fst + 1)).toNat, some (Bytes.get16 p (__s.fst + 2))))
                      else pure (ForInStep.yield (__s.fst + (Bytes.get p (__s.fst + 1)).toNat, __s.snd)))
        = spIter p off l.length s := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons a l ih =>
      intro s
      rw [List.forIn_cons]
      simp only [List.length_cons, spIter, spStep]
      by_cases h1 : s.1 ≥ off
      · simp only [if_pos h1]; rfl
      · simp only [if_neg h1]
        by_cases h2 : (Bytes.get p s.1 == 0) = true
        · simp only [if_pos h2]; rfl
        · simp only [if_neg h2]
          by_cases h3 : (Bytes.get p s.1 == 1) = true
          · simp only [if_pos h3]; exact ih _
          · simp only [if_neg h3]
            by_cases h4 : s.1 + 1 ≥ off
            · simp only [if_pos h4]; rfl
            · simp only [if_neg h4]
              by_cases h5 : (decide ((Bytes.get p (s.1 + 1)).toNat < 2)
                  || decide (s.1 + (Bytes.get p (s.1 + 1)).toNat > off)) = true
              · simp only [if_pos h5]; rfl
              · simp only [if_neg h5]
                by_cases h6 : (Bytes.get p s.1 == 2 && (Bytes.get p (s.1 + 1)).toNat == 4) = true
                · simp only [if_pos h6]; exact ih _
                · simp only [if_neg h6]; exact ih _
  exact congrArg Prod.snd (key _ _)

/-- The results of one round agree. -/
def MssR (off : Nat) : Option (UInt16 × Bool × UInt16) → Option (Nat × Option UInt16) → Prop
  | none, none => True
  | some a, some a' => a.1.toNat = a'.1 ∧ (a'.2 = if a.2.1 then some a.2.2 else none) ∧ a'.1 ≤ off
  | _, _ => False

theorem mssR_none (off : Nat) : MssR off none none := True.intro
theorem mssR_some (off : Nat) (a : UInt16 × Bool × UInt16) (a' : Nat × Option UInt16) (h1 : a.1.toNat = a'.1)
    (h2 : a'.2 = if a.2.1 then some a.2.2 else none) (h3 : a'.1 ≤ off) : MssR off (some a) (some a') :=
  ⟨h1, h2, h3⟩

/-- One round on both sides: the stack's 16-bit index into the packet
buffer and the Spec's index into the segment. -/
theorem mss_step_rel (b : ByteArray) (n : Nat) (off : UInt16) (hn : 20 + n ≤ b.size) (ho : off.toNat ≤ n)
    (ho60 : off.toNat ≤ 60) (s16 : UInt16 × Bool × UInt16) (s : Nat × Option UInt16)
    (h1 : s16.1.toNat = s.1) (h2 : s.2 = if s16.2.1 then some s16.2.2 else none) (h3 : s.1 ≤ off.toNat) :
    MssR off.toNat (mssStep b off s16) (spStep (b.extract 20 (20 + n)) off.toNat s) := by
  obtain ⟨i16, hm, m⟩ := s16
  obtain ⟨i, om⟩ := s
  simp only at h1 h2 h3
  subst h1
  have z20 : (20 : UInt16).toNat = 20 := rfl
  have z1 : (1 : UInt16).toNat = 1 := rfl
  have z2 : (2 : UInt16).toNat = 2 := rfl
  have z4 : (4 : UInt16).toNat = 4 := rfl
  simp only [mssStep, spStep]
  generalize hKb : Bytes.get b (20 + i16).toNat = Kb
  generalize hKp : Bytes.get (b.extract 20 (20 + n)) i16.toNat = Kp
  generalize hLb : Bytes.get b (20 + i16 + 1).toNat = Lb
  generalize hLp : Bytes.get (b.extract 20 (20 + n)) (i16.toNat + 1) = Lp
  generalize hGb : Bytes.get16 b (20 + i16 + 2).toNat = Gb
  generalize hGp : Bytes.get16 (b.extract 20 (20 + n)) (i16.toNat + 2) = Gp
  have c1 : (off ≤ i16) ↔ (i16.toNat ≥ off.toNat) := UInt16.le_iff_toNat_le
  by_cases a1 : off ≤ i16
  · rw [if_pos a1, if_pos (c1.mp a1)]; exact mssR_none _
  rw [if_neg a1, if_neg (fun q => a1 (c1.mpr q))]
  have hi : i16.toNat < off.toNat := by
    have : ¬ off.toNat ≤ i16.toNat := fun q => a1 (c1.mpr q)
    omega
  have e20 : (20 + i16).toNat = 20 + i16.toNat := by rw [UInt16.toNat_add, z20]; omega
  have hk : Kb = Kp := by rw [← hKb, ← hKp, e20, get_extract _ 20 _ _ (by omega) hn]
  subst hk
  by_cases a2 : (Kb == 0) = true
  · rw [if_pos a2, if_pos a2]; exact mssR_none _
  rw [if_neg a2, if_neg a2]
  by_cases a3 : (Kb == 1) = true
  · rw [if_pos a3, if_pos a3]
    exact mssR_some _ _ _ (by show (i16 + 1).toNat = i16.toNat + 1; rw [UInt16.toNat_add, z1]; omega) h2
      (by show i16.toNat + 1 ≤ off.toNat; omega)
  rw [if_neg a3, if_neg a3]
  have c4 : (off ≤ i16 + 1) ↔ (i16.toNat + 1 ≥ off.toNat) := by
    rw [UInt16.le_iff_toNat_le, UInt16.toNat_add, z1]; omega
  by_cases a4 : off ≤ i16 + 1
  · rw [if_pos a4, if_pos (c4.mp a4)]; exact mssR_none _
  rw [if_neg a4, if_neg (fun q => a4 (c4.mpr q))]
  have hi1 : i16.toNat + 1 < off.toNat := by
    have : ¬ i16.toNat + 1 ≥ off.toNat := fun q => a4 (c4.mpr q)
    omega
  have e21 : (20 + i16 + 1).toNat = 20 + (i16.toNat + 1) := by
    rw [UInt16.toNat_add, UInt16.toNat_add, z20, z1]; omega
  have hk1 : Lb = Lp := by rw [← hLb, ← hLp, e21, get_extract _ 20 _ _ (by omega) hn]
  subst hk1
  have bl := Lb.toNat_lt
  have hl : Lb.toUInt16.toNat = Lb.toNat := UInt8.toNat_toUInt16 _
  have hsum : (i16 + Lb.toUInt16).toNat = i16.toNat + Lb.toNat := by
    rw [UInt16.toNat_add, hl]; omega
  have c5 : (decide (Lb.toUInt16 < 2) || decide (off < i16 + Lb.toUInt16))
      = (decide (Lb.toNat < 2) || decide (i16.toNat + Lb.toNat > off.toNat)) := by
    rw [decide_eq_decide.mpr (show Lb.toUInt16 < 2 ↔ Lb.toNat < 2 by rw [UInt16.lt_iff_toNat_lt, hl, z2]),
      decide_eq_decide.mpr (show off < i16 + Lb.toUInt16 ↔ i16.toNat + Lb.toNat > off.toNat by
        rw [UInt16.lt_iff_toNat_lt, hsum])]
  rw [c5]
  by_cases a5 : (decide (Lb.toNat < 2) || decide (i16.toNat + Lb.toNat > off.toNat)) = true
  · rw [if_pos a5, if_pos a5]; exact mssR_none _
  rw [if_neg a5, if_neg a5]
  have hfit : i16.toNat + Lb.toNat ≤ off.toNat := by
    have : ¬ (i16.toNat + Lb.toNat > off.toNat) := by
      intro q; exact a5 (by simp [q])
    omega
  have c6 : (Lb.toUInt16 == 4) = (Lb.toNat == 4) := by
    apply beq_congr_iff
    rw [← UInt16.toNat_inj, hl, z4]
  rw [c6]
  by_cases a6 : (Kb == 2 && Lb.toNat == 4) = true
  · rw [if_pos a6, if_pos a6]
    have hl4 : Lb.toNat = 4 := by
      have := (Bool.and_eq_true _ _).mp a6
      exact beq_iff_eq.mp this.2
    have e22 : (20 + i16 + 2).toNat = 20 + (i16.toNat + 2) := by
      rw [UInt16.toNat_add, UInt16.toNat_add, z20, z2]; omega
    have hg : Gp = Gb := by rw [← hGb, ← hGp, e22, get16_extract b 20 _ _ (by omega) hn]
    refine mssR_some _ _ _ hsum ?_ hfit
    show some Gp = some Gb
    rw [hg]
  · rw [if_neg a6, if_neg a6]
    exact mssR_some _ _ _ hsum h2 hfit

/-- The two option loops, round for round. -/
theorem mss_iter_rel (b : ByteArray) (n : Nat) (off : UInt16) (hn : 20 + n ≤ b.size) (ho : off.toNat ≤ n)
    (ho60 : off.toNat ≤ 60) : ∀ (k : Nat) (s16 : UInt16 × Bool × UInt16) (s : Nat × Option UInt16),
    s16.1.toNat = s.1 → (s.2 = if s16.2.1 then some s16.2.2 else none) → s.1 ≤ off.toNat →
    (spIter (b.extract 20 (20 + n)) off.toNat k s).2
      = if (mssIter b off k s16).2.1 then some (mssIter b off k s16).2.2 else none := by
  intro k
  induction k with
  | zero => intro s16 s _ h2 _; exact h2
  | succ k ih =>
    intro s16 s h1 h2 h3
    have hstep := mss_step_rel b n off hn ho ho60 s16 s h1 h2 h3
    show (match spStep (b.extract 20 (20 + n)) off.toNat s with
      | none => s
      | some s' => spIter (b.extract 20 (20 + n)) off.toNat k s').2
      = if (match mssStep b off s16 with
          | none => s16
          | some s' => mssIter b off k s').2.1 then
          some (match mssStep b off s16 with
            | none => s16
            | some s' => mssIter b off k s').2.2 else none
    cases hA : mssStep b off s16 <;> cases hB : spStep (b.extract 20 (20 + n)) off.toNat s <;>
      rw [hA, hB] at hstep
    · exact h2
    · exact absurd hstep id
    · exact absurd hstep id
    · have hs' : _ ∧ _ ∧ _ := hstep
      exact ih _ _ hs'.1 hs'.2.1 hs'.2.2

/-- **`parse_mss` is `Spec.Tcp.parseMss`.** -/
theorem mss_rel (b : ByteArray) (n : Nat) (off : UInt16) (hn : 20 + n ≤ b.size) (ho : off.toNat ≤ n)
    (ho20 : 20 ≤ off.toNat) (ho60 : off.toNat ≤ 60) :
    Spec.Tcp.parseMss (b.extract 20 (20 + n)) off.toNat
      = if (mssIter b off 40 (20, false, 0)).2.1 then some (mssIter b off 40 (20, false, 0)).2.2 else none := by
  rw [parseMss_iter]
  exact mss_iter_rel b n off hn ho ho60 40 (20, false, 0) (20, none) rfl rfl ho20

/-! ## The header -/

/-- `Spec.Tcp.parse`, case by case. -/
theorem tcp_parse_eq (src dst : UInt32) (P : ByteArray) :
    Spec.Tcp.parse src dst P =
      if P.size < 20 then .error "short-tcp"
      else if (Bytes.get P 12 >>> 4).toNat * 4 < 20 || (Bytes.get P 12 >>> 4).toNat * 4 > P.size then
        .error "bad-tcp-header"
      else if !Spec.Checksum.verifies (Spec.Checksum.sum P 0 P.size (Spec.Checksum.pseudo src dst 6 P.size)) then
        .error "bad-tcp-checksum"
      else .ok { sport := Bytes.get16 P 0, dport := Bytes.get16 P 2, seq := Bytes.get32 P 4, ack := Bytes.get32 P 8,
                 flags := Bytes.get P 13 &&& 0x3F, wnd := Bytes.get16 P 14,
                 mss := Spec.Tcp.parseMss P ((Bytes.get P 12 >>> 4).toNat * 4),
                 data := Bytes.slice P ((Bytes.get P 12 >>> 4).toNat * 4)
                   (P.size - (Bytes.get P 12 >>> 4).toNat * 4) } := by
  unfold Spec.Tcp.parse
  simp [Spec.Ipv4.protoTcp]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try simp_all) <;> (try rfl)

theorem extract_extract (b : ByteArray) (s e a m : Nat) (h : s + a + m ≤ e) (he : e ≤ b.size) :
    (b.extract s e).extract a (a + m) = b.extract (s + a) (s + a + m) := by
  apply Bytes.ext_get
  · rw [ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]; omega
  · intro j hj
    rw [ByteArray.size_extract, ByteArray.size_extract] at hj
    rw [get_extract _ a _ j (by omega) (by rw [ByteArray.size_extract]; omega),
      get_extract _ s _ (a + j) (by omega) he, get_extract _ (s + a) _ j (by omega) (by omega), Nat.add_assoc]

theorem tcpDoff_toNat (b : ByteArray) : (tcpDoff b).toNat = (Bytes.get b 32 >>> 4).toNat * 4 := by
  have h15 : (Bytes.get b 32 >>> 4).toNat ≤ 15 := by
    have := (Bytes.get b 32).toNat_lt
    rw [UInt8.toNat_shiftRight]
    show (Bytes.get b 32).toNat >>> 4 ≤ 15
    rw [Nat.shiftRight_eq_div_pow]; omega
  have z4 : (4 : UInt16).toNat = 4 := rfl
  simp only [tcpDoff]
  rw [UInt16.toNat_mul, UInt8.toNat_toUInt16, z4]; omega

/-- **`tcp_input` parses as `Spec.Tcp.parse`**: the same segments are
rejected, for the same reason, and otherwise the segment record is the
Spec's parsed segment. -/
theorem parse_rel (w : TW) (ourIp src dst : UInt32) (n : UInt16) (hn : 20 + n.toNat ≤ w.b.size) :
    (∀ r, Spec.Tcp.parse src dst (w.b.extract 20 (20 + n.toNat)) = .error r →
      tcpInputW w ourIp src dst n = dropW w r) ∧
    (∀ S, Spec.Tcp.parse src dst (w.b.extract 20 (20 + n.toNat)) = .ok S →
      SegRel (parseMssW (tcpParse w src n) (tcpDoff w.b)).sg w.b S ∧
      tcpInputW w ourIp src dst n = segW (parseMssW (tcpParse w src n) (tcpDoff w.b)) ourIp) := by
  have hP : (w.b.extract 20 (20 + n.toNat)).size = n.toNat := by rw [ByteArray.size_extract]; omega
  have z20 : (20 : UInt16).toNat = 20 := rfl
  have hD := tcpDoff_toNat w.b
  have bn := n.toNat_lt
  rw [tcp_parse_eq, hP]
  have c1 : (n < 20) ↔ n.toNat < 20 := by rw [UInt16.lt_iff_toNat_lt, z20]
  by_cases a1 : n.toNat < 20
  · rw [if_pos a1]
    refine ⟨?_, fun S hS => by cases hS⟩
    intro r hr
    cases hr
    show (if n < 20 then _ else _) = _
    rw [if_pos (c1.mpr a1)]
  rw [if_neg a1]
  have h12 : Bytes.get (w.b.extract 20 (20 + n.toNat)) 12 = Bytes.get w.b 32 :=
    get_extract _ 20 _ 12 (by omega) hn
  rw [h12, ← hD]
  have c2 : (tcpDoff w.b < 20 || n < tcpDoff w.b)
      = (decide ((tcpDoff w.b).toNat < 20) || decide ((tcpDoff w.b).toNat > n.toNat)) := by
    rw [decide_eq_decide.mpr (show tcpDoff w.b < 20 ↔ (tcpDoff w.b).toNat < 20 by
        rw [UInt16.lt_iff_toNat_lt, z20]),
      decide_eq_decide.mpr (show n < tcpDoff w.b ↔ (tcpDoff w.b).toNat > n.toNat by
        rw [UInt16.lt_iff_toNat_lt])]
  by_cases a2 : (decide ((tcpDoff w.b).toNat < 20) || decide ((tcpDoff w.b).toNat > n.toNat)) = true
  · rw [if_pos a2]
    refine ⟨?_, fun S hS => by cases hS⟩
    intro r hr
    cases hr
    show (if n < 20 then _ else if (tcpDoff w.b < 20 || n < tcpDoff w.b) = true then _ else _) = _
    rw [if_neg (fun q => a1 (c1.mp q)), c2, if_pos a2]
  rw [if_neg a2]
  have hsum : Spec.Checksum.sum (w.b.extract 20 (20 + n.toNat)) 0 n.toNat (Spec.Checksum.pseudo src dst 6 n.toNat)
      = Spec.Checksum.sum w.b 20 n.toNat (Spec.Checksum.pseudo src dst 6 n.toNat) :=
    Spec.Checksum.sum_congr (fun i hi => by rw [get_extract _ 20 _ _ (by omega) hn, Nat.zero_add]) _
  rw [hsum]
  have hW : ∀ X : TW, (if n < 20 then dropW w "short-tcp"
      else if (tcpDoff w.b < 20 || n < tcpDoff w.b) = true then dropW w "bad-tcp-header"
      else if (!Spec.Checksum.verifies (Spec.Checksum.sum w.b 20 n.toNat (Spec.Checksum.pseudo src dst 6 n.toNat)))
          = true then dropW w "bad-tcp-checksum"
      else X)
      = if (!Spec.Checksum.verifies (Spec.Checksum.sum w.b 20 n.toNat (Spec.Checksum.pseudo src dst 6 n.toNat)))
          = true then dropW w "bad-tcp-checksum" else X := by
    intro X
    rw [if_neg (fun q => a1 (c1.mp q)), c2, if_neg a2]
  by_cases a3 : (!Spec.Checksum.verifies (Spec.Checksum.sum w.b 20 n.toNat
      (Spec.Checksum.pseudo src dst 6 n.toNat))) = true
  · rw [if_pos a3]
    refine ⟨?_, fun S hS => by cases hS⟩
    intro r hr
    cases hr
    exact (hW _).trans (if_pos a3)
  rw [if_neg a3]
  refine ⟨fun r hr => (by cases hr), ?_⟩
  intro S hS
  cases hS
  refine ⟨?_, (hW _).trans (if_neg a3)⟩
  have ho : (tcpDoff w.b).toNat ≤ n.toNat := by
    have : ¬ (tcpDoff w.b).toNat > n.toNat := fun q => a2 (by simp [q])
    omega
  have ho20 : 20 ≤ (tcpDoff w.b).toNat := by
    have : ¬ (tcpDoff w.b).toNat < 20 := fun q => a2 (by simp [q])
    omega
  have ho60 : (tcpDoff w.b).toNat ≤ 60 := by
    have := (Bytes.get w.b 32).toNat_lt
    rw [hD, UInt8.toNat_shiftRight]
    show (Bytes.get w.b 32).toNat >>> 4 * 4 ≤ 60
    rw [Nat.shiftRight_eq_div_pow]; omega
  have e1 : (20 + tcpDoff w.b).toNat = 20 + (tcpDoff w.b).toNat := by rw [UInt16.toNat_add, z20]; omega
  have e2 : (n - tcpDoff w.b).toNat = n.toNat - (tcpDoff w.b).toNat := by rw [UInt16.toNat_sub]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (get16_extract w.b 20 _ 0 (by omega) hn).symm
  · exact (get16_extract w.b 20 _ 2 (by omega) hn).symm
  · exact (get32_extract w.b 20 _ 4 (by omega) hn).symm
  · exact (get32_extract w.b 20 _ 8 (by omega) hn).symm
  · show Bytes.get w.b 33 &&& 63 = Bytes.get (w.b.extract 20 (20 + n.toNat)) 13 &&& 0x3F
    rw [get_extract _ 20 _ 13 (by omega) hn]
  · exact mss_rel w.b n.toNat (tcpDoff w.b) hn ho ho20 ho60
  · show Bytes.slice _ _ _ = w.b.extract (20 + tcpDoff w.b).toNat ((20 + tcpDoff w.b).toNat + (n - tcpDoff w.b).toNat)
    rw [e1, e2]
    exact extract_extract w.b 20 _ _ _ (by omega) hn
  · show (20 + tcpDoff w.b).toNat + (n - tcpDoff w.b).toNat ≤ w.b.size
    rw [e1, e2]; omega

/-- **`tcp_input` is `Spec.Tcp.parse` then `Spec.Tcp.input`**: a segment
the Spec rejects is dropped with the Spec's reason; otherwise the Spec's
step ends in a state the stack's simulates, the transmissions and drops
of the two being the same. -/
theorem tcp_input_sim (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (src dst : UInt32) (n : UInt16)
    (hn : 20 + n.toNat ≤ w.b.size) (hb : w.b.size < 65536) :
    (∀ r, Spec.Tcp.parse src dst (w.b.extract 20 (20 + n.toNat)) = .error r →
      tcpInputW w ourIp src dst n = dropW w r) ∧
    (∀ S, Spec.Tcp.parse src dst (w.b.extract 20 (20 + n.toNat)) = .ok S →
      Sim ourIp (tcpInputW w ourIp src dst n) ((Spec.Tcp.input src S).run c).2 ev0 id0) := by
  obtain ⟨p1, p2⟩ := parse_rel w ourIp src dst n hn
  refine ⟨p1, ?_⟩
  intro S hS
  obtain ⟨hs, hW⟩ := p2 S hS
  rw [hW]
  exact segment_wp ourIp (parseMssW (tcpParse w src n) (tcpDoff w.b)) c ev0 id0
    ⟨h.tcb, h.iss, h.ip, h.id, h.evs, h.mss⟩ hd src S hs rfl hb
    (fun _ c' => Sim ourIp (segW (parseMssW (tcpParse w src n) (tcpDoff w.b)) ourIp) c' ev0 id0)
    (fun _ x => x)

/-- **`tcp_tick` is `Spec.Tcp.tick`**, as a statement about the two results. -/
theorem tcp_tick_sim (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (hI : Spec.Tcp.Inv c.tcb)
    (hidle : c.tcb.idle < 255) (hretr : c.tcb.retries < 255) :
    Sim ourIp (tickW w ourIp) (Spec.Tcp.tick.run c).2 ev0 id0 :=
  tick_wp ourIp w c ev0 id0 h hd hI hidle hretr (fun _ c' => Sim ourIp (tickW w ourIp) c' ev0 id0) (fun _ x => x)

/-! ## The two layers joined

The raw layer (`RefineTcp*.lean`) needs size facts about the state; they
follow from `TcbRel` and the size of the packet buffer.  So the code
itself, run by the Ember semantics, does what the Spec does. -/

theorem TcbRel.raw {r : RawTcb} {pd : ByteArray} {T : Spec.Tcp.Tcb} (h : TcbRel r pd T) :
    r.sent.toNat ≤ r.pend_len.toNat ∧ r.pend_len.toNat ≤ 256 ∧ r.pend_len.toNat + r.wnd.toNat ≤ 256 ∧
      (r.pend_len - r.sent).toNat = r.pend_len.toNat - r.sent.toNat := by
  have h1 := h.plen; have h2 := h.sent; have h3 := h.hsent; have h4 := h.hcap; have h5 := h.hour
  have h6 := h.wnd_eq; have h7 := h.unsent
  have hc : T.cap ≤ 256 := by simp only [Spec.Tcp.Tcb.cap]; omega
  have hw : T.wnd = T.cap - T.pending.size := rfl
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem segFinW_keep (w : TW) (f i a : Bool) :
    (segFinW w f i a).1.r.pend_len = w.r.pend_len ∧ (segFinW w f i a).1.r.sent = w.r.sent ∧
      (segFinW w f i a).1.pd = w.pd ∧ (segFinW w f i a).1.b = w.b := by
  by_cases hc : (f && (i && (w.sg.seq + w.sg.dlen.toUInt32 == w.r.rcv_nxt))) = true
  · rw [segFinW_fin w f i a hc]
    repeat' split
    all_goals exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [segFinW_no w f i a hc]; exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The packet buffer keeps its size

Every TCP function leaves the packet buffer as long as it was (it is a
fixed array; here that is a fact about the transcribed functions). -/

theorem emitW_bsz (w : TW) (ourIp dst : UInt32) (sport dport : UInt16) (seq ack : UInt32) (flags : UInt8)
    (wn : UInt16) (m : Bool) (so n : UInt16) :
    (emitW w ourIp dst sport dport seq ack flags wn m so n).b.size = w.b.size := by
  simp [emitW]

theorem sendSegW_bsz (w : TW) (ourIp : UInt32) (flags : UInt8) (seq : UInt32) (so n : UInt16) (m : Bool) :
    (sendSegW w ourIp flags seq so n m).b.size = w.b.size := by
  simp [sendSegW, emitW]

theorem dropW_b (w : TW) (r : String) : (dropW w r).b = w.b := rfl
theorem noteW_b (w : TW) (r : String) : (noteW w r).b = w.b := rfl

theorem resetW_bsz (w : TW) (ourIp : UInt32) : (resetW w ourIp).b.size = w.b.size := by
  unfold resetW; split <;> simp only [emitW_bsz]

theorem listenW_bsz (w : TW) (ourIp : UInt32) : (listenW w ourIp).b.size = w.b.size := by
  unfold listenW
  repeat' split
  all_goals simp only [dropW_b, resetW_bsz, sendSegW_bsz]

theorem ackW_bsz (w : TW) (ourIp : UInt32) : (ackW w ourIp).2.b.size = w.b.size := by
  by_cases h1 : w.r.snd_nxt - w.r.snd_una < ackD w
  · rw [ackW_unsent w ourIp h1]; simp only [dropW_b, sendSegW_bsz]
  · by_cases h2 : (ackD w == 0) = true
    · rw [ackW_zero w ourIp h1 h2]
    · rw [ackW_adv w ourIp h1 h2]
      repeat' split
      all_goals simp only []

theorem segAckW_ok_b (w : TW) (ourIp : UInt32) (w1 : TW) (h : segAckW w ourIp = .ok w1) : w1.b = w.b := by
  rw [segAckW] at h
  by_cases s1 : (w.r.st == 1) = true
  · rw [if_pos s1] at h
    by_cases bad : (w.sg.ack != w.r.snd_nxt) = true
    · rw [if_pos bad] at h; cases h
    · rw [if_neg bad] at h; cases h; simp only []
  · rw [if_neg s1] at h
    by_cases ok : (ackW w ourIp).1 = true
    · rw [if_pos ok] at h; cases h; exact (ackW_keep w ourIp ok).2
    · rw [if_neg ok] at h; cases h

theorem segAckW_err_bsz (w : TW) (ourIp : UInt32) (w1 : TW) (h : segAckW w ourIp = .error w1) :
    w1.b.size = w.b.size := by
  rw [segAckW] at h
  by_cases s1 : (w.r.st == 1) = true
  · rw [if_pos s1] at h
    by_cases bad : (w.sg.ack != w.r.snd_nxt) = true
    · rw [if_pos bad] at h; cases h; simp only [dropW_b, resetW_bsz]
    · rw [if_neg bad] at h; cases h
  · rw [if_neg s1] at h
    by_cases ok : (ackW w ourIp).1 = true
    · rw [if_pos ok] at h; cases h
    · rw [if_neg ok] at h; cases h; exact ackW_bsz w ourIp

theorem segDataW_b (w : TW) : (segDataW w).1.b = w.b := by
  by_cases hc : 0 < w.sg.dlen ∧ (w.r.st == 2 || (w.r.st == 5 || w.r.st == 6)) = true
  · rw [segDataW_take w hc.1 hc.2]; exact dW_b w
  · rw [segDataW_none w hc]

theorem armW_b (w : TW) (was : Bool) : (armW w was).b = w.b := by
  unfold armW; split <;> simp only []

theorem outRest_bsz (w : TW) (ourIp : UInt32) (a : Bool) : (outRest w ourIp a).b.size = w.b.size := by
  unfold outRest
  repeat' split
  all_goals simp only [sendSegW_bsz]

theorem outputW_bsz (w : TW) (ourIp : UInt32) (a : Bool) : (outputW w ourIp a).b.size = w.b.size := by
  by_cases hc : ((w.r.st == 2 || w.r.st == 3) && (decide (0 < w.r.pend_len - w.r.sent)
        || ((w.r.st == 3 || w.r.close_req) && !w.r.fin_sent))) = true
  · rw [outputW_data w ourIp a hc, armW_b, sendSegW_bsz]
  · have hO : outputW w ourIp a = outRest w ourIp a := by
      simp only [outputW, hc, Bool.false_eq_true, if_false]
    rw [hO]; exact outRest_bsz w ourIp a

theorem rexmitW_bsz (w : TW) (ourIp : UInt32) : (rexmitW w ourIp).b.size = w.b.size := by
  unfold rexmitW; split <;> simp only [sendSegW_bsz]

theorem segTailW_bsz (w : TW) (ourIp : UInt32) : (segTailW w ourIp).b.size = w.b.size := by
  by_cases hc : ((decide (0 < w.sg.dlen) || (w.sg.flags &&& 1 != 0))
      && decide (2147483648 ≤ w.r.rcv_nxt - w.sg.seq)) = true
  · rw [segTailW_oo w ourIp hc]; simp only [dropW_b, sendSegW_bsz]
  · rw [segTailW_in w ourIp hc, outputW_bsz, (segFinW_keep _ _ _ _).2.2.2, segDataW_b]

theorem segNaW_bsz (w : TW) (ourIp : UInt32) : (segNaW w ourIp).b.size = w.b.size := by
  unfold segNaW
  repeat' split
  all_goals simp only [dropW_b, sendSegW_bsz]

theorem segAccW_bsz (w : TW) (ourIp : UInt32) : (segAccW w ourIp).b.size = w.b.size := by
  cases h : segAckW w ourIp with
  | error w' =>
    have hb := segAckW_err_bsz w ourIp w' h
    simp only [segAccW, h]
    repeat' split
    all_goals simp only [dropW_b, noteW_b, emitW_bsz, hb]
  | ok w1 =>
    have hb := segAckW_ok_b w ourIp w1 h
    simp only [segAccW, h]
    repeat' split
    all_goals simp only [dropW_b, noteW_b, emitW_bsz, segTailW_bsz, hb]

theorem segW_bsz (w : TW) (ourIp : UInt32) : (segW w ourIp).b.size = w.b.size := by
  have h1 : ∀ w' : TW, (segConnW w' ourIp).b.size = w'.b.size := by
    intro w'; unfold segConnW; split
    · exact segAccW_bsz ..
    · exact segNaW_bsz ..
  unfold segW
  repeat' split
  all_goals simp only [dropW_b, resetW_bsz, listenW_bsz, h1]

theorem tcpInputW_bsz (w : TW) (ourIp src dst : UInt32) (n : UInt16) :
    (tcpInputW w ourIp src dst n).b.size = w.b.size := by
  unfold tcpInputW
  repeat' split
  all_goals simp only [dropW_b, segW_bsz, parseMssW, tcpParse]

theorem tickRtW_bsz (w : TW) (ourIp : UInt32) : (tickRtW w ourIp).b.size = w.b.size := by
  rw [tickRtW_eq]
  repeat' split
  all_goals simp only [dropW_b, emitW_bsz, rexmitW_bsz]

theorem tickW_bsz (w : TW) (ourIp : UInt32) : (tickW w ourIp).b.size = w.b.size := by
  unfold tickW
  repeat' split
  all_goals simp only [dropW_b, outputW_bsz, tickRtW_bsz]

/-- The data stage keeps the relation to some control block of the Spec. -/
theorem segData_rel (w : TW) (T : Spec.Tcp.Tcb) (S : Spec.Tcp.Seg) (t : TcbRel w.r w.pd T)
    (hs : SegRel w.sg w.b S) (hb : w.b.size < 65536) :
    (∃ T', TcbRel (segDataW w).1.r (segDataW w).1.pd T') ∧ (segDataW w).1.b = w.b := by
  by_cases hc : 0 < w.sg.dlen ∧ (w.r.st == 2 || (w.r.st == 5 || w.r.st == 6)) = true
  · rw [segDataW_take w hc.1 hc.2]
    exact ⟨⟨_, data_rel w T S t hs hb⟩, dW_b w⟩
  · rw [segDataW_none w hc]; exact ⟨⟨T, t⟩, rfl⟩

/-- A state related to the Spec's, with a parsed segment in a packet
buffer of at least 296 bytes, is fit for the tail of `tcp_segment`. -/
theorem segTailOk_of (w : TW) (T : Spec.Tcp.Tcb) (S : Spec.Tcp.Seg) (t : TcbRel w.r w.pd T)
    (hs : SegRel w.sg w.b S) (hb296 : 296 ≤ w.b.size) (hb : w.b.size < 65536) : SegTailOk w := by
  obtain ⟨⟨T', t'⟩, eb⟩ := segData_rel w T S t hs hb
  obtain ⟨k1, k2, k3, k4⟩ := segFinW_keep (segDataW w).1 (w.sg.flags &&& 1 != 0) (segDataW w).2.2 (segDataW w).2.1
  obtain ⟨r1, r2, r3, r4⟩ := t'.raw
  refine ⟨⟨by omega, hb, t.pdsz⟩, t.raw.2.2.1, hs.fits, ⟨by rw [k4, eb]; omega, by rw [k4, eb]; exact hb,
    by rw [k3]; exact t'.pdsz⟩, ?_, ?_⟩
  · rw [k1, k2, k4, eb, r4]; omega
  · rw [k1, k2, r4]; omega

/-- After an ACK that lets the segment go on, the state is still related
to the Spec's and the segment is where it was. -/
theorem segAck_ok_rel (ourIp : UInt32) (w : TW) (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16)
    (h : Sim ourIp w c ev0 id0) (hd : c.diag.toList.filter keep = []) (S : Spec.Tcp.Seg)
    (hs : SegRel w.sg w.b S) (w1 : TW) (hok : segAckW w ourIp = .ok w1) :
    (∃ T1, TcbRel w1.r w1.pd T1) ∧ w1.sg = w.sg ∧ w1.b = w.b := by
  have t := h.tcb
  rw [segAckW] at hok
  by_cases s1 : (w.r.st == 1) = true
  · rw [if_pos s1] at hok
    by_cases bad : (w.sg.ack != w.r.snd_nxt) = true
    · rw [if_pos bad] at hok; cases hok
    · rw [if_neg bad] at hok
      cases hok
      exact ⟨⟨{ c.tcb with st := .established, sndUna := S.ack, rtTimer := 0, retries := 0 },
        ⟨rfl, t.rip, t.rport, hs.ack, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our, t.lw, rfl, rfl, t.tw,
          t.idle, t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩⟩, rfl, rfl⟩
  · rw [if_neg s1] at hok
    by_cases ok : (ackW w ourIp).1 = true
    · rw [if_pos ok] at hok
      cases hok
      have hsim : Sim ourIp (ackW w ourIp).2 ((Spec.Tcp.ackInput S).run c).2 ev0 id0 :=
        ack_wp ourIp w c ev0 id0 h hd S hs (fun _ c' => Sim ourIp (ackW w ourIp).2 c' ev0 id0) (fun _ x _ => x)
      exact ⟨⟨_, hsim.tcb⟩, ackW_keep w ourIp ok⟩
    · rw [if_neg ok] at hok; cases hok

/-- What `tcp_input` leaves in `sg` describes the bytes of the segment,
whatever its checksum. -/
theorem parsed_rel (w : TW) (src : UInt32) (n : UInt16) (hn : 20 + n.toNat ≤ w.b.size) (h20 : 20 ≤ n.toNat)
    (ho20 : 20 ≤ (tcpDoff w.b).toNat) (ho : (tcpDoff w.b).toNat ≤ n.toNat) :
    SegRel (parseMssW (tcpParse w src n) (tcpDoff w.b)).sg w.b
      { sport := Bytes.get16 (w.b.extract 20 (20 + n.toNat)) 0,
        dport := Bytes.get16 (w.b.extract 20 (20 + n.toNat)) 2,
        seq := Bytes.get32 (w.b.extract 20 (20 + n.toNat)) 4,
        ack := Bytes.get32 (w.b.extract 20 (20 + n.toNat)) 8,
        flags := Bytes.get (w.b.extract 20 (20 + n.toNat)) 13 &&& 0x3F,
        wnd := Bytes.get16 (w.b.extract 20 (20 + n.toNat)) 14,
        mss := Spec.Tcp.parseMss (w.b.extract 20 (20 + n.toNat)) (tcpDoff w.b).toNat,
        data := Bytes.slice (w.b.extract 20 (20 + n.toNat)) (tcpDoff w.b).toNat
          (n.toNat - (tcpDoff w.b).toNat) } := by
  have z20 : (20 : UInt16).toNat = 20 := rfl
  have hD := tcpDoff_toNat w.b
  have bn := n.toNat_lt
  have ho60 : (tcpDoff w.b).toNat ≤ 60 := by
    have := (Bytes.get w.b 32).toNat_lt
    rw [hD, UInt8.toNat_shiftRight]
    show (Bytes.get w.b 32).toNat >>> 4 * 4 ≤ 60
    rw [Nat.shiftRight_eq_div_pow]; omega
  have e1 : (20 + tcpDoff w.b).toNat = 20 + (tcpDoff w.b).toNat := by rw [UInt16.toNat_add, z20]; omega
  have e2 : (n - tcpDoff w.b).toNat = n.toNat - (tcpDoff w.b).toNat := by rw [UInt16.toNat_sub]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (get16_extract w.b 20 _ 0 (by omega) hn).symm
  · exact (get16_extract w.b 20 _ 2 (by omega) hn).symm
  · exact (get32_extract w.b 20 _ 4 (by omega) hn).symm
  · exact (get32_extract w.b 20 _ 8 (by omega) hn).symm
  · show Bytes.get w.b 33 &&& 63 = Bytes.get (w.b.extract 20 (20 + n.toNat)) 13 &&& 0x3F
    rw [get_extract _ 20 _ 13 (by omega) hn]
  · exact mss_rel w.b n.toNat (tcpDoff w.b) hn ho ho20 ho60
  · show Bytes.slice _ _ _ = w.b.extract (20 + tcpDoff w.b).toNat ((20 + tcpDoff w.b).toNat + (n - tcpDoff w.b).toNat)
    rw [e1, e2]
    exact extract_extract w.b 20 _ _ _ (by omega) hn
  · show (20 + tcpDoff w.b).toNat + (n - tcpDoff w.b).toNat ≤ w.b.size
    rw [e1, e2]; omega

/-- **`tcp_input`, the code, against the Spec.**  From a state that
agrees with the Spec's, with the segment `buf[20, 20+n)` in a packet
buffer of at least 296 bytes: the call does not trap; if `Spec.Tcp.parse`
rejects the segment the call drops it with the Spec's reason and changes
nothing else; otherwise it ends in a state that agrees with the one
`Spec.Tcp.input` ends in, having transmitted the Spec's segments and
dropped where the Spec drops. -/
theorem tcp_input_refines (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16) (h : Sim ourIp w c ev0 id0)
    (hd : c.diag.toList.filter keep = []) (src dst : UInt32) (n : UInt16) (hn : 20 + n.toNat ≤ w.b.size)
    (hb296 : 296 ≤ w.b.size) (hb : w.b.size < 65536) (d : Nat) :
    ∃ w', Sem.call (d + n.toNat + 3100) p (tcpSt st w) "tcp_input" [u32 src, u32 dst, u16 n]
        = .ok none (tcpSt st w') ∧ w'.b.size = w.b.size ∧
      (∀ r, Spec.Tcp.parse src dst (w.b.extract 20 (20 + n.toNat)) = .error r → w' = dropW w r) ∧
      (∀ S, Spec.Tcp.parse src dst (w.b.extract 20 (20 + n.toNat)) = .ok S →
        Sim ourIp w' ((Spec.Tcp.input src S).run c).2 ev0 id0) := by
  have t := h.tcb
  obtain ⟨r1, r2, _, _⟩ := t.raw
  refine ⟨tcpInputW w ourIp src dst n, ?_, tcpInputW_bsz w ourIp src dst n,
    tcp_input_sim ourIp w c ev0 id0 h hd src dst n hn hb⟩
  refine tcp_input_tw p hP hR st hB hK ourIp hip w ⟨by omega, hb, t.pdsz⟩ src dst n hn r1 r2 ?_ d
  intro h20 ho20 ho w1 hok
  have hs := parsed_rel w src n hn h20 ho20 ho
  have h0 : Sim ourIp
      { (parseMssW (tcpParse w src n) (tcpDoff w.b)) with
        r := { (parseMssW (tcpParse w src n) (tcpDoff w.b)).r with idle := 0 } }
      { c with tcb := { c.tcb with idle := 0 } } ev0 id0 :=
    ⟨⟨t.st, t.rip, t.rport, t.una, t.nxt, t.rcv, t.plen, t.sent, t.fin, t.peer, t.our, t.lw, t.rt, t.re, t.tw, rfl,
      t.cr, t.pend, t.pdsz, t.hsent, t.hcap, t.hour⟩, h.iss, h.ip, h.id, h.evs, h.mss⟩
  obtain ⟨⟨T1, t1⟩, e1, e2⟩ := segAck_ok_rel ourIp _ _ ev0 id0 h0 hd _ hs w1 hok
  exact segTailOk_of w1 T1 _ t1 (by rw [e1, e2]; exact hs) (by rw [e2]; exact hb296) (by rw [e2]; exact hb)

/-- **`tcp_tick`, the code, against the Spec**: the call does not trap
and ends in a state that agrees with the one `Spec.Tcp.tick` ends in,
with the Spec's transmissions and drops. -/
theorem tcp_tick_refines (p : Prog) (hP : TcpAll p) (hR : TcpReasons p) (st : St) (hB : TcpBase st)
    (hK : TcpConsts st) (ourIp : UInt32) (hip : st.globals.lookup "OUR_IP" = some (u32 ourIp)) (w : TW)
    (c : Spec.Tcp.Ctx) (ev0 : List Trace.Event) (id0 : UInt16) (h : Sim ourIp w c ev0 id0)
    (hd : c.diag.toList.filter keep = []) (hI : Spec.Tcp.Inv c.tcb) (hidle : c.tcb.idle < 255)
    (hretr : c.tcb.retries < 255) (hb296 : 296 ≤ w.b.size) (hb : w.b.size < 65536) (d : Nat) :
    ∃ w', Sem.call (d + 2000) p (tcpSt st w) "tcp_tick" [] = .ok none (tcpSt st w') ∧ w'.b.size = w.b.size ∧
      Sim ourIp w' (Spec.Tcp.tick.run c).2 ev0 id0 := by
  have t := h.tcb
  obtain ⟨r1, r2, _, r4⟩ := t.raw
  exact ⟨tickW w ourIp,
    tcp_tick_tw p hP hR st hB hK ourIp hip w ⟨by omega, hb, t.pdsz⟩ (by omega) (by omega) (by rw [r4]; omega)
      (by rw [r4]; omega) d,
    tickW_bsz w ourIp, tcp_tick_sim ourIp w c ev0 id0 h hd hI hidle hretr⟩

/-! ## Axioms -/

/-- info: 'Ember.Proof.Refine.tcp_input_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcp_input_refines

/-- info: 'Ember.Proof.Refine.tcp_tick_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcp_tick_refines

/-- info: 'Ember.Proof.Refine.tcp_input_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcp_input_sim

/-- info: 'Ember.Proof.Refine.tcp_tick_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcp_tick_sim

end Ember.Proof.Refine
