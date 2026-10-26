import Ember.Proof.Z80Cmp

/-!
# Ember.Proof.Z80Jump — jumps to labels of the image (plan M7.3)

A label resolves to the address of its item (`label_at`), so a jump
leaves the CPU at that item (`jp_step`, `jp_cc_step`, `jr_cc_step`) —
or, a condition failing, at the item after the jump.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area Bin Cmp)

section
variable {Z : ZCtx}

/-- A label is where its item is. -/
theorem label_at (ok : Z.OK) {j : Nat} {l : String} (hj : Z.items[j]? = some (.label l)) {s : Cpu}
    (R : Img Z.a 0 s) : ∃ T, Z.addrs[j]? = some T ∧ Z.sym l T ∧ T < 65536 := by
  obtain ⟨ad, bs, h1, _, _, _, _, hb, h6⟩ := ok.placed.2 j _ hj
  exact ⟨ad, h1, h6 l rfl, by have := R.rom; have := s.ramStart.toNat_lt; omega⟩

theorem encode_run {i : Instr} {env : Env} {bs : List UInt8} (h : encode i env = .ok bs) :
    (encode' i).run env = .ok bs := by
  unfold encode at h
  split at h
  · rename_i bs' hb
    cases h
    exact hb
  · cases h

theorem jp_len {env : Env} {v : Val} {bs : List UInt8} (h : encode ⟨.jp, [.imm v]⟩ env = .ok bs) :
    bs.length = 3 := by
  have he' : ((imm16 v).run env).bind (fun l => .ok ([0xC3] ++ l)) = Except.ok bs := encode_run h
  obtain ⟨l, hl, hb⟩ := bind_ok he'
  obtain rfl := imm16_bytes hl
  cases hb
  rfl

theorem jp_cc_len {env : Env} (op : Cmp) {v : Val} {bs : List UInt8}
    (h : encode ⟨.jp, [condOf op, .imm v]⟩ env = .ok bs) : bs.length = 3 := by
  have h' := encode_run h
  cases op <;>
    (have he' : ((imm16 v).run env).bind _ = Except.ok bs := h'
     obtain ⟨l, hl, hb⟩ := bind_ok he'
     obtain rfl := imm16_bytes hl
     cases hb
     rfl)

/-- The state after a jump: `pc` set, nothing else of note changed. -/
def jpTo (nn : UInt16) (s : Cpu) : Cpu := ({ (skip (op1 s) 2) with pc := nn } : Cpu).tick 10

theorem jpTo_sys (nn : UInt16) (s : Cpu) : Sys s (jpTo nn s) := by simp only [Sys, jpTo, zsim, and_self]
theorem jpTo_keep (nn : UInt16) (s : Cpu) : KeepR s (jpTo nn s) := by simp only [KeepR, jpTo, zsim, and_self]

/-- **An unconditional jump to a label.** -/
theorem jp_step (ok : Z.OK) {k j : Nat} {l : String} (hk : Z.items[k]? = some (.ins ⟨.jp, [.imm (.sym l)]⟩))
    (hj : Z.items[j]? = some (.label l)) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ At Z.addrs j s' ∧ Mach Z s' ∧ Sys s s' ∧ KeepR s s' := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨T, hT, hsym, hTlt⟩ := label_at ok hj M.1
  have hnn : (Instr.immW (Z.a.env ad) ⟨.jp, [.imm (.sym l)]⟩).toNat = T :=
    immW_toNat _ _ _ _ rfl (sym_val ad hsym) hTlt
  have hst := fun inp => (step_item ok.placed M.1 hk had hpc M.2 (inp := inp)
    (s' := jpTo (Instr.immW (Z.a.env ad) ⟨.jp, [.imm (.sym l)]⟩) s) rfl).1
  refine ⟨_, Steps.one hst (by simp only [jpTo, zsim]), ⟨T, hT, ?_⟩, M.sys (jpTo_sys _ _), jpTo_sys _ _, jpTo_keep _ _⟩
  simp only [jpTo, zsim]
  exact hnn

/-- The state after `jp cc,nn`. -/
def jpCC (c : UInt8) (nn : UInt16) (s : Cpu) : Cpu :=
  (if (op1 s).cond c then ({ (skip (op1 s) 2) with pc := nn } : Cpu) else skip (op1 s) 2).tick 10

theorem cond_op1 (s : Cpu) (c : UInt8) : (op1 s).cond c = s.cond c := rfl

theorem jpCC_io (c : UInt8) (nn : UInt16) (s : Cpu) : (jpCC c nn s).io = .none := by
  unfold jpCC
  split <;> simp only [zsim]

theorem jpCC_sys (c : UInt8) (nn : UInt16) (s : Cpu) : Sys s (jpCC c nn s) := by
  unfold jpCC
  split <;> simp only [Sys, zsim, and_self]

theorem jpCC_keep (c : UInt8) (nn : UInt16) (s : Cpu) : KeepR s (jpCC c nn s) := by
  unfold jpCC
  split <;> simp only [KeepR, zsim, and_self]

theorem exec_jp_cc (env : Env) (op : Cmp) (v : Val) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env ⟨.jp, [condOf op, .imm v]⟩ s inp =
      some (jpCC (ccOf op) (Instr.immW env ⟨.jp, [condOf op, .imm v]⟩) s) := by
  cases op <;> rfl

theorem immVal_jp_cc (op : Cmp) (v : Val) : (⟨.jp, [condOf op, .imm v]⟩ : Instr).immVal? = some v := by
  cases op <;> rfl

/-- **A conditional jump to a label**: there when the condition holds, at the next item when not. -/
theorem jp_cc_step (ok : Z.OK) {k j : Nat} (op : Cmp) {l : String}
    (hk : Z.items[k]? = some (.ins ⟨.jp, [condOf op, .imm (.sym l)]⟩))
    (hj : Z.items[j]? = some (.label l)) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ Mach Z s' ∧ Sys s s' ∧ KeepR s s' ∧
      (if s.cond (ccOf op) then At Z.addrs j s' else At Z.addrs (k + 1) s') := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨T, hT, hsym, hTlt⟩ := label_at ok hj M.1
  have hnn : (Instr.immW (Z.a.env ad) ⟨.jp, [condOf op, .imm (.sym l)]⟩).toNat = T :=
    immW_toNat _ _ _ _ (immVal_jp_cc op _) (sym_val ad hsym) hTlt
  have hst := fun inp => (step_item ok.placed M.1 hk had hpc M.2 (inp := inp) (exec_jp_cc _ op _ s _)).1
  refine ⟨_, Steps.one hst (jpCC_io _ _ _), M.sys (jpCC_sys _ _ _), jpCC_sys _ _ _, jpCC_keep _ _ _, ?_⟩
  by_cases hc : s.cond (ccOf op) = true
  · rw [if_pos hc]
    refine ⟨T, hT, ?_⟩
    simp only [jpCC, cond_op1, hc, if_true, zsim]
    exact hnn
  · rw [if_neg hc]
    obtain ⟨bs, hbs, hnext, hlt⟩ := ok.placed.next M.1 hk had
    have hlen := jp_cc_len op hbs
    refine ⟨ad + bs.length, hnext, ?_⟩
    have hlt' := hlt (by intro e; rw [e] at hlen; cases hlen)
    simp only [jpCC, cond_op1, hc, Bool.false_eq_true, if_false, zsim]
    rw [UInt16.toNat_add, UInt16.toNat_add, hpc, hlen]
    show ((ad + 1) % 65536 + 2) % 65536 = _
    omega

/-! ## Relative jumps -/

/-- A relative jump the assembler accepted is in range. -/
theorem rel_range {env : Env} {v : Val} {l : List UInt8} (h : (rel v).run env = .ok l) (hs : env.sizing = false) :
    -128 ≤ env.val v - (env.pc + 2) ∧ env.val v - (env.pc + 2) ≤ 127 := by
  simp only [Env.val]
  simp only [rel, ReaderT.run, bind, ReaderT.bind, Except.bind] at h ⊢
  cases hv : value v env with
  | error e => simp [hv] at h
  | ok n =>
    simp only [hv] at h ⊢
    have hr : (read : Enc Env) env = Except.ok env := rfl
    simp only [hr] at h
    split at h
    · cases h
    · rename_i hc
      simp only [hs, Bool.not_false, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt] at hc
      omega

/-- A displacement, sign-extended as the CPU does. -/
theorem sext_val (d : Int) (h1 : -128 ≤ d) (h2 : d ≤ 127) : ((sext (byteOf d)).toNat : Int) = d % 65536 := by
  have hb := byteOf_toNat d
  by_cases hd : 0 ≤ d
  · have hlt : byteOf d < 0x80 := by
      rw [UInt8.lt_iff_toNat_lt, hb]
      show (d % 256).toNat < 128
      omega
    simp only [sext, hlt, if_true, UInt8.toNat_toUInt16, hb]
    omega
  · have hge : ¬ byteOf d < 0x80 := by
      rw [UInt8.lt_iff_toNat_lt, hb]
      show ¬ (d % 256).toNat < 128
      omega
    simp only [sext, hge, if_false, UInt16.toNat_or, UInt8.toNat_toUInt16, hb]
    have hx : (d % 256).toNat < 2 ^ 8 := by omega
    have : (d % 256).toNat ||| (0xFF00 : UInt16).toNat = 0xFF <<< 8 + (d % 256).toNat := by
      rw [Nat.shiftLeft_add_eq_or_of_lt hx, Nat.or_comm]
      rfl
    rw [this]
    show (((255 <<< 8 + (d % 256).toNat : Nat)) : Int) = _
    have e : (255 <<< 8 : Nat) = 65280 := rfl
    rw [e]
    omega

/-- The state after `jr cc,e`. -/
def jrCC (c : UInt8) (n : UInt8) (s : Cpu) : Cpu :=
  if (op1 s).cond c then ({ (skip (op1 s) 1) with pc := (skip (op1 s) 1).pc + sext n } : Cpu).tick 12
  else (skip (op1 s) 1).tick 7

theorem jrCC_io (c n : UInt8) (s : Cpu) : (jrCC c n s).io = .none := by
  unfold jrCC
  split <;> simp only [zsim]

theorem jrCC_sys (c n : UInt8) (s : Cpu) : Sys s (jrCC c n s) := by
  unfold jrCC
  split <;> simp only [Sys, zsim, and_self]

theorem jrCC_keep (c n : UInt8) (s : Cpu) : KeepR s (jrCC c n s) := by
  unfold jrCC
  split <;> simp only [KeepR, zsim, and_self]

/-- **`jr nz` or `jr z` to a label.** -/
theorem jr_cc_step (ok : Z.OK) {k j : Nat} (z : Bool) {l : String}
    (hk : Z.items[k]? = some (.ins ⟨.jr, [if z then .z else .nz, .imm (.sym l)]⟩))
    (hj : Z.items[j]? = some (.label l)) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ Mach Z s' ∧ Sys s s' ∧ KeepR s s' ∧
      (if s.flag FZ = z then At Z.addrs j s' else At Z.addrs (k + 1) s') := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨T, hT, hsym, hTlt⟩ := label_at ok hj M.1
  obtain ⟨bs, hbs, hnext, hlt⟩ := ok.placed.next M.1 hk had
  -- the displacement
  have hval : (Z.a.env ad).val (.sym l) = Int.ofNat T := sym_val ad hsym
  have henc : ∃ lst, (rel (.sym l)).run (Z.a.env ad) = .ok lst ∧ bs.length = 2 := by
    have h' := encode_run hbs
    cases z <;>
      (have he' : ((rel (.sym l)).run (Z.a.env ad)).bind _ = Except.ok bs := h'
       obtain ⟨lst, hl, hb⟩ := bind_ok he'
       have := rel_bytes hl
       subst this
       cases hb
       exact ⟨_, hl, rfl⟩)
  obtain ⟨lst, hrel, hlen⟩ := henc
  obtain ⟨r1, r2⟩ := rel_range hrel rfl
  rw [hval] at r1 r2
  have hpcv : (Z.a.env ad).pc = Int.ofNat ad := rfl
  rw [hpcv] at r1 r2
  have hlt' := hlt (by intro e; rw [e] at hlen; cases hlen)
  have hexec : ∀ inp, exec (Z.a.env ad) ⟨.jr, [if z then .z else .nz, .imm (.sym l)]⟩ s inp =
      some (jrCC (if z then 1 else 0) (byteOf (Int.ofNat T - (Int.ofNat ad + 2))) s) := by
    intro inp
    cases z
    · show _ = some (jrCC 0 _ s)
      have : Instr.immB (Z.a.env ad) ⟨.jr, [.nz, .imm (.sym l)]⟩ = byteOf (Int.ofNat T - (Int.ofNat ad + 2)) := by
        show byteOf ((Z.a.env ad).val (.sym l) - ((Z.a.env ad).pc + 2)) = _
        rw [hval]
        rfl
      rw [← this]
      rfl
    · show _ = some (jrCC 1 _ s)
      have : Instr.immB (Z.a.env ad) ⟨.jr, [.z, .imm (.sym l)]⟩ = byteOf (Int.ofNat T - (Int.ofNat ad + 2)) := by
        show byteOf ((Z.a.env ad).val (.sym l) - ((Z.a.env ad).pc + 2)) = _
        rw [hval]
        rfl
      rw [← this]
      rfl
  have hst := fun inp => (step_item ok.placed M.1 hk had hpc M.2 (inp := inp) (hexec inp)).1
  refine ⟨_, Steps.one hst (jrCC_io _ _ _), M.sys (jrCC_sys _ _ _), jrCC_sys _ _ _, jrCC_keep _ _ _, ?_⟩
  have hcond : s.cond (if z then 1 else 0) = decide (s.flag FZ = z) := by
    cases z
    · show (!s.flag FZ) = _
      cases s.flag FZ <;> rfl
    · show s.flag FZ = _
      cases s.flag FZ <;> rfl
  by_cases hc : s.flag FZ = z
  · rw [if_pos hc]
    refine ⟨T, hT, ?_⟩
    have hc' : (op1 s).cond (if z then 1 else 0) = true := by rw [cond_op1, hcond]; simpa using hc
    simp only [jrCC, hc', if_true, zsim]
    have hs := sext_val (Int.ofNat T - (Int.ofNat ad + 2)) r1 r2
    rw [UInt16.toNat_add, UInt16.toNat_add, UInt16.toNat_add, hpc]
    show (((ad + 1) % 65536 + 1) % 65536 + (sext _).toNat) % 65536 = T
    rw [hlen] at hlt'
    generalize (sext (byteOf (Int.ofNat T - (Int.ofNat ad + 2)))).toNat = sx at hs ⊢
    simp only [Int.ofNat_eq_coe] at hs r1 r2
    omega
  · rw [if_neg hc]
    refine ⟨ad + bs.length, hnext, ?_⟩
    have hc' : (op1 s).cond (if z then 1 else 0) = false := by rw [cond_op1, hcond]; simpa using hc
    simp only [jrCC, hc', Bool.false_eq_true, if_false, zsim]
    rw [UInt16.toNat_add, UInt16.toNat_add, hpc, hlen]
    show ((ad + 1) % 65536 + 1) % 65536 = _
    rw [hlen] at hlt'
    omega

end

end Ember.Proof.Z80Gen
