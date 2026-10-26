import Ember.Proof.Z80Note

/-!
# Ember.Proof.Z80Wide — the runtime's routines on the accumulator, from their items (plan M7.3)

`rt_ld32` and `rt_st32` are an `ldir` of four bytes to and from the
accumulator.  `ldir_copy`: `ldir` copies `BC` bytes from `HL` to `DE`
when no byte it reads is one it writes.  The routines are right where
the bytes at `HL` are apart from the accumulator and the stack
(`HLApart`), which is how `RtW` takes them.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

section
variable {Z : ZCtx}

/-- One round of `ldir`: the byte at `HL` to `DE` (in RAM). -/
theorem ldir_round_g (ok : Z.OK) {k : Nat} (hk : Z.items[k]? = some (.ins ⟨.ldir, []⟩)) {s : Cpu} {h d m : Nat}
    (M : Mach Z s) (hat : At Z.addrs k s) (hrs : s.ramStart.toNat = Z.ramStart) (hhl : s.hl.toNat = h)
    (hde : s.de.toNat = d) (hbc : s.bc.toNat = m + 1) (hram : Z.ramStart ≤ d) :
    ∃ s1, Steps s s1 ∧ Mach Z s1 ∧ s1.sp = s.sp ∧ s1.ramStart = s.ramStart ∧
      s1.mem = s.mem.set! d (s.mem.get! h) ∧ s1.hl.toNat = (h + 1) % 65536 ∧ s1.de.toNat = (d + 1) % 65536 ∧
      s1.bc.toNat = m ∧ (if m = 0 then At Z.addrs (k + 1) s1 else At Z.addrs k s1) := by
  obtain ⟨ad, had, hpc⟩ := hat
  have ehl : (op2 s).hl = s.hl := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  have ede : (op2 s).de = s.de := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  have ebc : (op2 s).bc = s.bc := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  obtain ⟨hmem, hhl1, hde1, hbc1, hsp1, hh1, hrs1, hio1, hpc1⟩ := ldirOnce_spec (op2 s)
  simp only [ehl, ede, ebc] at hmem hhl1 hde1 hbc1 hpc1
  have hst := fun inp => (step_item ok.placed M.1 hk had hpc M.2 (inp := inp) (ldir_exec _ s inp)).1
  have hmem' : (ldirOnce (op2 s)).mem = s.mem.set! d (s.mem.get! h) := by
    rw [hmem, cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hrs, hde]; omega)]
    simp only [zsim, Cpu.rd, hde, hhl]
  have hbcv : (s.bc - 1).toNat = m := by rw [sub1_toNat _ (by omega), hbc]; rfl
  have M1 : Mach Z (ldirOnce (op2 s)) := by
    refine ⟨⟨by rw [hrs1]; exact M.1.rom, fun x b hx => ?_⟩, by rw [hh1]; exact M.2⟩
    have hlt : x < Z.a.bytes.size := by
      rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hx; cases hx
    have hrom := M.1.rom
    have hb' := M.1.bytes x b hx
    rw [Nat.zero_add] at hb' ⊢
    rw [hmem', getBang_set _ _ _ _ (by omega)]
    exact hb'
  refine ⟨_, Steps.one hst (by rw [hio1]; simp only [zsim]), M1, by rw [hsp1]; simp only [zsim],
    by rw [hrs1]; simp only [zsim], hmem', ?_, ?_, by rw [hbc1]; exact hbcv, ?_⟩
  · rw [hhl1, UInt16.toNat_add, hhl]
    rfl
  · rw [hde1, UInt16.toNat_add, hde]
    rfl
  · by_cases hm : m = 0
    · rw [if_pos hm]
      have hz : (s.bc - 1 != 0) = false := by
        have : s.bc - 1 = 0 := UInt16.toNat_inj.mp (by rw [hbcv, hm]; rfl)
        rw [this]
        rfl
      rw [hz] at hpc1
      simp only [Bool.false_eq_true, if_false] at hpc1
      obtain ⟨bs, hbs, hnext, hlt65⟩ := ok.placed.next M.1 hk had
      have hbs' : bs = [0xED, 0xB0] := by
        have : Item.encode (.ins ⟨.ldir, []⟩) (Z.a.env ad) = .ok [0xED, 0xB0] := rfl
        rw [this] at hbs
        exact (Except.ok.inj hbs).symm
      have hb2 := hlt65 (by rw [hbs']; exact List.cons_ne_nil _ _)
      rw [hbs'] at hb2 hnext
      have hb2' : ad + 2 < 65536 := hb2
      refine ⟨ad + 2, hnext, ?_⟩
      rw [hpc1]
      show (s.pc + 1 + 1).toNat = _
      rw [UInt16.toNat_add, UInt16.toNat_add, hpc]
      show ((ad + 1) % 65536 + 1) % 65536 = _
      omega
    · rw [if_neg hm]
      have hz : (s.bc - 1 != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro e
        have := congrArg UInt16.toNat e
        rw [hbcv] at this
        exact hm this
      rw [hz] at hpc1
      simp only [if_true] at hpc1
      refine ⟨ad, had, ?_⟩
      rw [hpc1]
      show (s.pc + 1 + 1 - 2).toNat = _
      have : s.pc + 1 + 1 - 2 = s.pc := by
        apply UInt16.toNat_inj.mp
        have := s.pc.toNat_lt
        rw [UInt16.toNat_sub, UInt16.toNat_add, UInt16.toNat_add]
        show (2 ^ 16 - 2 + ((s.pc.toNat + 1) % 65536 + 1) % 65536) % 2 ^ 16 = _
        omega
      rw [this, hpc]

/-- Four bytes, one by one. -/
theorem rd4 (m : ByteArray) (a : Nat) (h : a + 4 ≤ 65536) :
    IR.Sem.rd m a 4 = (m.get! (a + 0)).toNat + 256 * ((m.get! (a + 1)).toNat +
      256 * ((m.get! (a + 2)).toNat + 256 * ((m.get! (a + 3)).toNat + 256 * 0))) := by
  simp only [IR.Sem.rd]
  rw [Nat.mod_eq_of_lt (show a < 65536 by omega), Nat.mod_eq_of_lt (show a + 1 < 65536 by omega),
    Nat.mod_eq_of_lt (show a + 1 + 1 < 65536 by omega), Nat.mod_eq_of_lt (show a + 1 + 1 + 1 < 65536 by omega)]
  rfl

/-- **`ldir`**: the `m + 1` bytes at `HL` are copied to `DE`, when none of them is a byte written. -/
theorem ldir_copy (ok : Z.OK) {k : Nat} (hk : Z.items[k]? = some (.ins ⟨.ldir, []⟩)) :
    ∀ (m : Nat) (s : Cpu) (h d : Nat), Mach Z s → At Z.addrs k s → s.ramStart.toNat = Z.ramStart →
      s.hl.toNat = h → s.de.toNat = d → s.bc.toNat = m + 1 → Z.ramStart ≤ d → h + m + 1 ≤ 65536 →
      d + m + 1 ≤ 65536 → s.mem.size = 65536 → (∀ j, j ≤ m → h + j < d ∨ d + m + 1 ≤ h + j) →
      ∃ s', Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
        s'.mem.size = 65536 ∧ (∀ j, j ≤ m → s'.mem.get! (d + j) = s.mem.get! (h + j)) ∧
        (∀ x, x < d ∨ d + m + 1 ≤ x → s'.mem.get! x = s.mem.get! x) := by
  intro m
  induction m with
  | zero =>
    intro s h d M hat hrs hhl hde hbc hram hbh hbd hsz hap
    obtain ⟨s1, st, M1, hsp, hr, hmem, _, _, _, hat1⟩ := ldir_round_g ok hk M hat hrs hhl hde hbc hram
    rw [if_pos rfl] at hat1
    refine ⟨s1, st, hat1, M1, hsp, hr, by rw [hmem, set_size]; exact hsz, fun j hj => ?_, fun x hx => ?_⟩
    · have : j = 0 := by omega
      rw [this, hmem]
      exact getBang_same _ _ _ (by omega)
    · rw [hmem, getBang_set _ _ _ _ (by omega)]
  | succ m ih =>
    intro s h d M hat hrs hhl hde hbc hram hbh hbd hsz hap
    obtain ⟨s1, st, M1, hsp, hr, hmem, hhl1, hde1, hbc1, hat1⟩ := ldir_round_g ok hk M hat hrs hhl hde hbc hram
    rw [if_neg (by omega)] at hat1
    obtain ⟨s', st', at', M', hsp', hr', hsz', hcp, hkeep⟩ := ih s1 (h + 1) (d + 1) M1 hat1 (by rw [hr]; exact hrs)
      (by rw [hhl1]; omega) (by rw [hde1]; omega) hbc1 (by omega) (by omega) (by omega)
      (by rw [hmem, set_size]; exact hsz) (fun j hj => by have := hap (j + 1) (by omega); omega)
    refine ⟨s', st.trans st', at', M', by rw [hsp', hsp], by rw [hr', hr], hsz', fun j hj => ?_, fun x hx => ?_⟩
    · cases j with
      | zero =>
        show s'.mem.get! d = s.mem.get! h
        rw [hkeep d (Or.inl (by omega)), hmem]
        exact getBang_same _ _ _ (by omega)
      | succ j =>
        have := hap (j + 1) hj
        rw [show d + (j + 1) = d + 1 + j by omega, hcp j (by omega), hmem, getBang_set _ _ _ _ (by omega)]
        congr 1
        omega
    · rw [hkeep x (by omega), hmem, getBang_set _ _ _ _ (by omega)]

/-- `ld bc,nn` and `ld de,nn`: the pair is the word, the other registers are kept. -/
theorem ld_bc_imm (ok : Z.OK) {k : Nat} {v : Val} (hk : Z.items[k]? = some (.ins ⟨.ld, [.bc, .imm v]⟩))
    {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s' ad, Z.addrs[k]? = some ad ∧ Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ Sys s s' ∧
      s'.bc = Instr.immW (Z.a.env ad) ⟨.ld, [.bc, .imm v]⟩ ∧ s'.hl = s.hl ∧ s'.de = s.de ∧ s'.a = s.a := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 =
      ((skip (op1 s) 2).setRp .hl 0 (Instr.immW (Z.a.env ad) ⟨.ld, [.bc, .imm v]⟩)).tick 10 := ⟨_, rfl⟩
  obtain ⟨st, at'⟩ := step_raw ok hk M ⟨ad, had, hpc⟩ c1 (fun ad' had' inp => by
    rw [had] at had'
    cases had'
    rw [hc1]
    rfl) (by rw [hc1]; simp only [Cpu.setRp, skip, zsim])
  have hS : Sys s c1 := by rw [hc1]; simp only [Sys, Cpu.setRp, skip, zsim, and_self]
  refine ⟨c1, ad, had, st, at' rfl, M.sys hS, hS, ?_, ?_, ?_, ?_⟩
  · rw [hc1]
    show mk16 _ _ = _
    simp only [Cpu.setRp, skip, zsim, mk16_hi_lo]
  · rw [hc1]
    show mk16 _ _ = mk16 _ _
    simp only [Cpu.setRp, skip, zsim]
  · rw [hc1]
    show mk16 _ _ = mk16 _ _
    simp only [Cpu.setRp, skip, zsim]
  · rw [hc1]
    simp only [Cpu.setRp, skip, zsim]

theorem ld_de_imm (ok : Z.OK) {k : Nat} {v : Val} (hk : Z.items[k]? = some (.ins ⟨.ld, [.de, .imm v]⟩))
    {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s' ad, Z.addrs[k]? = some ad ∧ Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ Sys s s' ∧
      s'.de = Instr.immW (Z.a.env ad) ⟨.ld, [.de, .imm v]⟩ ∧ s'.hl = s.hl ∧ s'.bc = s.bc ∧ s'.a = s.a ∧
      s'.b = s.b ∧ s'.f = s.f := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 =
      ((skip (op1 s) 2).setRp .hl 1 (Instr.immW (Z.a.env ad) ⟨.ld, [.de, .imm v]⟩)).tick 10 := ⟨_, rfl⟩
  obtain ⟨st, at'⟩ := step_raw ok hk M ⟨ad, had, hpc⟩ c1 (fun ad' had' inp => by
    rw [had] at had'
    cases had'
    rw [hc1]
    rfl) (by rw [hc1]; simp only [Cpu.setRp, skip, zsim])
  have hS : Sys s c1 := by rw [hc1]; simp only [Sys, Cpu.setRp, skip, zsim, and_self]
  refine ⟨c1, ad, had, st, at' rfl, M.sys hS, hS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc1]
    show mk16 _ _ = _
    simp only [Cpu.setRp, skip, zsim, mk16_hi_lo]
  · rw [hc1]
    show mk16 _ _ = mk16 _ _
    simp only [Cpu.setRp, skip, zsim]
  · rw [hc1]
    show mk16 _ _ = mk16 _ _
    simp only [Cpu.setRp, skip, zsim]
  · rw [hc1]
    simp only [Cpu.setRp, skip, zsim]
  · rw [hc1]
    simp only [Cpu.setRp, skip, zsim]
  · rw [hc1]
    simp only [Cpu.setRp, skip, zsim]

/-- The items of `rt_ld64` and `rt_ld32`. -/
def ldItems : List Item :=
  [.label "rt_ld64", .ins ⟨.ld, [.bc, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym "rt_ldw")]⟩,
   .label "rt_ld32", .ins ⟨.ld, [.bc, .imm (.num 4)]⟩,
   .label "rt_ldw", .ins ⟨.ld, [.de, .imm (.sym "rt_acc")]⟩, .ins ⟨.ldir, []⟩, .ins ⟨.ret, []⟩]

/-- **`rt_ld32`**: the accumulator's first four bytes are the four at `HL`; nothing else is written. -/
theorem rt_ld32_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat} (hhas : Has Z k ldItems) :
    RtAcc Z "rt_ld32" (HLApart Z 4) (fun s s' => IR.Sem.rd s'.mem Z.acc 4 = IR.Sem.rd s.mem s.hl.toNat 4) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 3 rfl)
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 6, _, 0, hhas.get 6 rfl, rfl⟩
  have hram := ok.accRam
  have hstk := ok.stack
  have hacs := ok.accStack
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi ⟨hb, hap⟩ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at4 : At Z.addrs (k + 4) s := at_label ok (hhas.get 3 rfl) ⟨T, hT, hpc⟩
  obtain ⟨c1, ad1, had1, st1, at5, M1, hS1, hbc1, hhl1, _, _⟩ := ld_bc_imm ok (hhas.get 4 rfl) M at4
  have at6 := at_label ok (hhas.get 5 rfl) at5
  obtain ⟨c2, ad2, had2, st2, at7, M2, hS2, hde2, hhl2, hbc2, _⟩ := ld_de_imm ok (hhas.get 6 rfl) M1 at6
  have hbcv : c2.bc.toNat = 3 + 1 := by
    rw [hbc2, hbc1]
    exact immW_toNat _ _ _ 4 rfl rfl (by decide)
  have hdev : c2.de.toNat = Z.acc := by
    rw [hde2]
    exact immW_toNat _ _ _ _ rfl (sym_val ad2 hacc) (by omega)
  have hS02 : Sys s c2 := hS1.trans hS2
  obtain ⟨c3, st3, at8, M3, hsp3, hr3, hsz3, hcp, hkeep⟩ := ldir_copy ok (hhas.get 7 rfl) 3 c2 s.hl.toNat Z.acc M2 at7
    (by rw [hS02.2.1]; exact hrs) (by rw [hhl2, hhl1]) hdev hbcv hram.1 (by omega) (by omega)
    (by rw [hS02.1]; exact hmsz) (fun j hj => by have := (hap j (by omega)).1; omega)
  obtain ⟨c', st4, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 8 rfl) M3 at8
  rw [hS02.1] at hcp hkeep
  refine ⟨c', ((st1.trans st2).trans st3).trans st4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc', hsp3, hS02.2.2.2]
    apply UInt16.toNat_inj.mp
    rw [cpu_rd16 _ _ (by omega), cpu_rd16 _ _ (by omega)]
    exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hkeep x (by omega))
  · rw [hsp', hsp3, hS02.2.2.2]
  · rw [hh']
    exact M3.2
  · rw [hrs', hr3, hS02.2.1]
  · rw [hmem']
    exact hsz3
  · show IR.Sem.rd c'.mem Z.acc 4 = IR.Sem.rd s.mem s.hl.toNat 4
    rw [hmem']
    have e1 : IR.Sem.rd c3.mem Z.acc 4 = (c3.mem.get! (Z.acc + 0)).toNat + 256 * ((c3.mem.get! (Z.acc + 1)).toNat +
        256 * ((c3.mem.get! (Z.acc + 2)).toNat + 256 * ((c3.mem.get! (Z.acc + 3)).toNat + 256 * 0))) := rd4 _ _ (by omega)
    have e2 := rd4 s.mem s.hl.toNat hb
    rw [e1, e2, hcp 0 (by omega), hcp 1 (by omega), hcp 2 (by omega), hcp 3 (by omega)]
  · intro x _ _ hx
    rw [hmem']
    exact hkeep x (by omega)

theorem does_ex_de_hl : Does ⟨.ex, [.de, .hl]⟩ exDEHL :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, exDEHL, zsim, and_self], fun s => by simp only [exDEHL, zsim]⟩

theorem exDEHL_de (s : Cpu) : (exDEHL s).de = s.hl := by
  show mk16 _ _ = mk16 _ _
  simp only [exDEHL, zsim]
theorem exDEHL_bc (s : Cpu) : (exDEHL s).bc = s.bc := by
  show mk16 _ _ = mk16 _ _
  simp only [exDEHL, zsim]

/-- `ld hl,nn`: `HL` is the word, the other registers are kept. -/
theorem ld_hl_imm (ok : Z.OK) {k : Nat} {v : Val} (hk : Z.items[k]? = some (.ins ⟨.ld, [.hl, .imm v]⟩))
    {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s' ad, Z.addrs[k]? = some ad ∧ Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ Sys s s' ∧
      s'.hl = Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm v]⟩ ∧ s'.de = s.de ∧ s'.bc = s.bc ∧ s'.a = s.a := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 =
      ((skip (op1 s) 2).setHL (Instr.immW (Z.a.env ad) ⟨.ld, [.hl, .imm v]⟩)).tick 10 := ⟨_, rfl⟩
  obtain ⟨st, at'⟩ := step_raw ok hk M ⟨ad, had, hpc⟩ c1 (fun ad' had' inp => by
    rw [had] at had'
    cases had'
    rw [hc1]
    rfl) (by rw [hc1]; simp only [skip, zsim])
  have hS : Sys s c1 := by rw [hc1]; simp only [Sys, skip, zsim, and_self]
  refine ⟨c1, ad, had, st, at' rfl, M.sys hS, hS, ?_, ?_, ?_, ?_⟩
  · rw [hc1]
    show mk16 _ _ = _
    simp only [skip, zsim, mk16_hi_lo]
  · rw [hc1]
    show mk16 _ _ = mk16 _ _
    simp only [skip, zsim]
  · rw [hc1]
    show mk16 _ _ = mk16 _ _
    simp only [skip, zsim]
  · rw [hc1]
    simp only [skip, zsim]

/-- A byte of a value read from memory is the byte there. -/
theorem rd_byte (m : ByteArray) (a n j : Nat) (hj : j < n) (ha : a + n ≤ 65536) :
    m.get! (a + j) = UInt8.ofNat (IR.Sem.rd m a n / 256 ^ j % 256) := by
  induction n generalizing a j with
  | zero => omega
  | succ n ih =>
    rw [IR.Sem.rd, Nat.mod_eq_of_lt (show a < 65536 by omega)]
    have hb := (m.get! a).toNat_lt
    cases j with
    | zero =>
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_ofNat']
      simp only [Nat.pow_zero, Nat.div_one, Nat.add_zero]
      omega
    | succ j =>
      rw [show a + (j + 1) = a + 1 + j by omega, ih (a + 1) j (by omega) (by omega)]
      have e : ((m.get! a).toNat + 256 * IR.Sem.rd m (a + 1) n) / 256 ^ (j + 1) =
          IR.Sem.rd m (a + 1) n / 256 ^ j := by
        rw [Nat.pow_succ, Nat.mul_comm (256 ^ j) 256, ← Nat.div_div_eq_div_mul]
        congr 1
        omega
      rw [e]

/-- The items of `rt_st64` and `rt_st32`. -/
def stItems : List Item :=
  [.label "rt_st64", .ins ⟨.ld, [.bc, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym "rt_stw")]⟩,
   .label "rt_st32", .ins ⟨.ld, [.bc, .imm (.num 4)]⟩,
   .label "rt_stw", .ins ⟨.ex, [.de, .hl]⟩, .ins ⟨.ld, [.hl, .imm (.sym "rt_acc")]⟩, .ins ⟨.ldir, []⟩, .ins ⟨.ret, []⟩]

/-- **`rt_st32`**: the four bytes at `HL` are the accumulator's first four; nothing else is written. -/
theorem rt_st32_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat} (hhas : Has Z k stItems) :
    Uses Z "rt_st32" → ∃ entry, Z.sym "rt_st32" entry ∧ entry < 65536 ∧
      Routine Z entry Z.rtK (fun s => Z.ramStart ≤ s.hl.toNat ∧ HLApart Z 4 s)
        (fun s s' => ∀ x, x < Z.stackLo ∨ s.sp.toNat ≤ x → ¬ Z.rt x →
          s'.mem.get! x = (IR.Sem.wr s.mem s.hl.toNat 4 (IR.Sem.rd s.mem Z.acc 4)).get! x) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 3 rfl)
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 7, _, 0, hhas.get 7 rfl, rfl⟩
  have hram := ok.accRam
  have hstk := ok.stack
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi ⟨hhlram, hb, hap⟩ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at4 : At Z.addrs (k + 4) s := at_label ok (hhas.get 3 rfl) ⟨T, hT, hpc⟩
  obtain ⟨c1, ad1, had1, st1, at5, M1, hS1, hbc1, hhl1, _, _⟩ := ld_bc_imm ok (hhas.get 4 rfl) M at4
  have at6 := at_label ok (hhas.get 5 rfl) at5
  obtain ⟨st2, at7, M2, hS2⟩ := does_raw ok does_ex_de_hl (hhas.get 6 rfl) M1 at6
  obtain ⟨c3, ad3, had3, st3, at8, M3, hS3, hhl3, hde3, hbc3, _⟩ := ld_hl_imm ok (hhas.get 7 rfl) M2 at7
  have hbcv : c3.bc.toNat = 3 + 1 := by
    rw [hbc3, exDEHL_bc, hbc1]
    exact immW_toNat _ _ _ 4 rfl rfl (by decide)
  have hhlv : c3.hl.toNat = Z.acc := by
    rw [hhl3]
    exact immW_toNat _ _ _ _ rfl (sym_val ad3 hacc) (by omega)
  have hdev : c3.de.toNat = s.hl.toNat := by rw [hde3, exDEHL_de, hhl1]
  have hS03 : Sys s c3 := (hS1.trans hS2).trans hS3
  have h0 := hap 0 (by omega)
  have h3 := hap 3 (by omega)
  obtain ⟨c4, st4, at9, M4, hsp4, hr4, hsz4, hcp, hkeep⟩ := ldir_copy ok (hhas.get 8 rfl) 3 c3 Z.acc s.hl.toNat M3 at8
    (by rw [hS03.2.1]; exact hrs) hhlv hdev hbcv hhlram (by omega) (by omega)
    (by rw [hS03.1]; exact hmsz) (fun j hj => by omega)
  obtain ⟨c', st5, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 9 rfl) M4 at9
  rw [hS03.1] at hcp hkeep
  refine ⟨c', (((st1.trans st2).trans st3).trans st4).trans st5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc', hsp4, hS03.2.2.2]
    apply UInt16.toNat_inj.mp
    rw [cpu_rd16 _ _ (by omega), cpu_rd16 _ _ (by omega)]
    refine rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hkeep x ?_)
    have a0 := (hap 0 (by omega)).2
    have a1 := (hap 1 (by omega)).2
    have a2 := (hap 2 (by omega)).2
    have a3 := (hap 3 (by omega)).2
    omega
  · rw [hsp', hsp4, hS03.2.2.2]
  · rw [hh']
    exact M4.2
  · rw [hrs', hr4, hS03.2.1]
  · rw [hmem']
    exact hsz4
  · intro x _ _
    show c'.mem.get! x = _
    rw [hmem', wr_get _ _ _ _ _ (by rw [hmsz]; exact hb) (by rw [hmsz]; exact Nat.le_refl _)]
    by_cases hx : s.hl.toNat ≤ x ∧ x < s.hl.toNat + 4
    · rw [if_pos hx]
      have e : x = s.hl.toNat + (x - s.hl.toNat) := by omega
      rw [e, hcp (x - s.hl.toNat) (by omega), show s.hl.toNat + (x - s.hl.toNat) - s.hl.toNat = x - s.hl.toNat by omega]
      exact rd_byte s.mem Z.acc 4 (x - s.hl.toNat) (by omega) (by omega)
    · rw [if_neg hx]
      exact hkeep x (by omega)

/-- The items proved are those of the runtime's pieces (`#guard`). -/
def inRuntime (items : List Item) : Bool :=
  Runtime.pieces.any fun pc => match Asm.parse pc.src with
    | .ok l => l == items
    | .error _ => false

#guard inRuntime ldItems
#guard inRuntime stItems

/-! ## The accumulator from a register -/

/-- `ld (name+off),hl`, in RAM: the word of `HL` is there, the rest as it was. -/
theorem ld_cell_hl (ok : Z.OK) {k A : Nat} {name : String} (off : Nat)
    (hk : Z.items[k]? = some (.ins ⟨.ld, [.mem (.sym name (Int.ofNat off)), .hl]⟩)) (hsym : Z.sym name A)
    (hram : Z.ramStart ≤ A + off) (hA : A + off + 2 ≤ 65536) {s : Cpu} (M : Mach Z s)
    (hrs : s.ramStart.toNat = Z.ramStart) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ s'.mem = IR.Sem.wr s.mem (A + off) 2 s.hl.toNat ∧
      s'.ramStart = s.ramStart ∧ s'.halted = s.halted ∧ s'.sp = s.sp ∧ s'.hl = s.hl := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.mem (.sym name (Int.ofNat off)), .hl]⟩).toNat = A + off :=
    immW_toNat _ _ _ _ rfl (sym_val_off ad off hsym) (by omega)
  have hnn1 : (Instr.immW (Z.a.env ad) ⟨.ld, [.mem (.sym name (Int.ofNat off)), .hl]⟩ + 1).toNat = A + off + 1 := by
    rw [UInt16.toNat_add, hnn]
    show (A + off + 1) % 65536 = _
    omega
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = ((skip (op1 s) 2).wr16
      (Instr.immW (Z.a.env ad) ⟨.ld, [.mem (.sym name (Int.ofNat off)), .hl]⟩) (op1 s).hl).tick 16 := ⟨_, rfl⟩
  obtain ⟨st, at'⟩ := step_raw ok hk M ⟨ad, had, hpc⟩ c1 (fun ad' had' inp => by
    rw [had] at had'
    cases had'
    rw [hc1]
    rfl) (by rw [hc1]; simp only [Cpu.wr16, skip, zsim])
  have hset : c1.mem = (s.mem.set! (A + off) (s.hl.toUInt8)).set! (A + off + 1) ((s.hl >>> 8).toUInt8) := by
    rw [hc1]
    simp only [zsim, Cpu.wr16]
    rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hnn1, hrs]; omega),
      cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hnn, hrs]; exact hram)]
    simp only [zsim]
    rw [hnn, hnn1]
  have hmem : c1.mem = IR.Sem.wr s.mem (A + off) 2 s.hl.toNat := by
    rw [hset]
    have := s.hl.toNat_lt
    refine wr_two _ _ _ (by omega) _ _ ?_ ?_
    · rw [UInt16.toNat_toUInt8]
    · rw [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]
      rw [show (8 : UInt16).toNat % 16 = 8 from rfl, Nat.shiftRight_eq_div_pow]
  have hr1 : c1.ramStart = s.ramStart := by rw [hc1]; simp only [Cpu.wr16, skip, zsim]
  have hh1 : c1.halted = s.halted := by rw [hc1]; simp only [Cpu.wr16, skip, zsim]
  refine ⟨c1, st, at' rfl, ⟨⟨by rw [hr1]; exact M.1.rom, fun x b hx => ?_⟩, by rw [hh1]; exact M.2⟩, hmem, hr1, hh1,
    by rw [hc1]; simp only [Cpu.wr16, skip, zsim], ?_⟩
  · have hlt : x < Z.a.bytes.size := by
      rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hx; cases hx
    have hrom := M.1.rom
    have hb := M.1.bytes x b hx
    rw [Nat.zero_add] at hb ⊢
    rw [hset, getBang_set _ _ _ _ (by omega), getBang_set _ _ _ _ (by omega)]
    exact hb
  · rw [hc1]
    show mk16 _ _ = mk16 _ _
    simp only [Cpu.wr16, skip, zsim]

/-- The items of `rt_acc_a`, `rt_acc_hl` and `rt_zx32`. -/
def accItems : List Item :=
  [.label "rt_acc_a", .ins ⟨.ld, [.l, .a]⟩, .ins ⟨.ld, [.h, .imm (.num 0)]⟩,
   .label "rt_acc_hl", .ins ⟨.ld, [.mem (.sym "rt_acc" 0), .hl]⟩, .ins ⟨.ld, [.hl, .imm (.num 0)]⟩,
   .ins ⟨.ld, [.mem (.sym "rt_acc" 2), .hl]⟩,
   .label "rt_zx32", .ins ⟨.ld, [.hl, .imm (.num 0)]⟩, .ins ⟨.ld, [.mem (.sym "rt_acc" 4), .hl]⟩,
   .ins ⟨.ld, [.mem (.sym "rt_acc" 6), .hl]⟩, .ins ⟨.ret, []⟩]

/-- From `rt_acc_hl` on: the accumulator's eight bytes are `HL`, nothing else is written. -/
theorem acc_core (ok : Z.OK) {k : Nat} (hhas : Has Z k accItems) {s : Cpu} (M : Mach Z s)
    (hat : At Z.addrs (k + 4) s) (hrs : s.ramStart.toNat = Z.ramStart) (hmsz : s.mem.size = 65536)
    (hlo : Z.stackLo ≤ s.sp.toNat) (hhi : s.sp.toNat + 2 ≤ Z.stackHi) :
    ∃ s', Steps s s' ∧ s'.pc = s.rd16 s.sp ∧ s'.sp = s.sp + 2 ∧ s'.halted = false ∧ s'.ramStart = s.ramStart ∧
      s'.mem.size = 65536 ∧ IR.Sem.rd s'.mem Z.acc 8 = s.hl.toNat ∧
      ∀ x, x < Z.acc ∨ Z.acc + 8 ≤ x → s'.mem.get! x = s.mem.get! x := by
  have hacc : Z.sym "rt_acc" Z.acc := ok.accSym ⟨k + 4, _, 0, hhas.get 4 rfl, rfl⟩
  have hram := ok.accRam
  have hstk := ok.stack
  have hacs := ok.accStack
  obtain ⟨c1, st1, at5, M1, hm1, hr1, hh1, hsp1, hhl1⟩ := ld_cell_hl ok 0 (hhas.get 4 rfl) hacc (by omega) (by omega) M hrs hat
  obtain ⟨c2, ad2, _, st2, at6, M2, hS2, hhl2, _, _, _⟩ := ld_hl_imm ok (hhas.get 5 rfl) M1 at5
  have hz2 : c2.hl.toNat = 0 := by rw [hhl2]; exact immW_toNat _ _ _ 0 rfl rfl (by decide)
  obtain ⟨c3, st3, at7, M3, hm3, hr3, hh3, hsp3, hhl3⟩ := ld_cell_hl ok 2 (hhas.get 6 rfl) hacc (by omega) (by omega) M2
    (by rw [hS2.2.1, hr1]; exact hrs) at6
  have at8 := at_label ok (hhas.get 7 rfl) at7
  obtain ⟨c4, ad4, _, st4, at9, M4, hS4, hhl4, _, _, _⟩ := ld_hl_imm ok (hhas.get 8 rfl) M3 at8
  have hz4 : c4.hl.toNat = 0 := by rw [hhl4]; exact immW_toNat _ _ _ 0 rfl rfl (by decide)
  obtain ⟨c5, st5, at10, M5, hm5, hr5, hh5, hsp5, hhl5⟩ := ld_cell_hl ok 4 (hhas.get 9 rfl) hacc (by omega) (by omega) M4
    (by rw [hS4.2.1, hr3, hS2.2.1, hr1]; exact hrs) at9
  obtain ⟨c6, st6, at11, M6, hm6, hr6, hh6, hsp6, hhl6⟩ := ld_cell_hl ok 6 (hhas.get 10 rfl) hacc (by omega) (by omega) M5
    (by rw [hr5, hS4.2.1, hr3, hS2.2.1, hr1]; exact hrs) at10
  obtain ⟨c', st7, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 11 rfl) M6 at11
  have hmem : c6.mem = IR.Sem.wr (IR.Sem.wr (IR.Sem.wr (IR.Sem.wr s.mem (Z.acc + 0) 2 s.hl.toNat) (Z.acc + 2) 2 0)
      (Z.acc + 4) 2 0) (Z.acc + 6) 2 0 := by
    rw [hm6, hhl5, hz4, hm5, hz4, hS4.1, hm3, hz2, hS2.1, hm1]
  have hsp : c6.sp = s.sp := by rw [hsp6, hsp5, hS4.2.2.2, hsp3, hS2.2.2.2, hsp1]
  have hfar : ∀ x, x < Z.acc ∨ Z.acc + 8 ≤ x → c6.mem.get! x = s.mem.get! x := by
    intro x hx
    rw [hmem, wr_get_far _ _ _ _ _ (by omega) (by omega), wr_get_far _ _ _ _ _ (by omega) (by omega),
      wr_get_far _ _ _ _ _ (by omega) (by omega), wr_get_far _ _ _ _ _ (by omega) (by omega)]
  have hv := s.hl.toNat_lt
  refine ⟨c', ((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc', hsp]
    apply UInt16.toNat_inj.mp
    rw [cpu_rd16 _ _ (by omega), cpu_rd16 _ _ (by omega)]
    exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hfar x (by omega))
  · rw [hsp', hsp]
  · rw [hh']
    exact M6.2
  · rw [hrs', hr6, hr5, hS4.2.1, hr3, hS2.2.1, hr1]
  · rw [hmem', hmem]
    simp only [wr_size]
    exact hmsz
  · rw [hmem', hmem]
    rw [show (8 : Nat) = 2 + (2 + (2 + 2)) from rfl, rd_add, rd_add, rd_add]
    rw [show Z.acc + 2 + 2 = Z.acc + 4 by omega, show Z.acc + 4 + 2 = Z.acc + 6 by omega]
    rw [rd_wr_other _ _ _ _ _ 2 (by omega) (by omega) (by omega), rd_wr_other _ _ _ _ _ 2 (by omega) (by omega) (by omega),
      rd_wr_other _ _ _ _ _ 2 (by omega) (by omega) (by omega),
      rd_wr_other _ _ _ _ (Z.acc + 2) 2 (by omega) (by omega) (by omega),
      rd_wr_other _ _ _ _ (Z.acc + 2) 2 (by omega) (by omega) (by omega),
      rd_wr_other _ _ _ _ (Z.acc + 4) 2 (by omega) (by omega) (by omega)]
    rw [show Z.acc + 0 = Z.acc from rfl,
      rd_wr _ _ _ _ (by rw [hmsz]; omega) (by rw [hmsz]; exact Nat.le_refl _),
      rd_wr _ _ _ _ (by simp only [wr_size]; rw [hmsz]; omega)
        (by simp only [wr_size]; rw [hmsz]; exact Nat.le_refl _),
      rd_wr _ _ _ _ (by simp only [wr_size]; rw [hmsz]; omega)
        (by simp only [wr_size]; rw [hmsz]; exact Nat.le_refl _),
      rd_wr _ _ _ _ (by simp only [wr_size]; rw [hmsz]; omega)
        (by simp only [wr_size]; rw [hmsz]; exact Nat.le_refl _)]
    rw [Nat.mod_eq_of_lt (show s.hl.toNat < 2 ^ (8 * 2) from hv)]
    simp
  · intro x hx
    rw [hmem']
    exact hfar x hx

#guard inRuntime accItems

/-- **`rt_acc_hl`**: the accumulator is `HL`, zero-extended to its eight bytes. -/
theorem rt_acc_hl_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat} (hhas : Has Z k accItems) :
    RtAcc Z "rt_acc_hl" (fun _ => True) (fun s s' => IR.Sem.rd s'.mem Z.acc 8 = s.hl.toNat) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 3 rfl)
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi _ => ?_⟩
  have at4 : At Z.addrs (k + 4) s := at_label ok (hhas.get 3 rfl) ⟨T, hT, hpc⟩
  obtain ⟨c', st, hpc', hsp', hh', hrs', hsz', hv, hfar⟩ := acc_core ok hhas ⟨I, hh⟩ at4 hrs hmsz (by omega) hhi
  exact ⟨c', st, hpc', hsp', hh', hrs', hsz', hv, fun x _ _ hx => hfar x hx⟩

/-- **`rt_acc_a`**: the accumulator is `A`, zero-extended to its eight bytes. -/
theorem rt_acc_a_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat} (hhas : Has Z k accItems) :
    RtAcc Z "rt_acc_a" (fun _ => True) (fun s s' => IR.Sem.rd s'.mem Z.acc 8 = s.a.toNat) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 0 rfl)
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz hlo hhi _ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at1 : At Z.addrs (k + 1) s := at_label ok (hhas.get 0 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at2, M1, hS1⟩ := does_raw ok does_ld_l_a (hhas.get 1 rfl) M at1
  obtain ⟨st2, at3, M2, hS2⟩ := does_raw ok does_ld_h_0 (hhas.get 2 rfl) M1 at2
  have at4 := at_label ok (hhas.get 3 rfl) at3
  have hS : Sys s (ldH0 (ldRA 5 s)) := hS1.trans hS2
  obtain ⟨c', st, hpc', hsp', hh', hrs', hsz', hv, hfar⟩ := acc_core ok hhas M2 at4 (by rw [hS.2.1]; exact hrs)
    (by rw [hS.1]; exact hmsz) (by rw [hS.2.2.2]; omega) (by rw [hS.2.2.2]; exact hhi)
  have hhl : (ldH0 (ldRA 5 s)).hl.toNat = s.a.toNat := by
    rw [hl_toNat]
    have e1 : (ldH0 (ldRA 5 s)).h = 0 := by simp only [ldH0, zsim]; rfl
    have e2 : (ldH0 (ldRA 5 s)).l = s.a := by simp only [ldH0, ldRA, zsim]
    rw [e1, e2]
    show 0 * 256 + _ = _
    omega
  refine ⟨c', (st1.trans st2).trans st, ?_, ?_, hh', ?_, hsz', ?_, fun x _ _ hx => ?_⟩
  · rw [hpc', rd16_sys hS]
  · rw [hsp', hS.2.2.2]
  · rw [hrs', hS.2.1]
  · show IR.Sem.rd c'.mem Z.acc 8 = s.a.toNat
    rw [hv, hhl]
  · rw [hfar x hx, hS.1]

end

end Ember.Proof.Z80Gen
