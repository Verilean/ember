import Ember.Proof.Z80Rt
import Ember.Proof.IRProgram

/-!
# Ember.Proof.Z80Boot — start-up and the loop that calls the entry (plan M7.3)

Around the functions of a program the runtime has code of its own: the
start-up (the stack pointer, the RAM cleared) and the loop that calls
the program's entry.  This file has what proofs about that code need
beyond `Z80Rt` — jumps (`jr` with any condition, `jr`), a byte of RAM
read and written by name, a read of a port, the first call from an empty
stack, `ldir` — and start-up itself (`boot_ok`).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim

section
variable {Z : ZCtx}

/-! ## Relative jumps -/

/-- **`jr cc` to a label**, any of the four conditions. -/
theorem jr_cond_step (ok : Z.OK) {k j : Nat} {cA : Arg} {y : UInt8} {l : String}
    (hy : (cA = .nz ∧ y = 0) ∨ (cA = .z ∧ y = 1) ∨ (cA = .nc ∧ y = 2) ∨ (cA = .c ∧ y = 3))
    (hk : Z.items[k]? = some (.ins ⟨.jr, [cA, .imm (.sym l)]⟩))
    (hj : Z.items[j]? = some (.label l)) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ Mach Z s' ∧ Sys s s' ∧ KeepR s s' ∧
      (if s.cond y = true then At Z.addrs j s' else At Z.addrs (k + 1) s') := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨T, hT, hsym, hTlt⟩ := label_at ok hj M.1
  obtain ⟨bs, hbs, hnext, hlt⟩ := ok.placed.next M.1 hk had
  have hval : (Z.a.env ad).val (.sym l) = Int.ofNat T := sym_val ad hsym
  have henc : ∃ lst, (rel (.sym l)).run (Z.a.env ad) = .ok lst ∧ bs.length = 2 := by
    have h' := encode_run hbs
    rcases hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
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
  have himm : Instr.immB (Z.a.env ad) ⟨.jr, [cA, .imm (.sym l)]⟩ = byteOf (Int.ofNat T - (Int.ofNat ad + 2)) := by
    rcases hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (show byteOf ((Z.a.env ad).val (.sym l) - ((Z.a.env ad).pc + 2)) = _
       rw [hval]
       rfl)
  have hexec : ∀ inp, exec (Z.a.env ad) ⟨.jr, [cA, .imm (.sym l)]⟩ s inp =
      some (jrCC y (byteOf (Int.ofNat T - (Int.ofNat ad + 2))) s) := by
    intro inp
    rw [← himm]
    rcases hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hst := fun inp => (step_item ok.placed M.1 hk had hpc M.2 (inp := inp) (hexec inp)).1
  refine ⟨_, Steps.one hst (jrCC_io _ _ _), M.sys (jrCC_sys _ _ _), jrCC_sys _ _ _, jrCC_keep _ _ _, ?_⟩
  by_cases hc : s.cond y = true
  · rw [if_pos hc]
    refine ⟨T, hT, ?_⟩
    have hc' : (op1 s).cond y = true := by rw [cond_op1]; exact hc
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
    have hc' : (op1 s).cond y = false := by rw [cond_op1]; simpa using hc
    simp only [jrCC, hc', Bool.false_eq_true, if_false, zsim]
    rw [UInt16.toNat_add, UInt16.toNat_add, hpc, hlen]
    show ((ad + 1) % 65536 + 1) % 65536 = _
    rw [hlen] at hlt'
    omega

/-- The state after `jr e`. -/
def jrTo (n : UInt8) (s : Cpu) : Cpu :=
  ({ (skip (op1 s) 1) with pc := (skip (op1 s) 1).pc + sext n } : Cpu).tick 12

/-- **`jr` to a label.** -/
theorem jr_step (ok : Z.OK) {k j : Nat} {l : String} (hk : Z.items[k]? = some (.ins ⟨.jr, [.imm (.sym l)]⟩))
    (hj : Z.items[j]? = some (.label l)) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ Mach Z s' ∧ Sys s s' ∧ KeepR s s' ∧ At Z.addrs j s' := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨T, hT, hsym, hTlt⟩ := label_at ok hj M.1
  obtain ⟨bs, hbs, hnext, hlt⟩ := ok.placed.next M.1 hk had
  have hval : (Z.a.env ad).val (.sym l) = Int.ofNat T := sym_val ad hsym
  have henc : ∃ lst, (rel (.sym l)).run (Z.a.env ad) = .ok lst ∧ bs.length = 2 := by
    have h' := encode_run hbs
    have he' : ((rel (.sym l)).run (Z.a.env ad)).bind _ = Except.ok bs := h'
    obtain ⟨lst, hl, hb⟩ := bind_ok he'
    have := rel_bytes hl
    subst this
    cases hb
    exact ⟨_, hl, rfl⟩
  obtain ⟨lst, hrel, hlen⟩ := henc
  obtain ⟨r1, r2⟩ := rel_range hrel rfl
  rw [hval] at r1 r2
  have hpcv : (Z.a.env ad).pc = Int.ofNat ad := rfl
  rw [hpcv] at r1 r2
  have hlt' := hlt (by intro e; rw [e] at hlen; cases hlen)
  have himm : Instr.immB (Z.a.env ad) ⟨.jr, [.imm (.sym l)]⟩ = byteOf (Int.ofNat T - (Int.ofNat ad + 2)) := by
    show byteOf ((Z.a.env ad).val (.sym l) - ((Z.a.env ad).pc + 2)) = _
    rw [hval]
    rfl
  have hexec : ∀ inp, exec (Z.a.env ad) ⟨.jr, [.imm (.sym l)]⟩ s inp =
      some (jrTo (byteOf (Int.ofNat T - (Int.ofNat ad + 2))) s) := by
    intro inp
    rw [← himm]
    rfl
  have hst := fun inp => (step_item ok.placed M.1 hk had hpc M.2 (inp := inp) (hexec inp)).1
  have hS : Sys s (jrTo (byteOf (Int.ofNat T - (Int.ofNat ad + 2))) s) := by
    simp only [Sys, jrTo, skip, zsim, and_self]
  refine ⟨_, Steps.one hst (by simp only [jrTo, zsim]), M.sys hS, hS, by simp only [KeepR, jrTo, skip, zsim, and_self],
    T, hT, ?_⟩
  simp only [jrTo, zsim]
  have hs := sext_val (Int.ofNat T - (Int.ofNat ad + 2)) r1 r2
  rw [UInt16.toNat_add, UInt16.toNat_add, UInt16.toNat_add, hpc]
  show (((ad + 1) % 65536 + 1) % 65536 + (sext _).toNat) % 65536 = T
  rw [hlen] at hlt'
  generalize (sext (byteOf (Int.ofNat T - (Int.ofNat ad + 2)))).toNat = sx at hs ⊢
  simp only [Int.ofNat_eq_coe] at hs r1 r2
  omega

/-! ## Only the runtime's own bytes differ -/

/-- From `s` to `s'` the CPU runs on, with the stack pointer and the
memory as they were but for the runtime's own bytes. -/
structure Frame (Z : ZCtx) (s s' : Cpu) : Prop where
  rs : s'.ramStart = s.ramStart
  run : s'.halted = s.halted
  sp : s'.sp = s.sp
  msz : s'.mem.size = s.mem.size
  mem : ∀ x, ¬ Z.rt x → s'.mem.get! x = s.mem.get! x

theorem Frame.refl (s : Cpu) : Frame Z s s := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {s s' s'' : Cpu} (h1 : Frame Z s s') (h2 : Frame Z s' s'') : Frame Z s s'' :=
  ⟨h2.rs.trans h1.rs, h2.run.trans h1.run, h2.sp.trans h1.sp, h2.msz.trans h1.msz,
    fun x hx => (h2.mem x hx).trans (h1.mem x hx)⟩

theorem Frame.of_sys {s s' : Cpu} (h : Sys s s') : Frame Z s s' :=
  ⟨h.2.1, h.2.2.1, h.2.2.2, by rw [h.1], fun _ _ => by rw [h.1]⟩

theorem Mach.frame (ok : Z.OK) {s s' : Cpu} (M : Mach Z s) (hrs : s.ramStart.toNat = Z.ramStart)
    (h : Frame Z s s') : Mach Z s' := by
  refine ⟨⟨by rw [h.rs]; exact M.1.rom, fun x b hx => ?_⟩, by rw [h.run]; exact M.2⟩
  have hlt : x < Z.a.bytes.size := by
    rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  have hrom := M.1.rom
  have hb := M.1.bytes x b hx
  rw [Nat.zero_add] at hb ⊢
  rw [h.mem x (fun hr => by have := ok.rtRam x hr; omega)]
  exact hb

/-! ## Steps of the runtime's own code -/

/-- An instruction that leaves memory, the stack pointer and `halted` alone. -/
theorem sys_step (ok : Z.OK) {k : Nat} {i : Instr} (hk : Z.items[k]? = some (.ins i)) (hf : i.falls = true)
    {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s)
    (hx : ∀ ad, ∃ s', (∀ inp, exec (Z.a.env ad) i s inp = some s') ∧ s'.io = .none ∧ Sys s s') :
    ∃ s', Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ Sys s s' := by
  obtain ⟨ad, had, hpc⟩ := hat
  obtain ⟨s', hex, hio, hS⟩ := hx ad
  obtain ⟨st, at'⟩ := step_raw ok hk M ⟨ad, had, hpc⟩ s' (fun ad' had' inp => by
    rw [had] at had'
    cases had'
    exact hex inp) hio
  exact ⟨s', st, at' hf, M.sys hS, hS⟩

/-- `ld a,(nn)`. -/
theorem ld_a_mem_step (ok : Z.OK) {k : Nat} {v : Val} (hk : Z.items[k]? = some (.ins ⟨.ld, [.a, .mem v]⟩))
    {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ Sys s s' :=
  sys_step ok hk rfl M hat (fun ad => ⟨_, fun _ => rfl, by simp only [zsim], by simp only [Sys, skip, zsim, and_self]⟩)

/-- `ld hl,nn`. -/
theorem ld_hl_imm_step (ok : Z.OK) {k : Nat} {v : Val} (hk : Z.items[k]? = some (.ins ⟨.ld, [.hl, .imm v]⟩))
    {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ Sys s s' :=
  sys_step ok hk rfl M hat (fun ad => ⟨_, fun _ => rfl, by simp only [zsim], by simp only [Sys, skip, zsim, and_self]⟩)

theorem set_size (m : ByteArray) (a : Nat) (v : UInt8) : (m.set! a v).size = m.size := by
  obtain ⟨bs⟩ := m
  simp [ByteArray.set!, ByteArray.size]

/-- A read of a port: the bus answers, the machine sees the read. -/
theorem in_step (ok : Z.OK) {k : Nat} {n : Nat} (hn : n < 256)
    (hk : Z.items[k]? = some (.ins ⟨.in, [.a, .mem (.num (Int.ofNat n))]⟩)) {s : Cpu} (M : Mach Z s)
    (hat : At Z.addrs k s) (w : Z.W) :
    ∃ s' p, lo p = UInt8.ofNat n ∧ WSteps Z (s, w) (s', Z.dev w (.read p)) ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧
      Sys s s' ∧ s'.a = Z.bus w p := by
  obtain ⟨p, hp⟩ : ∃ p : UInt16, p = mk16 (op1 s).a (byteOf (Int.ofNat n)) := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = (({ (skip (op1 s) 1) with a := Z.bus w p, io := .read p } : Cpu).tick 11) :=
    ⟨_, rfl⟩
  obtain ⟨st1, at2⟩ := wstep_item ok hk M hat w (s' := c1) (fun ad _ => by rw [hc1, hp]; rfl)
  have hio1 : c1.io = .read p := by rw [hc1]; rfl
  rw [hio1] at st1
  have hS1 : Sys s c1 := by rw [hc1]; simp only [Sys, skip, zsim, and_self]
  refine ⟨c1, p, ?_, st1, at2 rfl, M.sys hS1, hS1, by rw [hc1]; rfl⟩
  rw [hp, lo_mk16]
  apply UInt8.toNat_inj.mp
  rw [byteOf_toNat, UInt8.toNat_ofNat']
  show ((n : Int) % 256).toNat = n % 256
  omega

/-- **The first call**, from an empty stack at the top of memory: the
return address goes to the last two bytes. -/
theorem call_top (ok : Z.OK) {k : Nat} {name : String} {entry : Nat}
    (hk : Z.items[k]? = some (.ins ⟨.call, [.imm (.sym name)]⟩)) (hsym : Z.sym name entry) (hent : entry < 65536)
    {s : Cpu} (hat : At Z.addrs k s) (I : Img Z.a 0 s) (hh : s.halted = false)
    (hrs : s.ramStart.toNat = Z.ramStart) (hsz : s.mem.size = 65536) (hsp : s.sp = 0)
    (hram : Z.ramStart ≤ 65534) :
    ∃ s1, Steps s s1 ∧ s1.sp.toNat = 65534 ∧ s1.pc.toNat = entry ∧ Img Z.a 0 s1 ∧ s1.halted = false ∧
      s1.ramStart = s.ramStart ∧ s1.mem.size = 65536 ∧
      (∀ x, x < 65534 → s1.mem.get! x = s.mem.get! x) ∧
      ∀ s' : Cpu, s'.pc.toNat = IR.Sem.rd s1.mem 65534 2 → At Z.addrs (k + 1) s' := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hnn : (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩).toNat = entry :=
    immW_toNat _ _ _ _ rfl (sym_val ad hsym) hent
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = (callTo (skip (op1 s) 2)
      (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩)).tick 17 := ⟨_, rfl⟩
  have hst := fun inp => (step_item ok.placed I hk had hpc hh (inp := inp) (s' := c1) (by rw [hc1]; rfl)).1
  have hmem1 : c1.mem = IR.Sem.wr s.mem 65534 2 (s.pc + 1 + 2).toNat := by
    rw [hc1]
    simp only [callTo, zsim, Cpu.push, Cpu.wr16, skip]
    have e0 : (s.sp - 2).toNat = 65534 := by
      rw [hsp]
      rfl
    have e1 : (s.sp - 2 + 1).toNat = 65534 + 1 := by
      rw [hsp]
      rfl
    rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [e1, hrs]; omega),
      cpu_wr_mem _ _ _ (by simp only [zsim]; rw [e0, hrs]; omega)]
    simp only [zsim]
    rw [e0, e1]
    refine wr_two _ _ _ (by omega) _ _ ?_ ?_
    · rw [UInt16.toNat_toUInt8]
    · rw [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]
      rw [show (8 : UInt16).toNat % 16 = 8 from rfl, Nat.shiftRight_eq_div_pow]
  have hsp1 : c1.sp.toNat = 65534 := by
    rw [hc1]
    simp only [callTo, zsim, Cpu.push, skip]
    rw [hsp]
    rfl
  refine ⟨c1, Steps.one hst (by rw [hc1]; simp only [callTo, zsim]), hsp1, by rw [hc1]; simp only [callTo, zsim]; exact hnn,
    Img.of_wr I (by rw [hc1]; simp only [callTo, zsim]) hmem1 (by omega) (by omega),
    by rw [hc1]; simp only [callTo, zsim]; exact hh, by rw [hc1]; simp only [callTo, zsim],
    by rw [hmem1, wr_size]; exact hsz, fun x hx => by rw [hmem1, wr_get_far _ _ _ _ _ (by omega) (by omega)],
    fun s' hpc' => ?_⟩
  obtain ⟨bs, hbs, hnext, hlt⟩ := ok.placed.next I hk had
  have hlen := call_len hbs
  refine ⟨ad + bs.length, hnext, ?_⟩
  rw [hpc', hmem1, rd_wr _ _ _ _ (by rw [hsz]; exact Nat.le_refl _) (by rw [hsz]; exact Nat.le_refl _)]
  have hlt' := hlt (by intro e; rw [e] at hlen; cases hlen)
  have : (s.pc + 1 + 2).toNat = ad + 3 := by
    rw [UInt16.toNat_add, UInt16.toNat_add, hpc]
    show ((ad + 1) % 65536 + 2) % 65536 = _
    omega
  rw [this, hlen]
  show (ad + 3) % 65536 = _
  omega

/-! ## A byte of RAM the runtime keeps -/

/-- `ld a,(nn)` of a named byte: `A` is what is there. -/
theorem ld_a_cell (ok : Z.OK) {k A : Nat} {name : String}
    (hk : Z.items[k]? = some (.ins ⟨.ld, [.a, .mem (.sym name)]⟩)) (hsym : Z.sym name A) (hA : A < 65536)
    {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ Sys s s' ∧ s'.a = s.mem.get! A := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (.sym name)]⟩).toNat = A :=
    immW_toNat _ _ _ _ rfl (sym_val ad hsym) hA
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = (({ (skip (op1 s) 2) with
      a := (op1 s).rd (Instr.immW (Z.a.env ad) ⟨.ld, [.a, .mem (.sym name)]⟩) } : Cpu).tick 13) := ⟨_, rfl⟩
  obtain ⟨st, at'⟩ := step_raw ok hk M ⟨ad, had, hpc⟩ c1 (fun ad' had' inp => by
    rw [had] at had'
    cases had'
    rw [hc1]
    rfl) (by rw [hc1]; rfl)
  have hS : Sys s c1 := by rw [hc1]; simp only [Sys, skip, zsim, and_self]
  refine ⟨c1, st, at' rfl, M.sys hS, hS, ?_⟩
  rw [hc1]
  show (op1 s).mem.get! (Instr.immW _ _).toNat = _
  rw [hnn]
  rfl

/-- `ld (nn),a` to a named byte in RAM: that byte is `A`, the rest as it was. -/
theorem ld_cell_a (ok : Z.OK) {k A : Nat} {name : String}
    (hk : Z.items[k]? = some (.ins ⟨.ld, [.mem (.sym name), .a]⟩)) (hsym : Z.sym name A) (hram : Z.ramStart ≤ A)
    (hA : A < 65536) {s : Cpu} (M : Mach Z s) (hrs : s.ramStart.toNat = Z.ramStart) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ s'.mem = s.mem.set! A s.a ∧ s'.ramStart = s.ramStart ∧
      s'.halted = s.halted ∧ s'.sp = s.sp := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hnn : (Instr.immW (Z.a.env ad) ⟨.ld, [.mem (.sym name), .a]⟩).toNat = A :=
    immW_toNat _ _ _ _ rfl (sym_val ad hsym) hA
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = ((skip (op1 s) 2).wr
      (Instr.immW (Z.a.env ad) ⟨.ld, [.mem (.sym name), .a]⟩) (op1 s).a).tick 13 := ⟨_, rfl⟩
  obtain ⟨st, at'⟩ := step_raw ok hk M ⟨ad, had, hpc⟩ c1 (fun ad' had' inp => by
    rw [had] at had'
    cases had'
    rw [hc1]
    rfl) (by rw [hc1]; simp only [skip, zsim])
  have hmem : c1.mem = s.mem.set! A s.a := by
    rw [hc1]
    simp only [zsim]
    rw [cpu_wr_mem _ _ _ (by simp only [skip, zsim]; rw [hrs, hnn]; exact hram)]
    simp only [skip, zsim, hnn]
  have hr1 : c1.ramStart = s.ramStart := by rw [hc1]; simp only [skip, zsim]
  have hh1 : c1.halted = s.halted := by rw [hc1]; simp only [skip, zsim]
  refine ⟨c1, st, at' rfl, ⟨⟨by rw [hr1]; exact M.1.rom, fun x b hx => ?_⟩, by rw [hh1]; exact M.2⟩, hmem, hr1, hh1,
    by rw [hc1]; simp only [skip, zsim]⟩
  have hlt : x < Z.a.bytes.size := by
    rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  have hrom := M.1.rom
  have hb := M.1.bytes x b hx
  rw [Nat.zero_add] at hb ⊢
  rw [hmem, getBang_set _ _ _ _ (by omega)]
  exact hb

/-- `xor a` as the model runs it: `A` is zero. -/
def xorA (s : Cpu) : Cpu := ((op1 s).alu 5 ((op1 s).reg .hl 7)).tick 4

theorem does_xor_a : Does ⟨.xor, [.a]⟩ xorA :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, xorA, zsim, and_self], fun s => by simp only [xorA, zsim]⟩

theorem xorA_a (s : Cpu) : (xorA s).a = 0 := by
  show (op1 s).a ^^^ (op1 s).reg .hl 7 = 0
  simp only [zsim]
  exact UInt8.xor_self

/-! ## `ldir` -/

/-- One round of `ldir`, the prefix and the opcode fetched (`execBlock` for it, without the bus). -/
def ldirOnce (s : Cpu) : Cpu :=
  let v := s.rd s.hl
  let s := s.wr s.de v
  let s := (s.setHL (s.hl + 1)).setDE (s.de + 1)
  let s := s.setBC (s.bc - 1)
  let more : Bool := s.bc != 0
  let n : UInt8 := s.a + v
  let y5 : Bool := n &&& 2 != 0
  let f : UInt8 := (s.f &&& (FS ||| FZ ||| FC)) ||| bit more FPV ||| (n &&& FX) ||| bit y5 FY
  let s := { s with f := f }
  if more then ({ s with pc := s.pc - 2 }).tick 21 else s.tick 16

theorem ldir_exec (env : Env) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env ⟨.ldir, []⟩ s inp = some (ldirOnce (op2 s)) := rfl

theorem bc_setBC (s : Cpu) (v : UInt16) : (s.setBC v).bc = v := mk16_hi_lo v
theorem de_setDE (s : Cpu) (v : UInt16) : (s.setDE v).de = v := mk16_hi_lo v
theorem hl_setHL' (s : Cpu) (v : UInt16) : (s.setHL v).hl = v := mk16_hi_lo v
theorem bc_keep (s : Cpu) (v w : UInt16) (x : UInt16) (b : UInt8) :
    (((s.wr x b).setHL v).setDE w).bc = s.bc := by
  show mk16 _ _ = mk16 _ _
  simp only [zsim]
theorem de_keep (s : Cpu) (v : UInt16) (x : UInt16) (b : UInt8) : ((s.wr x b).setHL v).de = s.de := by
  show mk16 _ _ = mk16 _ _
  simp only [zsim]
theorem hl_keep (s : Cpu) (x : UInt16) (b : UInt8) : (s.wr x b).hl = s.hl := by
  show mk16 _ _ = mk16 _ _
  simp only [zsim]
theorem de_wr (s : Cpu) (x : UInt16) (b : UInt8) : (s.wr x b).de = s.de := by
  show mk16 _ _ = mk16 _ _
  simp only [zsim]

/-- What one round does, in terms of the registers before it. -/
theorem ldirOnce_spec (e : Cpu) :
    (ldirOnce e).mem = (e.wr e.de (e.rd e.hl)).mem ∧ (ldirOnce e).hl = e.hl + 1 ∧ (ldirOnce e).de = e.de + 1 ∧
    (ldirOnce e).bc = e.bc - 1 ∧ (ldirOnce e).sp = e.sp ∧ (ldirOnce e).halted = e.halted ∧
    (ldirOnce e).ramStart = e.ramStart ∧ (ldirOnce e).io = e.io ∧
    (ldirOnce e).pc = (if (e.bc - 1 != 0) = true then e.pc - 2 else e.pc) := by
  unfold ldirOnce
  simp only [bc_setBC, bc_keep, hl_keep, de_wr]
  by_cases hm : (e.bc - 1 != 0) = true
  · rw [if_pos hm, if_pos hm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (simp only [zsim]; done)
      | (show mk16 _ _ = _; simp only [zsim, mk16_hi_lo]; done)
      | rfl
  · rw [if_neg hm, if_neg hm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (simp only [zsim]; done)
      | (show mk16 _ _ = _; simp only [zsim, mk16_hi_lo]; done)
      | rfl

theorem getBang_same (m : ByteArray) (i : Nat) (b : UInt8) (h : i < m.size) : (m.set! i b).get! i = b := by
  obtain ⟨bs⟩ := m
  have h' : i < bs.size := h
  simp [ByteArray.set!, ByteArray.get!, h']

theorem sub1_toNat (x : UInt16) (h : 1 ≤ x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  have := x.toNat_lt
  rw [UInt16.toNat_sub]
  show (2 ^ 16 - 1 + x.toNat) % 2 ^ 16 = _
  omega

/-- One round of `ldir`. -/
theorem ldir_round (ok : Z.OK) {k : Nat} (hk : Z.items[k]? = some (.ins ⟨.ldir, []⟩)) {s : Cpu} {h m : Nat}
    (M : Mach Z s) (hat : At Z.addrs k s) (hrs : s.ramStart.toNat = Z.ramStart) (hhl : s.hl.toNat = h)
    (hde : s.de.toNat = h + 1) (hbc : s.bc.toNat = m + 1) (hram : Z.ramStart ≤ h) (hb : h + 1 < 65536) :
    ∃ s1, Steps s s1 ∧ Mach Z s1 ∧ s1.sp = s.sp ∧ s1.ramStart = s.ramStart ∧
      s1.mem = s.mem.set! (h + 1) (s.mem.get! h) ∧ s1.hl.toNat = h + 1 ∧ s1.de.toNat = (h + 2) % 65536 ∧
      s1.bc.toNat = m ∧ (if m = 0 then At Z.addrs (k + 1) s1 else At Z.addrs k s1) := by
  obtain ⟨ad, had, hpc⟩ := hat
  have ehl : (op2 s).hl = s.hl := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  have ede : (op2 s).de = s.de := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  have ebc : (op2 s).bc = s.bc := by show mk16 _ _ = mk16 _ _; simp only [zsim]
  obtain ⟨hmem, hhl1, hde1, hbc1, hsp1, hh1, hrs1, hio1, hpc1⟩ := ldirOnce_spec (op2 s)
  simp only [ehl, ede, ebc] at hmem hhl1 hde1 hbc1 hpc1
  have hst := fun inp => (step_item ok.placed M.1 hk had hpc M.2 (inp := inp) (ldir_exec _ s inp)).1
  have hmem' : (ldirOnce (op2 s)).mem = s.mem.set! (h + 1) (s.mem.get! h) := by
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
    show (h + 1) % 65536 = _
    omega
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

/-- **`ldir` with `DE = HL + 1` and a zero at `HL`**: the `BC` bytes after `HL` are cleared. -/
theorem ldir_zero (ok : Z.OK) {k : Nat} (hk : Z.items[k]? = some (.ins ⟨.ldir, []⟩)) :
    ∀ (n : Nat) (s : Cpu) (h : Nat), Mach Z s → At Z.addrs k s → s.ramStart.toNat = Z.ramStart →
      s.hl.toNat = h → s.de.toNat = h + 1 → s.bc.toNat = n + 1 → Z.ramStart ≤ h → h + n + 1 < 65536 →
      s.mem.get! h = 0 → s.mem.size = 65536 →
      ∃ s', Steps s s' ∧ At Z.addrs (k + 1) s' ∧ Mach Z s' ∧ s'.sp = s.sp ∧ s'.ramStart = s.ramStart ∧
        s'.mem.size = s.mem.size ∧ (∀ x, h < x → x ≤ h + n + 1 → s'.mem.get! x = 0) ∧
        (∀ x, x ≤ h ∨ h + n + 1 < x → s'.mem.get! x = s.mem.get! x) := by
  intro n
  induction n with
  | zero =>
    intro s h M hat hrs hhl hde hbc hram hb hz hsz
    obtain ⟨s1, st, M1, hsp, hr, hmem, _, _, _, hat1⟩ := ldir_round ok hk M hat hrs hhl hde hbc hram (by omega)
    rw [if_pos rfl] at hat1
    refine ⟨s1, st, hat1, M1, hsp, hr, by rw [hmem, set_size], fun x h1 h2 => ?_, fun x hx => ?_⟩
    · have : x = h + 1 := by omega
      rw [this, hmem, hz]
      exact getBang_same _ _ _ (by omega)
    · rw [hmem, getBang_set _ _ _ _ (by omega)]
  | succ n ih =>
    intro s h M hat hrs hhl hde hbc hram hb hz hsz
    obtain ⟨s1, st, M1, hsp, hr, hmem, hhl1, hde1, hbc1, hat1⟩ := ldir_round ok hk M hat hrs hhl hde hbc hram (by omega)
    rw [if_neg (by omega)] at hat1
    have hz1 : s1.mem.get! (h + 1) = 0 := by
      rw [hmem, hz]
      exact getBang_same _ _ _ (by omega)
    obtain ⟨s', st', at', M', hsp', hr', hsz', hzero, hkeep⟩ := ih s1 (h + 1) M1 hat1 (by rw [hr]; exact hrs) hhl1
      (by rw [hde1]; omega) hbc1 (by omega) (by omega) hz1 (by rw [hmem, set_size]; exact hsz)
    refine ⟨s', st.trans st', at', M', by rw [hsp', hsp], by rw [hr', hr], by rw [hsz', hmem, set_size],
      fun x h1 h2 => ?_, fun x hx => ?_⟩
    · by_cases hx : x = h + 1
      · rw [hx, hkeep (h + 1) (Or.inl (Nat.le_refl _)), hz1]
      · exact hzero x (by omega) (by omega)
    · rw [hkeep x (by omega), hmem, getBang_set _ _ _ _ (by omega)]

/-! ## Start-up: the RAM cleared -/

/-- `rt_zero`: `BC` (> 1) bytes of zero from `HL`. -/
def zeroItems : List Item :=
  [.label "rt_zero", .ins ⟨.ld, [.mhl, .imm (.num 0)]⟩, .ins ⟨.dec, [.bc]⟩, .ins ⟨.ld, [.a, .b]⟩, .ins ⟨.or, [.c]⟩,
   .ins ⟨.ret, [.z]⟩, .ins ⟨.ld, [.d, .h]⟩, .ins ⟨.ld, [.e, .l]⟩, .ins ⟨.inc, [.de]⟩, .ins ⟨.ldir, []⟩,
   .ins ⟨.ret, []⟩]

theorem mk16_zero {b c : UInt8} (h : (b ||| c == 0) = true) : mk16 b c = 0 := by
  have h' : b ||| c = 0 := by simpa using h
  have h0 : b.toNat ||| c.toNat = 0 := by
    have := congrArg UInt8.toNat h'
    rw [UInt8.toNat_or] at this
    exact this
  have h1 : b.toNat ≤ b.toNat ||| c.toNat := Nat.left_le_or
  have h2 : c.toNat ≤ b.toNat ||| c.toNat := Nat.right_le_or
  have hb : b = 0 := UInt8.toNat_inj.mp (by show b.toNat = 0; omega)
  have hc : c = 0 := UInt8.toNat_inj.mp (by show c.toNat = 0; omega)
  rw [hb, hc]
  rfl

def decBC (s : Cpu) : Cpu := ((op1 s).setRp .hl 0 ((op1 s).rp .hl 0 - 1)).tick 6
def incDE (s : Cpu) : Cpu := ((op1 s).setRp .hl 1 ((op1 s).rp .hl 1 + 1)).tick 6
def orC (s : Cpu) : Cpu := ((op1 s).alu 6 ((op1 s).reg .hl 1)).tick 4

theorem does_dec_bc : Does ⟨.dec, [.bc]⟩ decBC :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, decBC, Cpu.setRp, zsim, and_self],
    fun s => by simp only [decBC, Cpu.setRp, zsim]⟩
theorem does_inc_de : Does ⟨.inc, [.de]⟩ incDE :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, incDE, Cpu.setRp, zsim, and_self],
    fun s => by simp only [incDE, Cpu.setRp, zsim]⟩
theorem does_or_c : Does ⟨.or, [.c]⟩ orC :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, orC, zsim, and_self], fun s => by simp only [orC, zsim]⟩
theorem does_ld_a_b : Does ⟨.ld, [.a, .b]⟩ (ldRR 7 0) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldRR, zsim, and_self], fun s => by simp only [ldRR, zsim]⟩
theorem does_ld_d_h : Does ⟨.ld, [.d, .h]⟩ (ldRR 2 4) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldRR, zsim, and_self], fun s => by simp only [ldRR, zsim]⟩
theorem does_ld_e_l : Does ⟨.ld, [.e, .l]⟩ (ldRR 3 5) :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, ldRR, zsim, and_self], fun s => by simp only [ldRR, zsim]⟩

/-- **`rt_zero`**, entered at the item after its label with `HL = R`
and `BC = N` (at least two): the `N` bytes from `R` are zero when it
returns, and nothing else has changed. -/
theorem rt_zero_ok (ok : Z.OK) {k : Nat} (hhas : Has Z k zeroItems) {s : Cpu} {R N : Nat} (M : Mach Z s)
    (hat : At Z.addrs k s) (hrs : s.ramStart.toNat = Z.ramStart) (hsz : s.mem.size = 65536)
    (hhl : s.hl.toNat = R) (hbc : s.bc.toNat = N) (hN : 2 ≤ N) (hram : Z.ramStart ≤ R) (hb : R + N ≤ 65536) :
    ∃ s' sr, Steps s s' ∧ Mach Z sr ∧ sr.sp = s.sp ∧ sr.ramStart = s.ramStart ∧ sr.mem.size = 65536 ∧
      s'.pc = sr.rd16 sr.sp ∧ s'.sp = sr.sp + 2 ∧ s'.mem = sr.mem ∧ s'.halted = sr.halted ∧
      s'.ramStart = sr.ramStart ∧
      (∀ x, R ≤ x → x < R + N → sr.mem.get! x = 0) ∧ (∀ x, x < R ∨ R + N ≤ x → sr.mem.get! x = s.mem.get! x) := by
  have at1 := at_label ok (hhas.get 0 rfl) hat
  -- ld (hl),0
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = ((skip (op1 s) 1).wr (op1 s).hl (byteOf (Int.ofNat 0))).tick 10 := ⟨_, rfl⟩
  obtain ⟨st1, at2⟩ := step_raw ok (hhas.get 1 rfl) M at1 c1 (fun _ _ _ => by rw [hc1]; rfl)
    (by rw [hc1]; simp only [skip, zsim])
  have hmem1 : c1.mem = s.mem.set! R 0 := by
    rw [hc1]
    simp only [zsim]
    rw [cpu_wr_mem _ _ _ (by simp only [skip, zsim]; rw [hrs, hhl]; exact hram)]
    simp only [skip, zsim, hhl]
    rfl
  have hF1 : c1.ramStart = s.ramStart ∧ c1.halted = s.halted ∧ c1.sp = s.sp ∧ c1.h = s.h ∧ c1.l = s.l ∧
      c1.b = s.b ∧ c1.c = s.c := by
    rw [hc1]
    simp only [skip, zsim, and_self]
  have M1 : Mach Z c1 := by
    refine ⟨⟨by rw [hF1.1]; exact M.1.rom, fun x b hx => ?_⟩, by rw [hF1.2.1]; exact M.2⟩
    have hlt : x < Z.a.bytes.size := by
      rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hx; cases hx
    have hrom := M.1.rom
    have hb' := M.1.bytes x b hx
    rw [Nat.zero_add] at hb' ⊢
    rw [hmem1, getBang_set _ _ _ _ (by omega)]
    exact hb'
  have hbc1 : c1.bc = s.bc := by simp only [Cpu.bc, hF1.2.2.2.2.2.1, hF1.2.2.2.2.2.2]
  have hhl1 : c1.hl = s.hl := by simp only [Cpu.hl, hF1.2.2.2.1, hF1.2.2.2.2.1]
  -- dec bc; ld a,b; or c
  obtain ⟨st2, at3, M2, hS2⟩ := does_raw ok does_dec_bc (hhas.get 2 rfl) M1 (at2 rfl)
  obtain ⟨st3, at4, M3, hS3⟩ := does_raw ok does_ld_a_b (hhas.get 3 rfl) M2 at3
  obtain ⟨st4, at5, M4, hS4⟩ := does_raw ok does_or_c (hhas.get 4 rfl) M3 at4
  obtain ⟨c4, hc4⟩ : ∃ c4 : Cpu, c4 = orC (ldRR 7 0 (decBC c1)) := ⟨_, rfl⟩
  rw [← hc4] at st4 at5 M4 hS4
  have hbc2 : (decBC c1).bc = s.bc - 1 := by
    show mk16 _ _ = _
    simp only [decBC, Cpu.setRp, zsim]
    rw [hbc1]
    exact mk16_hi_lo _
  have hbcn : (s.bc - 1).toNat = N - 1 := by rw [sub1_toNat _ (by omega), hbc]
  have hfz : c4.flag FZ = false := by
    cases hfl : c4.flag FZ with
    | false => rfl
    | true =>
      have h1 : ((decBC c1).b ||| (decBC c1).c == 0) = true := by
        rw [← hfl, hc4]
        unfold orC
        rw [flag_tick, or_z]
        simp only [ldRR, zsim]
      have h2 : (decBC c1).bc = 0 := mk16_zero h1
      rw [hbc2] at h2
      have := congrArg UInt16.toNat h2
      rw [hbcn] at this
      have h0 : (0 : UInt16).toNat = 0 := rfl
      omega
  have hS14 : Sys c1 c4 := (hS2.trans hS3).trans (by rw [hc4]; rw [hc4] at hS4; exact hS4)
  -- ret z: not taken
  obtain ⟨ad, had, hpcad⟩ := at5
  obtain ⟨c5, hc5⟩ : ∃ c5 : Cpu, c5 = (op1 c4).tick 5 := ⟨_, rfl⟩
  have hst5 := fun inp => (step_item ok.placed M4.1 (hhas.get 5 rfl) had hpcad M4.2 (inp := inp) (s' := c5) (by
    rw [hc5]
    show (some (if (op1 c4).cond 1 = true then (retTo (op1 c4)).tick 11 else (op1 c4).tick 5) : Option Cpu) = _
    rw [cond_op1]
    show (some (if c4.flag FZ = true then _ else _) : Option Cpu) = _
    rw [hfz]
    rfl)).1
  have st5 : Steps c4 c5 := Steps.one hst5 (by rw [hc5]; simp only [zsim])
  have hS5 : Sys c4 c5 := by rw [hc5]; simp only [Sys, zsim, and_self]
  have M5 := M4.sys hS5
  obtain ⟨bs, hbs, hnext, hlt65⟩ := ok.placed.next M4.1 (hhas.get 5 rfl) had
  have hbs' : bs = [0xC8] := by
    have : Item.encode (.ins ⟨.ret, [.z]⟩) (Z.a.env ad) = .ok [0xC8] := rfl
    rw [this] at hbs
    exact (Except.ok.inj hbs).symm
  have at6 : At Z.addrs (k + 6) c5 := by
    refine ⟨ad + 1, by rw [hbs'] at hnext; exact hnext, ?_⟩
    have hb1 := hlt65 (by rw [hbs']; exact List.cons_ne_nil _ _)
    rw [hbs'] at hb1
    have hb1' : ad + 1 < 65536 := hb1
    rw [hc5]
    simp only [zsim]
    rw [UInt16.toNat_add, hpcad]
    show (ad + 1) % 65536 = ad + 1
    omega
  -- ld d,h; ld e,l; inc de
  obtain ⟨st6, at7, M6, hS6⟩ := does_raw ok does_ld_d_h (hhas.get 6 rfl) M5 at6
  obtain ⟨st7, at8, M7, hS7⟩ := does_raw ok does_ld_e_l (hhas.get 7 rfl) M6 at7
  obtain ⟨st8, at9, M8, hS8⟩ := does_raw ok does_inc_de (hhas.get 8 rfl) M7 at8
  obtain ⟨c8, hc8⟩ : ∃ c8 : Cpu, c8 = incDE (ldRR 3 5 (ldRR 2 4 c5)) := ⟨_, rfl⟩
  rw [← hc8] at st8 at9 M8 hS8
  have hS58 : Sys c5 c8 := (hS6.trans hS7).trans (by rw [hc8]; rw [hc8] at hS8; exact hS8)
  have hS18 : Sys c1 c8 := (hS14.trans hS5).trans hS58
  have hhl8 : c8.hl = s.hl := by
    rw [← hhl1, hc8, hc5, hc4]
    show mk16 _ _ = mk16 _ _
    simp only [incDE, ldRR, orC, decBC, Cpu.setRp, zsim]
  have hbc8 : c8.bc = s.bc - 1 := by
    rw [← hbc2, hc8, hc5, hc4]
    show mk16 _ _ = mk16 _ _
    simp only [incDE, ldRR, orC, decBC, Cpu.setRp, zsim]
  have hde8 : c8.de = s.hl + 1 := by
    rw [← hhl1, hc8, hc5, hc4]
    show mk16 _ _ = _
    simp only [incDE, ldRR, orC, decBC, Cpu.setRp, zsim]
    rw [mk16_hi_lo]
    show mk16 _ _ + 1 = mk16 _ _ + 1
    simp only [zsim]
  -- ldir
  have hmem8 : c8.mem = s.mem.set! R 0 := by rw [hS18.1, hmem1]
  have hsz8 : c8.mem.size = 65536 := by rw [hmem8, set_size]; exact hsz
  obtain ⟨s9, st9, at10, M9, hsp9, hr9, hsz9, hzero, hkeep⟩ := ldir_zero ok (hhas.get 9 rfl) (N - 2) c8 R M8 at9
    (by rw [hS18.2.1, hF1.1]; exact hrs) (by rw [hhl8]; exact hhl)
    (by rw [hde8, UInt16.toNat_add, hhl]; show (R + 1) % 65536 = _; omega)
    (by rw [hbc8, hbcn]; omega) hram (by omega) (by rw [hmem8]; exact getBang_same _ _ _ (by omega)) hsz8
  obtain ⟨s', st10, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 10 rfl) M9 at10
  refine ⟨s', s9, (((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st8).trans st9)).trans st10,
    M9, by rw [hsp9, hS18.2.2.2, hF1.2.2.1], by rw [hr9, hS18.2.1, hF1.1], by rw [hsz9]; exact hsz8, hpc', hsp', hmem',
    hh', hrs', fun x h1 h2 => ?_, fun x hx => ?_⟩
  · by_cases hx : x = R
    · rw [hx, hkeep R (Or.inl (Nat.le_refl _)), hmem8]
      exact getBang_same _ _ _ (by omega)
    · exact hzero x (by omega) (by omega)
  · rw [hkeep x (by omega), hmem8, getBang_set _ _ _ _ (by omega)]

/-- `ld sp,nn` as the model runs it. -/
def ldSP (v : UInt16) (s : Cpu) : Cpu := ({ (skip (op1 s) 2) with sp := v } : Cpu).tick 10

/-- The harness's start-up, and `rt_init` of a program without initial values. -/
def startItems : List Item :=
  [.label "rt_start", .ins ⟨.di, []⟩, .ins ⟨.ld, [.sp, .imm (.num 0)]⟩, .ins ⟨.call, [.imm (.sym "rt_init")]⟩]

def initItems : List Item :=
  [.label "rt_init", .ins ⟨.ld, [.hl, .imm (.sym "rt_ram")]⟩, .ins ⟨.ld, [.bc, .imm (.sym "rt_ram_size")]⟩,
   .ins ⟨.call, [.imm (.sym "rt_zero")]⟩, .ins ⟨.ret, []⟩]

/-- Items that are names only take no room: the CPU at the first is at the item after them. -/
theorem at_skip_equs (ok : Z.OK) {s : Cpu} : ∀ (n : Nat), (∀ i, i < n → ∃ name v, Z.items[i]? = some (.equ name v)) →
    At Z.addrs 0 s → At Z.addrs n s
  | 0, _, h => h
  | n + 1, hall, h => by
    obtain ⟨name, v, hi⟩ := hall n (Nat.lt_succ_self n)
    exact at_skip ok.placed hi (fun _ => rfl) (at_skip_equs ok n (fun i hi' => hall i (by omega)) h)

/-- What start-up needs of the image. -/
structure BootNeed (Z : ZCtx) (kH kS kI kZ R N : Nat) : Prop where
  /-- The image begins with names, then the jump to `rt_start`. -/
  head : ∀ i, i < kH → ∃ name v, Z.items[i]? = some (.equ name v)
  jump : Z.items[kH]? = some (.ins ⟨.jp, [.imm (.sym "rt_start")]⟩)
  start : Has Z kS startItems
  init : Has Z kI initItems
  zero : Has Z kZ zeroItems
  ram : Z.sym "rt_ram" R
  ramSize : Z.sym "rt_ram_size" N
  /-- The RAM in use: at least two bytes, in RAM, below the four bytes of stack start-up uses. -/
  n2 : 2 ≤ N
  lo : Z.ramStart ≤ R
  hi : R + N ≤ 65532
  stackLo : Z.stackLo ≤ 65532
  stackHi : Z.stackHi = 65536
  size : Z.a.bytes.size < 65536

/-- **Start-up**: from reset the CPU gets to the item after the call of
`rt_init` (the head of the loop), its stack empty, the RAM in use zero. -/
theorem boot_ok (ok : Z.OK) {kH kS kI kZ R N : Nat} (B : BootNeed Z kH kS kI kZ R N) {s : Cpu}
    (hpc : s.pc.toNat = 0) (I : Img Z.a 0 s) (hh : s.halted = false) (hrs : s.ramStart.toNat = Z.ramStart)
    (hsz : s.mem.size = 65536) :
    ∃ s', Steps s s' ∧ At Z.addrs (kS + 4) s' ∧ Img Z.a 0 s' ∧ s'.halted = false ∧
      s'.ramStart.toNat = Z.ramStart ∧ s'.mem.size = 65536 ∧ s'.sp = 0 ∧
      ∀ x, R ≤ x → x < R + N → s'.mem.get! x = 0 := by
  have hstk := ok.stack
  have hlo := B.lo
  have hhi := B.hi
  have hslo := B.stackLo
  have hshi := B.stackHi
  have hn2 := B.n2
  have hsize := B.size
  have M : Mach Z s := ⟨I, hh⟩
  -- the jump at the reset address
  have at0 : At Z.addrs 0 s := ⟨0, ok.placed.1, hpc⟩
  have atH := at_skip_equs ok kH B.head at0
  obtain ⟨c0, st0, atS, M0, hS0, _⟩ := jp_step ok B.jump (B.start.get 0 rfl) M atH
  have at1 := at_label ok (B.start.get 0 rfl) atS
  -- di; ld sp,0
  obtain ⟨c1, st1, at2, M1, hS1⟩ := sys_step ok (B.start.get 1 rfl) rfl M0 at1
    (fun ad => ⟨_, fun _ => rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩)
  obtain ⟨ad2, had2, hpc2⟩ := at2
  obtain ⟨c2, hc2⟩ : ∃ c2 : Cpu, c2 = ldSP (Instr.immW (Z.a.env ad2) ⟨.ld, [.sp, .imm (.num 0)]⟩) c1 := ⟨_, rfl⟩
  obtain ⟨st2, at3⟩ := step_raw ok (B.start.get 2 rfl) M1 ⟨ad2, had2, hpc2⟩ c2 (fun ad' had' _ => by
    rw [had2] at had'
    cases had'
    rw [hc2]
    rfl) (by rw [hc2]; rfl)
  have hF2 : c2.mem = c1.mem ∧ c2.ramStart = c1.ramStart ∧ c2.halted = c1.halted ∧ c2.sp = 0 := by
    rw [hc2]
    refine ⟨rfl, rfl, rfl, ?_⟩
    apply UInt16.toNat_inj.mp
    show (Instr.immW (Z.a.env ad2) ⟨.ld, [.sp, .imm (.num 0)]⟩).toNat = 0
    exact immW_toNat _ _ _ 0 rfl rfl (by decide)
  have hS02 : c2.mem = s.mem ∧ c2.ramStart = s.ramStart ∧ c2.halted = s.halted := by
    refine ⟨by rw [hF2.1, hS1.1, hS0.1], by rw [hF2.2.1, hS1.2.1, hS0.2.1], by rw [hF2.2.2.1, hS1.2.2.1, hS0.2.2.1]⟩
  have M2 : Mach Z c2 := ⟨I.congr hS02.2.1 hS02.1, by rw [hS02.2.2]; exact hh⟩
  have hrs2 : c2.ramStart.toNat = Z.ramStart := by rw [hS02.2.1]; exact hrs
  have hsz2 : c2.mem.size = 65536 := by rw [hS02.1]; exact hsz
  -- call rt_init
  obtain ⟨TI, hTI, hsymI, hTIle⟩ := label_sym ok (B.init.get 0 rfl)
  obtain ⟨c3, st3, hsp3, hpc3, I3, hh3, hrs3, hsz3, hmem3, hback3⟩ := call_top ok (B.start.get 3 rfl) hsymI (by omega)
    (at3 rfl) M2.1 M2.2 hrs2 hsz2 hF2.2.2.2 (by omega)
  have M3 : Mach Z c3 := ⟨I3, hh3⟩
  have atI1 := at_label ok (B.init.get 0 rfl) ⟨TI, hTI, hpc3⟩
  -- ld hl,rt_ram
  obtain ⟨ad4, had4, hpc4⟩ := atI1
  obtain ⟨c4, hc4⟩ : ∃ c4 : Cpu, c4 = ((skip (op1 c3) 2).setHL
      (Instr.immW (Z.a.env ad4) ⟨.ld, [.hl, .imm (.sym "rt_ram")]⟩)).tick 10 := ⟨_, rfl⟩
  have hnn4 : (Instr.immW (Z.a.env ad4) ⟨.ld, [.hl, .imm (.sym "rt_ram")]⟩).toNat = R :=
    immW_toNat _ _ _ _ rfl (sym_val ad4 B.ram) (by omega)
  obtain ⟨st4, at5⟩ := step_raw ok (B.init.get 1 rfl) M3 ⟨ad4, had4, hpc4⟩ c4 (fun ad' had' inp => by
    rw [had4] at had'
    cases had'
    rw [hc4]
    rfl) (by rw [hc4]; simp only [zsim])
  have hS4 : Sys c3 c4 := by rw [hc4]; simp only [Sys, skip, zsim, and_self]
  have hhl4 : c4.hl.toNat = R := by rw [hc4]; simp only [zsim]; exact hnn4
  have M4 := M3.sys hS4
  -- ld bc,rt_ram_size
  obtain ⟨ad5, had5, hpc5⟩ := at5 rfl
  obtain ⟨c5, hc5⟩ : ∃ c5 : Cpu, c5 = ((skip (op1 c4) 2).setRp .hl 0
      (Instr.immW (Z.a.env ad5) ⟨.ld, [.bc, .imm (.sym "rt_ram_size")]⟩)).tick 10 := ⟨_, rfl⟩
  have hnn5 : (Instr.immW (Z.a.env ad5) ⟨.ld, [.bc, .imm (.sym "rt_ram_size")]⟩).toNat = N :=
    immW_toNat _ _ _ _ rfl (sym_val ad5 B.ramSize) (by omega)
  obtain ⟨st5, at6⟩ := step_raw ok (B.init.get 2 rfl) M4 ⟨ad5, had5, hpc5⟩ c5 (fun ad' had' inp => by
    rw [had5] at had'
    cases had'
    rw [hc5]
    rfl) (by rw [hc5]; simp only [Cpu.setRp, zsim])
  have hS5 : Sys c4 c5 := by rw [hc5]; simp only [Sys, Cpu.setRp, skip, zsim, and_self]
  have hbc5 : c5.bc.toNat = N := by
    rw [hc5]
    show (mk16 _ _).toNat = _
    simp only [Cpu.setRp, zsim]
    rw [mk16_hi_lo]
    exact hnn5
  have hhl5 : c5.hl.toNat = R := by
    rw [← hhl4, hc5]
    show (mk16 _ _).toNat = (mk16 _ _).toNat
    simp only [Cpu.setRp, skip, zsim]
  have M5 := M4.sys hS5
  have hS35 : Sys c3 c5 := hS4.trans hS5
  have hsp5 : c5.sp.toNat = 65534 := by rw [hS35.2.2.2]; exact hsp3
  have hrs5 : c5.ramStart.toNat = Z.ramStart := by rw [hS35.2.1, hrs3]; exact hrs2
  have hsz5 : c5.mem.size = 65536 := by rw [hS35.1]; exact hsz3
  -- call rt_zero
  obtain ⟨TZ, hTZ, hsymZ, hTZle⟩ := label_sym ok (B.zero.get 0 rfl)
  obtain ⟨c6, st6, cs6, hpc6, I6, hh6, hrs6, hback6⟩ := call_step ok (B.init.get 3 rfl) hsymZ (by omega) (at6 rfl)
    M5.1 M5.2 hrs5 hsz5 (by omega) (by omega)
  have hsp6 : c6.sp.toNat = 65532 := by rw [cs6.sp, sub2_toNat _ (by omega), hsp5]
  obtain ⟨s7, sr, st7, Mr, hspr, hrsr, hszr, hpc7, hsp7, hmem7, hh7, hrs7, hzero, hkeep⟩ :=
    rt_zero_ok ok B.zero ⟨I6, hh6⟩ ⟨TZ, hTZ, hpc6⟩ (by rw [hrs6]; exact hrs5) (by rw [cs6.size]; exact hsz5)
      (by rw [hl_congr cs6.h cs6.l]; exact hhl5) (by rw [bc_congr cs6.b cs6.c]; exact hbc5) hn2 hlo (by omega)
  -- back in rt_init: ret
  have hsr : sr.sp.toNat = 65532 := by rw [hspr]; exact hsp6
  have at7 : At Z.addrs (kI + 4) s7 := hback6 s7 (by
    rw [hpc7, cpu_rd16 _ _ (by rw [hsr]; omega), hsr, hsp5]
    exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hkeep x (Or.inr (by omega))))
  have M7 : Mach Z s7 := ⟨Mr.1.congr hrs7 hmem7, by rw [hh7]; exact Mr.2⟩
  obtain ⟨s8, st8, hpc8, hsp8, hmem8, hh8, hrs8, _, _, _⟩ := ret_raw ok (B.init.get 4 rfl) M7 at7
  have hsp7' : s7.sp.toNat = 65534 := by
    rw [hsp7, UInt16.toNat_add, hsr]
    rfl
  have hmem78 : ∀ x, 65534 ≤ x → s7.mem.get! x = c3.mem.get! x := by
    intro x hx
    rw [hmem7, hkeep x (Or.inr (by omega)), cs6.mem x (Or.inr (by omega)), hS35.1]
  refine ⟨s8, ((((((((st0.trans st1).trans st2).trans st3).trans st4).trans st5).trans st6).trans st7)).trans st8, ?_,
    M7.1.congr hrs8 hmem8, by rw [hh8]; exact M7.2, ?_, by rw [hmem8, hmem7]; exact hszr, ?_, ?_⟩
  · exact hback3 s8 (by
      rw [hpc8, cpu_rd16 _ _ (by rw [hsp7']; omega), hsp7']
      exact rd_congr _ _ _ _ (by omega) (fun x h1 h2 => hmem78 x h1))
  · rw [hrs8, hrs7, hrsr, hrs6]
    exact hrs5
  · apply UInt16.toNat_inj.mp
    rw [hsp8, UInt16.toNat_add, hsp7']
    rfl
  · intro x h1 h2
    rw [hmem8, hmem7]
    exact hzero x h1 h2

/-- **`di; halt`**: the CPU stops — halted, interrupts off, memory as it was. -/
theorem di_halt (ok : Z.OK) {k : Nat} (h1 : Z.items[k]? = some (.ins ⟨.di, []⟩))
    (h2 : Z.items[k + 1]? = some (.ins ⟨.halt, []⟩)) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ s'.halted = true ∧ s'.iff1 = false ∧ s'.mem = s.mem := by
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = ({ (op1 s) with iff1 := false, iff2 := false } : Cpu).tick 4 := ⟨_, rfl⟩
  obtain ⟨st1, at2⟩ := step_raw ok h1 M hat c1 (fun _ _ _ => by rw [hc1]; rfl) (by rw [hc1]; rfl)
  have M1 : Mach Z c1 := M.sys (by rw [hc1]; exact ⟨rfl, rfl, rfl, rfl⟩)
  obtain ⟨c2, hc2⟩ : ∃ c2 : Cpu, c2 = ({ (op1 c1) with halted := true } : Cpu).tick 4 := ⟨_, rfl⟩
  obtain ⟨st2, _⟩ := step_raw ok h2 M1 (at2 rfl) c2 (fun _ _ _ => by rw [hc2]; rfl) (by rw [hc2]; rfl)
  exact ⟨c2, st1.trans st2, by rw [hc2]; rfl, by rw [hc2, hc1]; rfl, by rw [hc2, hc1]; rfl⟩

theorem cpN_c (v : Nat) (hv : v < 256) (s : Cpu) : (cpN v s).flag FC = decide (s.a.toNat < v) := by
  unfold cpN
  rw [flag_tick, cp_c]
  simp only [skip, zsim]
  have e : (byteOf (Int.ofNat (v % 256))).toNat = v := by
    rw [byteOf_toNat]
    show (((v % 256 : Nat) : Int) % 256).toNat = v
    omega
  rw [e]
  congr

end

end Ember.Proof.Z80Gen
