import Ember.Proof.Z80Instr

/-!
# Ember.Proof.Z80Call — calling a routine of the image (plan M7.3)

`Routine Z entry K P Q`: entered at `entry` with a return address on the
stack and `K` bytes of stack below it, from a state with `P`, the code
returns — the program counter at the return address, the stack pointer
after it — in a state with `Q`.  The routines of the runtime are taken
with such specifications; a function of the program will have one by
the theorem about functions.

`call_rule`: a `call` item, the routine, and the return, as one step of
the caller.  `Rel.free_stack`: the states still agree when only the free
part of the stack (below the stack pointer) has changed.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Z80.IR (Opd Dst Slot Area)

def Routine (Z : ZCtx) (entry K : Nat) (P : Cpu → Prop) (Q : Cpu → Cpu → Prop) : Prop :=
  ∀ s, s.pc.toNat = entry → Img Z.a 0 s → s.halted = false → s.ramStart.toNat = Z.ramStart →
    s.mem.size = 65536 → Z.stackLo + K ≤ s.sp.toNat → s.sp.toNat + 2 ≤ Z.stackHi → P s →
    ∃ s', Steps Z.inp s s' ∧ s'.pc = s.rd16 s.sp ∧ s'.sp = s.sp + 2 ∧ s'.halted = false ∧
      s'.ramStart = s.ramStart ∧ s'.mem.size = 65536 ∧ Q s s'

/-- The state a `call` leaves: the registers as they were, the return
address pushed. -/
structure CallSt (s s1 : Cpu) : Prop where
  a : s1.a = s.a
  f : s1.f = s.f
  b : s1.b = s.b
  c : s1.c = s.c
  d : s1.d = s.d
  e : s1.e = s.e
  h : s1.h = s.h
  l : s1.l = s.l
  sp : s1.sp = s.sp - 2
  mem : ∀ x, x < s.sp.toNat - 2 ∨ s.sp.toNat ≤ x → s1.mem.get! x = s.mem.get! x
  size : s1.mem.size = s.mem.size

section
variable {Z : ZCtx} {E : GEnv} {dt : Nat → Prop} {fr : Fr}

theorem sub2_toNat (x : UInt16) (h : 2 ≤ x.toNat) : (x - 2).toNat = x.toNat - 2 := by
  have := x.toNat_lt
  rw [UInt16.toNat_sub]
  show (2 ^ 16 - 2 + x.toNat) % 2 ^ 16 = _
  omega

/-- What a push writes. -/
theorem push_mem (X : Cpu) (v : UInt16) (h2 : 2 ≤ X.sp.toNat) (hram : X.ramStart.toNat + 2 ≤ X.sp.toNat) :
    (X.push v).mem = IR.Sem.wr X.mem (X.sp.toNat - 2) 2 v.toNat := by
  have hsp := X.sp.toNat_lt
  have ha : (X.sp - 2).toNat = X.sp.toNat - 2 := sub2_toNat _ h2
  have ha1 : (X.sp - 2 + 1).toNat = X.sp.toNat - 2 + 1 := by
    rw [UInt16.toNat_add, ha]
    show (X.sp.toNat - 2 + 1) % 65536 = _
    omega
  simp only [Cpu.push, Cpu.wr16]
  rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [ha1]; omega), cpu_wr_mem _ _ _ (by rw [ha]; show X.ramStart.toNat ≤ _; omega)]
  rw [ha, ha1]
  refine wr_two _ _ _ (by omega) _ _ ?_ ?_
  · rw [UInt16.toNat_toUInt8]
  · rw [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]
    rw [show (8 : UInt16).toNat % 16 = 8 from rfl, Nat.shiftRight_eq_div_pow]

theorem sym_val (pc : Nat) {name : String} {entry : Nat} (h : Z.sym name entry) :
    (Z.a.env pc).val (.sym name 0) = Int.ofNat entry := by
  unfold ZCtx.sym at h
  rw [val_sym _ _ _ (Int.ofNat entry) (by simp [Assembled.env, h])]
  simp

theorem call_len {env : Env} {v : Val} {bs : List UInt8}
    (h : encode ⟨.call, [.imm v]⟩ env = .ok bs) : bs.length = 3 := by
  have h' : (encode' ⟨.call, [.imm v]⟩).run env = .ok bs := by
    unfold encode at h
    split at h
    · rename_i bs' hb
      cases h
      exact hb
    · cases h
  have he' : ((imm16 v).run env).bind (fun l => .ok ([0xCD] ++ l)) = Except.ok bs := h'
  obtain ⟨l, hl, hb⟩ := bind_ok he'
  obtain rfl := imm16_bytes hl
  cases hb
  rfl

/-- A write to RAM leaves the image. -/
theorem Img.of_wr {a : Assembled} {s s' : Cpu} (I : Img a 0 s) (hr : s'.ramStart = s.ramStart) {x n v : Nat}
    (hm : s'.mem = IR.Sem.wr s.mem x n v) (hx : s.ramStart.toNat ≤ x) (hb : x + n ≤ 65536) : Img a 0 s' := by
  refine ⟨by rw [hr]; exact I.rom, fun y b hy => ?_⟩
  have hlt : y < a.bytes.size := by
    rcases Nat.lt_or_ge y a.bytes.data.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hy; cases hy
  have hrom := I.rom
  rw [hm, wr_get_far _ _ _ _ _ hb (by omega)]
  exact I.bytes y b hy

/-- **The `call` item**: the return address pushed, the CPU at the entry;
whatever then gets to the return address is at the item after the call. -/
theorem call_step (ok : Z.OK) {k : Nat} {name : String} {entry : Nat}
    (hk : Z.items[k]? = some (.ins ⟨.call, [.imm (.sym name)]⟩)) (hsym : Z.sym name entry) (hent : entry < 65536)
    {s : Cpu} (hat : At Z.addrs k s) (I : Img Z.a 0 s) (hh : s.halted = false)
    (hrs : s.ramStart.toNat = Z.ramStart) (hsz : s.mem.size = 65536)
    (hroom : Z.stackLo + 2 ≤ s.sp.toNat) (htop : s.sp.toNat ≤ Z.stackHi) :
    ∃ s1, Steps Z.inp s s1 ∧ CallSt s s1 ∧ s1.pc.toNat = entry ∧ Img Z.a 0 s1 ∧ s1.halted = false ∧
      s1.ramStart = s.ramStart ∧
      ∀ s' : Cpu, s'.pc.toNat = IR.Sem.rd s1.mem (s.sp.toNat - 2) 2 → At Z.addrs (k + 1) s' := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hstk := ok.stack
  have hspl := s.sp.toNat_lt
  have hnn : (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩).toNat = entry :=
    immW_toNat _ _ _ _ rfl (sym_val ad hsym) hent
  obtain ⟨hst, _⟩ := step_item ok.placed I hk had hpc hh (inp := Z.inp)
    (s' := (callTo (skip (op1 s) 2) (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩)).tick 17) rfl
  have hpm := push_mem (skip (op1 s) 2) (skip (op1 s) 2).pc (by simp only [zsim]; omega)
    (by simp only [zsim]; omega)
  simp only [zsim] at hpm
  have hmem1 : ((callTo (skip (op1 s) 2) (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩)).tick 17).mem =
      IR.Sem.wr s.mem (s.sp.toNat - 2) 2 (s.pc + 1 + 2).toNat := by
    simp only [callTo, zsim]
    exact hpm
  have hsp1 : ((callTo (skip (op1 s) 2) (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩)).tick 17).sp =
      s.sp - 2 := by
    simp only [callTo, zsim]
  have cs : CallSt s ((callTo (skip (op1 s) 2) (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩)).tick 17) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsp1, fun x hx => ?_, ?_⟩
    all_goals try (simp only [callTo, zsim]; done)
    · rw [hmem1, wr_get_far _ _ _ _ _ (by omega) (by omega)]
    · rw [hmem1, wr_size]
  refine ⟨_, Steps.one hst, cs, by simp only [callTo, zsim]; exact hnn,
    Img.of_wr I (by simp only [callTo, zsim]) hmem1 (by omega) (by omega),
    by simp only [callTo, zsim]; exact hh, by simp only [callTo, zsim], fun s' hpc' => ?_⟩
  obtain ⟨bs, hbs, hnext, hlt⟩ := ok.placed.next I hk had
  have hlen := call_len hbs
  refine ⟨ad + bs.length, hnext, ?_⟩
  rw [hpc', hmem1, rd_wr _ _ _ _ (by rw [hsz]; omega) (by rw [hsz]; exact Nat.le_refl _)]
  have hlt' := hlt (by intro e; rw [e] at hlen; cases hlen)
  have : (s.pc + 1 + 2).toNat = ad + 3 := by
    rw [UInt16.toNat_add, UInt16.toNat_add, hpc]
    show ((ad + 1) % 65536 + 2) % 65536 = _
    omega
  rw [this, hlen]
  show (ad + 3) % 65536 = _
  omega

/-- **A call**: the `call` item, the routine and its return. -/
theorem call_rule (ok : Z.OK) {k : Nat} {name : String} {entry K : Nat} {P : Cpu → Prop} {Q : Cpu → Cpu → Prop}
    (hk : Z.items[k]? = some (.ins ⟨.call, [.imm (.sym name)]⟩)) (hsym : Z.sym name entry) (hent : entry < 65536)
    (hR : Routine Z entry K P Q) {s : Cpu} (hat : At Z.addrs k s) (I : Img Z.a 0 s) (hh : s.halted = false)
    (hrs : s.ramStart.toNat = Z.ramStart) (hsz : s.mem.size = 65536)
    (hroom : Z.stackLo + K + 2 ≤ s.sp.toNat) (htop : s.sp.toNat ≤ Z.stackHi)
    (hP : ∀ s1, CallSt s s1 → P s1) :
    ∃ s1 s', CallSt s s1 ∧ Steps Z.inp s s' ∧ At Z.addrs (k + 1) s' ∧ s'.sp = s.sp ∧ s'.halted = false ∧
      s'.ramStart = s.ramStart ∧ s'.mem.size = 65536 ∧ Q s1 s' := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hstk := ok.stack
  have hspl := s.sp.toNat_lt
  -- the call
  have hnn : (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩).toNat = entry :=
    immW_toNat _ _ _ _ rfl (sym_val ad hsym) hent
  obtain ⟨hst, _⟩ := step_item ok.placed I hk had hpc hh (inp := Z.inp)
    (s' := (callTo (skip (op1 s) 2) (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩)).tick 17) rfl
  have hpm := push_mem (skip (op1 s) 2) (skip (op1 s) 2).pc (by simp only [zsim]; omega)
    (by simp only [zsim]; omega)
  simp only [zsim] at hpm
  have hmem1 : ((callTo (skip (op1 s) 2) (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩)).tick 17).mem =
      IR.Sem.wr s.mem (s.sp.toNat - 2) 2 (s.pc + 1 + 2).toNat := by
    simp only [callTo, zsim]
    exact hpm
  have hsp1 : ((callTo (skip (op1 s) 2) (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩)).tick 17).sp =
      s.sp - 2 := by
    simp only [callTo, zsim]
  have hsp1n : (s.sp - 2).toNat = s.sp.toNat - 2 := sub2_toNat _ (by omega)
  have cs : CallSt s ((callTo (skip (op1 s) 2) (Instr.immW (Z.a.env ad) ⟨.call, [.imm (.sym name)]⟩)).tick 17) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsp1, fun x hx => ?_, ?_⟩
    all_goals try (simp only [callTo, zsim]; done)
    · rw [hmem1, wr_get_far _ _ _ _ _ (by omega) (by omega)]
    · rw [hmem1, wr_size]
  -- the routine
  obtain ⟨s', hst', hpc', hsp', hh', hrs', hsz', hQ⟩ := hR _
    (by simp only [callTo, zsim]; exact hnn)
    (Img.of_wr I (by simp only [callTo, zsim]) hmem1 (by omega) (by omega))
    (by simp only [callTo, zsim]; exact hh) (by simp only [callTo, zsim]; exact hrs)
    (by rw [hmem1, wr_size]; exact hsz) (by rw [hsp1, hsp1n]; omega) (by rw [hsp1, hsp1n]; omega) (hP _ cs)
  refine ⟨_, s', cs, (Steps.one hst).trans hst', ?_, ?_, hh', ?_, hsz', hQ⟩
  · -- back at the item after the call
    obtain ⟨bs, hbs, hnext, hlt⟩ := ok.placed.next I hk had
    have hlen := call_len hbs
    refine ⟨ad + bs.length, hnext, ?_⟩
    rw [hpc', hsp1, cpu_rd16 _ _ (by rw [hsp1n]; omega), hmem1, hsp1n,
      rd_wr _ _ _ _ (by rw [hsz]; omega) (by rw [hsz]; exact Nat.le_refl _)]
    have hlt' := hlt (by intro e; rw [e] at hlen; cases hlen)
    have : (s.pc + 1 + 2).toNat = ad + 3 := by
      rw [UInt16.toNat_add, UInt16.toNat_add, hpc]
      show ((ad + 1) % 65536 + 2) % 65536 = _
      omega
    rw [this, hlen]
    show (ad + 3) % 65536 = _
    omega
  · rw [hsp', hsp1]
    exact UInt16.sub_add_cancel _ _
  · rw [hrs']
    simp only [callTo, zsim]

/-! ## The free part of the stack -/

/-- Only the stack below `s`'s stack pointer may differ in `s'`. -/
def FreeStack (Z : ZCtx) (s s' : Cpu) : Prop :=
  ∀ x, x < Z.stackLo ∨ s.sp.toNat ≤ x → s'.mem.get! x = s.mem.get! x

/-- The states agree again when only the free part of the stack changed. -/
theorem Rel.free_stack (ok : Z.OK) (hT : FnLay Z E) {regs regs' : Regs} {ist : IR.Sem.St} {tmps : Array Nat}
    {s s' : Cpu} (R : Rel Z E fr dt regs ist tmps s) (hm : FreeStack Z s s') (hsz : s'.mem.size = 65536)
    (hr : s'.ramStart = s.ramStart) (hh : s'.halted = s.halted) (hsp : s'.sp = s.sp)
    (ha : ∀ o, o ∈ regs'.a → Own E o → s'.a.toNat = IR.Sem.opd Z.c ist tmps 1 o)
    (hhl : ∀ o, o ∈ regs'.hl → Own E o → s'.hl.toNat = IR.Sem.opd Z.c ist tmps 2 o)
    (hina : ∀ sl, Opd.slot sl ∈ regs'.a → Own E (.slot sl) → Z.use (sl, 1))
    (hinhl : ∀ sl, Opd.slot sl ∈ regs'.hl → Own E (.slot sl) → Z.use (sl, 2))
    (hacc : ∀ n o, regs'.acc = some (n, o) → regs.acc = some (n, o)) :
    Rel Z E fr dt regs' ist tmps s' := by
  have hstk := ok.stack
  have hroom := R.room
  have hspv : s.sp.toNat = fr.sp.toNat := by rw [R.sp]
  have himg : ∀ x b, Z.a.bytes.data[x]? = some b → s'.mem.get! (0 + x) = b := by
    intro x b hx
    have hlt : x < Z.a.bytes.size := by
      rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hx; cases hx
    have hrom := R.img.rom
    have hrs := R.rs
    rw [Nat.zero_add, hm x (by omega)]
    simpa using R.img.bytes x b hx
  have hmem : ∀ x, Z.data x → s'.mem.get! x = ist.mem.get! x := by
    intro x hx
    rw [hm x (by have := ok.nostack x hx; omega)]
    exact R.mem x hx
  have htmp : ∀ t, dt t → E.spilled[t]! = true →
      IR.Sem.rd s'.mem (tmpAddr Z E t) (E.fn.tmps[t]!) = tmps.getD t 0 := by
    intro t h1 h2
    rw [← R.tmp t h1 h2]
    refine rd_congr _ _ _ _ (hT.bound t h2) (fun x hx1 hx2 => hm x ?_)
    have := hT.nostack t h2
    omega
  have hstk' : ∀ x, fr.sp.toNat ≤ x → x < Z.stackHi → s'.mem.get! x = fr.mem.get! x := by
    intro x h1 h2
    rw [hm x (by omega)]
    exact R.stk x h1 h2
  have hout : ∀ x, ¬ Z.wr E.fn.name x → s'.mem.get! x = fr.mem.get! x := by
    intro x hx
    rw [hm x ?_]
    · exact R.out x hx
    · rcases Nat.lt_or_ge x Z.stackLo with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge x Z.stackHi with h' | h'
        · exact absurd (ok.wrStack _ x h h') hx
        · exact Or.inr (by omega)
  have hacc' : ∀ n o, regs'.acc = some (n, o) → Own E o →
      IR.Sem.rd s'.mem Z.acc n = IR.Sem.opd Z.c ist tmps n o := by
    intro n o h hown
    have h8 := R.nacc n o (hacc n o h)
    have hacr := ok.accRam
    rw [← R.racc n o (hacc n o h) hown]
    refine rd_congr _ _ _ _ (by omega) (fun x hx1 hx2 => hm x ?_)
    have := ok.accStack
    omega
  exact ⟨⟨by rw [hr]; exact R.img.rom, himg⟩, by rw [hh]; exact R.run, hmem, htmp, by rw [hr]; exact R.rs, hsz,
    R.isz, R.tsz, by rw [hsp]; exact R.sp, R.room, hstk', hout, ha, hhl, hacc', hina, hinhl,
    fun n sl h hown => R.inacc n sl (hacc _ _ h) hown, fun n o h => R.nacc n o (hacc n o h)⟩

/-- A routine of the runtime that works on registers: `rel` between the
state it is entered in and the state it returns in. -/
def RtPure (Z : ZCtx) (name : String) (rel : Cpu → Cpu → Prop) : Prop :=
  ∃ entry, Z.sym name entry ∧ entry < 65536 ∧
    Routine Z entry Z.rtK (fun _ => True) (fun s s' => rel s s' ∧ FreeStack Z s s')

/-- **A call of a routine of the runtime**, from states that agree. -/
theorem rt_call {base : Nat} {sF : GS} (ok : Z.OK) (hT : FnLay Z E) (F : GFinal Z base sF) {s0 s1 : GS}
    {name : String} {rel : Cpu → Cpu → Prop} (hx : GExt s1 sF)
    (ho : s1.out = s0.out.push (.ins ⟨.call, [.imm (.sym name)]⟩)) (hrt : RtPure Z name rel)
    (hdep : Z.rtK + 2 ≤ Z.depth E.fn.name) {regs : Regs} {ist : IR.Sem.St} {tmps : Array Nat} {s : Cpu}
    (R : Rel Z E fr dt regs ist tmps s) (hat : At Z.addrs (base + s0.out.size) s) :
    ∃ c1 s', CallSt s c1 ∧ Steps Z.inp s s' ∧ At Z.addrs (base + s1.out.size) s' ∧ rel c1 s' ∧
      ∀ regs' : Regs,
        (∀ o, o ∈ regs'.a → Own E o → s'.a.toNat = IR.Sem.opd Z.c ist tmps 1 o) →
        (∀ o, o ∈ regs'.hl → Own E o → s'.hl.toNat = IR.Sem.opd Z.c ist tmps 2 o) →
        (∀ sl, Opd.slot sl ∈ regs'.a → Own E (.slot sl) → Z.use (sl, 1)) →
        (∀ sl, Opd.slot sl ∈ regs'.hl → Own E (.slot sl) → Z.use (sl, 2)) →
        (∀ n o, regs'.acc = some (n, o) → regs.acc = some (n, o)) →
        Rel Z E fr dt regs' ist tmps s' := by
  obtain ⟨entry, hsym, hent, hR⟩ := hrt
  have hroom := R.room
  have hspv : s.sp.toNat = fr.sp.toNat := by rw [R.sp]
  have hstk := ok.stack
  obtain ⟨c1, s', cs, hst, hat', hsp', hh', hrs', hsz', hrel, hfree⟩ :=
    call_rule ok (F.emitted hx ho) hsym hent hR hat R.img R.run R.rs R.msz (by omega) (by omega)
      (fun _ _ => trivial)
  refine ⟨c1, s', cs, hst, by rw [ho, Array.size_push, ← Nat.add_assoc]; exact hat', hrel, fun regs' ha hhl hina hinhl hacc => ?_⟩
  refine R.free_stack ok hT (fun x hx => ?_) hsz' hrs' (by rw [hh', R.run]) hsp' ha hhl hina hinhl hacc
  have hc1sp : c1.sp.toNat = s.sp.toNat - 2 := by rw [cs.sp]; exact sub2_toNat _ (by omega)
  rw [hfree x (by omega), cs.mem x (by omega)]

end

end Ember.Proof.Z80Gen
