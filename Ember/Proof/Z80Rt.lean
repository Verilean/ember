import Ember.Proof.Z80Prog
import Ember.Proof.Z80Cmp
import Ember.Proof.Z80Ext
import Ember.Proof.Z80Addr

/-!
# Ember.Proof.Z80Rt — routines of the runtime, proved (plan M7.3)

The routines of the runtime are hand-written assembly.  Here they are
proved against what the theorems about generated code take of them
(`RtOK`), from their items in the image:

* `Has Z k l`: the items `l` are in the image from the index `k` on;
* the test harness (`Runtime.harness`): its effects are ports of the
  machine.  `Harness Z` says what the machine around the CPU does at
  those ports, as a view of its state as the IR's world; the routines
  `rt_out_byte`, `rt_out_end`, `rt_drop` and `rt_input` then do to the
  machine what the effects do to the world (`RtEff`).

None of these routines uses the stack: they hold for any `rtK`.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Lang (Effect World)

/-- The items `l` are in the image from the index `k` on. -/
def Has (Z : ZCtx) (k : Nat) (l : List Item) : Prop := ∀ (j : Nat) it, l[j]? = some it → Z.items[k + j]? = some it

section
variable {Z : ZCtx}

theorem Has.get {k : Nat} {l : List Item} (h : Has Z k l) (j : Nat) {it : Item} (hj : l[j]? = some it) :
    Z.items[k + j]? = some it := h j it hj

/-- A label of the image has its address, below the end of the image. -/
theorem label_sym (ok : Z.OK) {j : Nat} {l : String} (hj : Z.items[j]? = some (.label l)) :
    ∃ T, Z.addrs[j]? = some T ∧ Z.sym l T ∧ T ≤ Z.a.bytes.size := by
  obtain ⟨ad, bs, h1, _, _, _, _, hb, h6⟩ := ok.placed.2 j _ hj
  exact ⟨ad, h1, h6 l rfl, by omega⟩

/-- The CPU at a label is at the item after it. -/
theorem at_label (ok : Z.OK) {j : Nat} {l : String} (hj : Z.items[j]? = some (.label l)) {s : Cpu}
    (h : At Z.addrs j s) : At Z.addrs (j + 1) s :=
  at_skip ok.placed hj (fun _ => rfl) h

/-- **`ret`**, of the image. -/
theorem ret_raw (ok : Z.OK) {k : Nat} (hk : Z.items[k]? = some (.ins ⟨.ret, []⟩)) {s : Cpu} (M : Mach Z s)
    (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ s'.pc = s.rd16 s.sp ∧ s'.sp = s.sp + 2 ∧ s'.mem = s.mem ∧ s'.halted = s.halted ∧
      s'.ramStart = s.ramStart ∧ s'.h = s.h ∧ s'.l = s.l ∧ s'.a = s.a := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hst := fun inp => (step_item ok.placed M.1 hk had hpc M.2 (inp := inp)
    (s' := (retTo (op1 s)).tick 10) rfl).1
  refine ⟨_, Steps.one hst rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [retTo, zsim]

/-- One instruction of the image, in the machine: what it did on the bus changes the machine. -/
theorem wstep_item (ok : Z.OK) {k : Nat} {i : Instr} (hk : Z.items[k]? = some (.ins i)) {s s' : Cpu} (M : Mach Z s)
    (hat : At Z.addrs k s) (w : Z.W)
    (hx : ∀ ad, Z.addrs[k]? = some ad → exec (Z.a.env ad) i s (Z.bus w) = some s') :
    WSteps Z (s, w) (s', Z.dev w s'.io) ∧ (i.falls = true → At Z.addrs (k + 1) s') := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hst := step_item ok.placed M.1 hk had hpc M.2 (inp := Z.bus w) (hx ad had)
  refine ⟨⟨1, ?_⟩, hst.2⟩
  show wstep Z (s, w) = _
  unfold wstep
  simp only [hst.1]

/-- One instruction of the image that does no I/O. -/
theorem step_raw (ok : Z.OK) {k : Nat} {i : Instr} (hk : Z.items[k]? = some (.ins i)) {s : Cpu} (M : Mach Z s)
    (hat : At Z.addrs k s) (s' : Cpu)
    (hx : ∀ ad, Z.addrs[k]? = some ad → ∀ inp, exec (Z.a.env ad) i s inp = some s') (hio : s'.io = .none) :
    Steps s s' ∧ (i.falls = true → At Z.addrs (k + 1) s') := by
  obtain ⟨ad, had, hpc⟩ := hat
  have hst := fun inp => step_item ok.placed M.1 hk had hpc M.2 (inp := inp) (hx ad had inp)
  exact ⟨Steps.one (fun inp => (hst inp).1) hio, (hst (fun _ => 0)).2⟩

/-! ## The test harness -/

/-- What the harness answers at its port `0xD1`: the kind of the next
item of input — a byte (0), a tick (1), nothing (2). -/
def kindOf (w : World) : UInt8 :=
  if w.next.1 = 0xFFFF then 2 else if w.next.1 = 0x0100 then 1 else 0

/-- **The machine of the test harness**, as a view of its state: the
world, and the byte latched by the last read of the port `0xD1`.  The
bus answers the kind of the next input at `0xD1` and the latch at
`0xD2`; a read of `0xD1` takes the next input; writes to `0xD3`, `0xD4`
and `0xD5` are a byte of the frame, its end, a drop.  (This is what
`Ember.Z80.Machine` does at these ports.) -/
structure Harness (Z : ZCtx) where
  view : Z.W → World × UInt8
  wrel : ∀ wd w, Z.wrel wd w ↔ (view w).1 = wd
  busKind : ∀ w p, lo p = 0xD1 → Z.bus w p = kindOf (view w).1
  busByte : ∀ w p, lo p = 0xD2 → Z.bus w p = (view w).2
  rdNext : ∀ w p, lo p = 0xD1 → view (Z.dev w (.read p)) = ((view w).1.next.2, lo (view w).1.next.1)
  rdByte : ∀ w p, lo p = 0xD2 → (view (Z.dev w (.read p))).1 = (view w).1
  /-- `0xD0`: does input remain?  Asking changes nothing. -/
  rdMore : ∀ w p, lo p = 0xD0 → (view (Z.dev w (.read p))).1 = (view w).1
  busMore : ∀ w p, lo p = 0xD0 → Z.bus w p = if kindOf (view w).1 = 2 then 0 else 1
  wrByte : ∀ w p v, lo p = 0xD3 → (view (Z.dev w (.write p v))).1 = (IR.Sem.effect Z.c (view w).1 .outByte [v.toNat]).2
  wrEnd : ∀ w p v, lo p = 0xD4 → (view (Z.dev w (.write p v))).1 = (IR.Sem.effect Z.c (view w).1 .outEnd []).2
  wrDrop : ∀ w p v, lo p = 0xD5 → (view (Z.dev w (.write p v))).1 = (IR.Sem.effect Z.c (view w).1 .drop [v.toNat]).2

/-- `out (n),a; ret` under a label: the routine of an effect that is one write to a port. -/
theorem out_routine (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat} {name : String} {port : Nat}
    (hport : port < 256)
    (hhas : Has Z k [.label name, .ins ⟨.out, [.mem (.num (Int.ofNat port)), .a]⟩, .ins ⟨.ret, []⟩]) :
    ∃ entry, Z.sym name entry ∧ entry < 65536 ∧
      ∀ (c : Cpu) (w : Z.W), c.pc.toNat = entry → Img Z.a 0 c → c.halted = false →
        ∃ c' p, lo p = UInt8.ofNat port ∧ WSteps Z (c, w) (c', Z.dev w (.write p c.a)) ∧ c'.pc = c.rd16 c.sp ∧
          c'.sp = c.sp + 2 ∧ c'.halted = false ∧ c'.ramStart = c.ramStart ∧ c'.mem = c.mem := by
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 0 rfl)
  refine ⟨T, hsym, by omega, fun c w hpc I hh => ?_⟩
  have M : Mach Z c := ⟨I, hh⟩
  have at1 : At Z.addrs (k + 1) c := at_label ok (hhas.get 0 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at2⟩ := wstep_item ok (hhas.get 1 rfl) M at1 w
    (s' := (({ (skip (op1 c) 1) with
      io := .write (mk16 (op1 c).a (byteOf (Int.ofNat port))) (op1 c).a } : Cpu).tick 11)) (fun ad _ => rfl)
  have at2' := at2 rfl
  have M1 : Mach Z (({ (skip (op1 c) 1) with
      io := .write (mk16 (op1 c).a (byteOf (Int.ofNat port))) (op1 c).a } : Cpu).tick 11) :=
    M.sys (by simp only [Sys, skip, zsim, and_self])
  obtain ⟨c', st2, hpc', hsp', hmem', hh', hrs', _, _, _⟩ := ret_raw ok (hhas.get 2 rfl) M1 at2'
  refine ⟨c', mk16 c.a (byteOf (Int.ofNat port)), ?_, st1.trans (Steps.lift ok st2 _), ?_, ?_, ?_, ?_, ?_⟩
  · rw [lo_mk16]
    apply UInt8.toNat_inj.mp
    rw [byteOf_toNat, UInt8.toNat_ofNat']
    show ((port : Int) % 256).toNat = port % 256
    omega
  · rw [hpc']
    simp only [skip, zsim]
    rfl
  · rw [hsp']
    simp only [skip, zsim]
  · rw [hh']
    simp only [skip, zsim]
    exact hh
  · rw [hrs']
    simp only [skip, zsim]
  · rw [hmem']
    simp only [skip, zsim]

/-- The effects that are one write to a port of the harness. -/
theorem harness_out (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k : Nat} {port : Nat}
    (hport : port < 256) (e : Effect)
    (hhas : Has Z k [.label (effectRoutine e), .ins ⟨.out, [.mem (.num (Int.ofNat port)), .a]⟩, .ins ⟨.ret, []⟩])
    (hdev : ∀ (w : Z.W) (p : UInt16) (c : Cpu) (vs : List Nat), lo p = UInt8.ofNat port → EffArgs Z e vs c →
      (H.view (Z.dev w (.write p c.a))).1 = (IR.Sem.effect Z.c (H.view w).1 e vs).2)
    (hnone : ∀ wd vs, (IR.Sem.effect Z.c wd e vs).1 = none) : RtEff Z e := by
  intro _
  obtain ⟨entry, hsym, hent, hrun⟩ := out_routine ok hsz hport hhas
  refine ⟨entry, hsym, hent, fun c w wd vs hpc I hh hrs hmsz _ _ hw hargs => ?_⟩
  obtain ⟨c', p, hp, st, hpc', hsp', hh', hrs', hmem'⟩ := hrun c w hpc I hh
  refine ⟨c', _, st, hpc', hsp', hh', hrs', by rw [hmem']; exact hmsz, fun x _ _ => by rw [hmem'], ?_, ?_⟩
  · rw [H.wrel, hdev w p c vs hp hargs, (H.wrel wd w).mp hw]
  · intro r hr
    rw [hnone] at hr
    cases hr

theorem harness_out_byte (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k [.label "rt_out_byte", .ins ⟨.out, [.mem (.num 0xD3), .a]⟩, .ins ⟨.ret, []⟩]) :
    RtEff Z .outByte :=
  harness_out ok H hsz (port := 0xD3) (by decide) .outByte hhas
    (fun w p c vs hp hargs => by
      have hv : vs = [c.a.toNat] := hargs
      rw [hv]
      exact H.wrByte w p c.a hp) (fun _ _ => rfl)

theorem harness_out_end (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k [.label "rt_out_end", .ins ⟨.out, [.mem (.num 0xD4), .a]⟩, .ins ⟨.ret, []⟩]) :
    RtEff Z .outEnd :=
  harness_out ok H hsz (port := 0xD4) (by decide) .outEnd hhas
    (fun w p c vs hp hargs => by
      have hv : vs = [] := hargs
      rw [hv]
      exact H.wrEnd w p c.a hp) (fun _ _ => rfl)

theorem harness_drop (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k [.label "rt_drop", .ins ⟨.out, [.mem (.num 0xD5), .a]⟩, .ins ⟨.ret, []⟩]) :
    RtEff Z .drop :=
  harness_out ok H hsz (port := 0xD5) (by decide) .drop hhas
    (fun w p c vs hp hargs => by
      have hv : vs = [c.a.toNat] := hargs
      rw [hv]
      exact H.wrDrop w p c.a hp) (fun _ _ => rfl)

theorem next_cases (w : World) : w.next.1 = 0xFFFF ∨ w.next.1 = 0x0100 ∨ w.next.1.toNat < 256 := by
  unfold World.next
  simp only
  split
  · split
    · exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr ?_)
      rw [UInt8.toNat_toUInt16]
      exact UInt8.toNat_lt _
  · exact Or.inl rfl

/-- The items of the harness's `rt_input`. -/
def inputItems : List Item :=
  [.label "rt_input",
   .ins ⟨.in, [.a, .mem (.num 0xD1)]⟩, .ins ⟨.cp, [.imm (.num 2)]⟩, .ins ⟨.jr, [.z, .imm (.sym "rt_input_none")]⟩,
   .ins ⟨.ld, [.hl, .imm (.sym "rt_consumed")]⟩, .ins ⟨.inc, [.mhl]⟩, .ins ⟨.cp, [.imm (.num 1)]⟩,
   .ins ⟨.jr, [.z, .imm (.sym "rt_input_tick")]⟩,
   .ins ⟨.in, [.a, .mem (.num 0xD2)]⟩, .ins ⟨.ld, [.l, .a]⟩, .ins ⟨.ld, [.h, .imm (.num 0)]⟩, .ins ⟨.ret, []⟩,
   .label "rt_input_tick", .ins ⟨.ld, [.hl, .imm (.num 0x0100)]⟩, .ins ⟨.ret, []⟩,
   .label "rt_input_none", .ins ⟨.ld, [.hl, .imm (.num 0xFFFF)]⟩, .ins ⟨.ret, []⟩]

/-- `ld hl,nn; ret`. -/
theorem ld_hl_ret (ok : Z.OK) {k : Nat} (v : Nat) (hv : v < 65536)
    (h1 : Z.items[k]? = some (.ins ⟨.ld, [.hl, .imm (.num (Int.ofNat v))]⟩))
    (h2 : Z.items[k + 1]? = some (.ins ⟨.ret, []⟩)) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    ∃ s', Steps s s' ∧ s'.pc = s.rd16 s.sp ∧ s'.sp = s.sp + 2 ∧ s'.mem = s.mem ∧ s'.halted = s.halted ∧
      s'.ramStart = s.ramStart ∧ s'.hl.toNat = v := by
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = ((skip (op1 s) 2).setHL
      (w16 (byteOf (Int.ofNat v)) (byteOf (Int.ofNat v / 256)))).tick 10 := ⟨_, rfl⟩
  obtain ⟨st1, at1⟩ := step_raw ok h1 M hat c1 (fun ad _ inp => by rw [hc1]; rfl) (by rw [hc1]; simp only [zsim])
  have hS : Sys s c1 := by rw [hc1]; simp only [Sys, skip, zsim, and_self]
  obtain ⟨s', st2, hpc', hsp', hmem', hh', hrs', hh2, hl2, _⟩ := ret_raw ok h2 (M.sys hS) (at1 rfl)
  refine ⟨s', st1.trans st2, ?_, by rw [hsp', hS.2.2.2], by rw [hmem', hS.1], by rw [hh', hS.2.2.1],
    by rw [hrs', hS.2.1], ?_⟩
  · rw [hpc', hS.2.2.2]
    show Cpu.rd16 c1 s.sp = Cpu.rd16 s s.sp
    simp only [Cpu.rd16, Cpu.rd, hS.1]
  · rw [show s'.hl = c1.hl from by simp only [Cpu.hl, hh2, hl2], hc1]
    simp only [zsim]
    exact w16_val v hv

/-- A `Does` instruction of the image, run. -/
theorem does_raw (ok : Z.OK) {k : Nat} {i : Instr} {f : Cpu → Cpu} (D : Does i f)
    (hk : Z.items[k]? = some (.ins i)) {s : Cpu} (M : Mach Z s) (hat : At Z.addrs k s) :
    Steps s (f s) ∧ At Z.addrs (k + 1) (f s) ∧ Mach Z (f s) ∧ Sys s (f s) := by
  obtain ⟨st, at'⟩ := step_raw ok hk M hat (f s) (fun _ _ inp => D.exec _ _ inp) (D.io s)
  exact ⟨st, at' D.falls, M.sys (D.sys s), D.sys s⟩

theorem cpN_z (v : Nat) (hv : v < 256) (s : Cpu) : (cpN v s).flag FZ = (s.a.toNat == v) := by
  unfold cpN
  rw [flag_tick, cp_z, u8_beq]
  simp only [skip, zsim]
  have e : (byteOf (Int.ofNat (v % 256))).toNat = v := by
    rw [byteOf_toNat]
    show (((v % 256 : Nat) : Int) % 256).toNat = v
    omega
  rw [e]

theorem cpN_a (v : Nat) (s : Cpu) : (cpN v s).a = s.a := by
  simp only [cpN, skip, zsim]

/-- **The harness's `rt_input`**: it takes the next item of input. -/
theorem harness_input_core (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k A : Nat}
    (hhas : Has Z k inputItems) (hcons : Z.sym "rt_consumed" A) (hrt : Z.rt A) (hA : A < 65536) :
    ∃ entry, Z.sym "rt_input" entry ∧ entry < 65536 ∧
      ∀ (c : Cpu) (w : Z.W), c.pc.toNat = entry → Img Z.a 0 c → c.halted = false → c.ramStart.toNat = Z.ramStart →
        c.mem.size = 65536 → Z.stackLo ≤ c.sp.toNat → c.sp.toNat + 2 ≤ Z.stackHi →
        ∃ c' w', WSteps Z (c, w) (c', w') ∧ c'.pc = c.rd16 c.sp ∧ c'.sp = c.sp + 2 ∧ c'.halted = false ∧
          c'.ramStart = c.ramStart ∧ c'.mem.size = 65536 ∧ FreeStack Z c c' ∧
          (H.view w').1 = (H.view w).1.next.2 ∧ c'.hl.toNat = (H.view w).1.next.1.toNat := by
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 0 rfl)
  refine ⟨T, hsym, by omega, fun c w hpc I hh hrs hmsz hlo' htop => ?_⟩
  have M : Mach Z c := ⟨I, hh⟩
  have at1 : At Z.addrs (k + 1) c := at_label ok (hhas.get 0 rfl) ⟨T, hT, hpc⟩
  -- in a,(0xD1)
  obtain ⟨p, hp⟩ : ∃ p : UInt16, p = mk16 (op1 c).a (byteOf (Int.ofNat 0xD1)) := ⟨_, rfl⟩
  have hlo : lo p = 0xD1 := by rw [hp, lo_mk16]; rfl
  obtain ⟨c1, hc1⟩ : ∃ c1 : Cpu, c1 = (({ (skip (op1 c) 1) with a := Z.bus w p, io := .read p } : Cpu).tick 11) :=
    ⟨_, rfl⟩
  obtain ⟨st1, at2⟩ := wstep_item ok (hhas.get 1 rfl) M at1 w (s' := c1) (fun ad _ => by rw [hc1, hp]; rfl)
  have hio1 : c1.io = .read p := by rw [hc1]; rfl
  rw [hio1] at st1
  have hS1 : Sys c c1 := by rw [hc1]; simp only [Sys, skip, zsim, and_self]
  have ha1 : c1.a = kindOf (H.view w).1 := by rw [hc1]; simp only [zsim]; exact H.busKind w p hlo
  have hv1 := H.rdNext w p hlo
  have M1 := M.sys hS1
  -- cp 2; jr z,rt_input_none
  obtain ⟨st2, at3, M2, hS2⟩ := does_raw ok (does_cp_n 2) (hhas.get 2 rfl) M1 (at2 rfl)
  obtain ⟨c3, st3, M3, hS3, hK3, hbr3⟩ := jr_cc_step ok true (l := "rt_input_none") (hhas.get 3 rfl)
    (hhas.get 15 rfl) M2 at3
  rw [cpN_z 2 (by decide), ha1] at hbr3
  have hS03 : Sys c c3 := (hS1.trans hS2).trans hS3
  have ha3 : c3.a = kindOf (H.view w).1 := by rw [hK3.1, cpN_a, ha1]
  have st03 : WSteps Z (c, w) (c3, Z.dev w (.read p)) :=
    st1.trans (Steps.lift ok (st2.trans st3) _)
  have hfree0 : ∀ c' : Cpu, c'.mem = c3.mem → FreeStack Z c c' := fun c' h x _ _ => by rw [h, hS03.1]
  by_cases hk2 : kindOf (H.view w).1 = 2
  · -- nothing
    have hn : (H.view w).1.next.1 = 0xFFFF := by
      unfold kindOf at hk2
      split at hk2
      · assumption
      · split at hk2 <;> cases hk2
    rw [hk2] at hbr3
    simp only [show ((2 : UInt8).toNat == 2) = true from rfl, if_true] at hbr3
    obtain ⟨c', st4, hpc', hsp', hmem', hh', hrs', hhl'⟩ := ld_hl_ret ok 0xFFFF (by decide) (hhas.get 16 rfl)
      (hhas.get 17 rfl) M3 (at_label ok (hhas.get 15 rfl) hbr3)
    refine ⟨c', _, st03.trans (Steps.lift ok st4 _), ?_, by rw [hsp', hS03.2.2.2], by rw [hh', hS03.2.2.1]; exact hh,
      by rw [hrs', hS03.2.1], by rw [hmem', hS03.1]; exact hmsz, hfree0 c' hmem', by rw [hv1], ?_⟩
    · rw [hpc', hS03.2.2.2]
      simp only [Cpu.rd16, Cpu.rd, hS03.1]
    · rw [hhl', hn]
      rfl
  -- something: count it, then tell a tick from a byte
  have hne2 : ((kindOf (H.view w).1).toNat == 2) = false := by
    simpa using fun h => hk2 (UInt8.toNat_inj.mp h)
  rw [hne2] at hbr3
  simp only [Bool.false_eq_true, if_false] at hbr3
  have hramA : Z.ramStart ≤ A := ok.rtRam A hrt
  -- ld hl,rt_consumed
  obtain ⟨ad4, had4, hpc4⟩ := hbr3
  obtain ⟨c4, hc4⟩ : ∃ c4 : Cpu, c4 = ((skip (op1 c3) 2).setHL
      (Instr.immW (Z.a.env ad4) ⟨.ld, [.hl, .imm (.sym "rt_consumed")]⟩)).tick 10 := ⟨_, rfl⟩
  have hnn : (Instr.immW (Z.a.env ad4) ⟨.ld, [.hl, .imm (.sym "rt_consumed")]⟩).toNat = A :=
    immW_toNat _ _ _ _ rfl (sym_val ad4 hcons) hA
  obtain ⟨st4, at5⟩ := step_raw ok (hhas.get 4 rfl) M3 ⟨ad4, had4, hpc4⟩ c4 (fun ad' had' inp => by
    rw [had4] at had'
    cases had'
    rw [hc4]
    rfl) (by rw [hc4]; simp only [zsim])
  have hS4 : Sys c3 c4 := by rw [hc4]; simp only [Sys, skip, zsim, and_self]
  have hhl4 : c4.hl.toNat = A := by rw [hc4]; simp only [zsim]; exact hnn
  have ha4 : c4.a = c3.a := by rw [hc4]; simp only [skip, zsim]
  have M4 := M3.sys hS4
  -- inc (hl)
  obtain ⟨c5, hc5⟩ : ∃ c5 : Cpu, c5 = (((op1 c4).inc8 ((op1 c4).rd (op1 c4).hl)).2.wr (op1 c4).hl
      ((op1 c4).inc8 ((op1 c4).rd (op1 c4).hl)).1).tick 11 := ⟨_, rfl⟩
  obtain ⟨st5, at6⟩ := step_raw ok (hhas.get 5 rfl) M4 (at5 rfl) c5 (fun _ _ _ => by rw [hc5]; rfl)
    (by rw [hc5]; simp only [zsim])
  have hrs4 : c4.ramStart.toNat = Z.ramStart := by rw [hS4.2.1, hS03.2.1]; exact hrs
  have hmem5 : ∃ v, c5.mem = c4.mem.set! A v := by
    refine ⟨((op1 c4).inc8 ((op1 c4).rd (op1 c4).hl)).1, ?_⟩
    rw [hc5]
    simp only [zsim]
    rw [cpu_wr_mem _ _ _ (by simp only [zsim]; rw [hrs4, hhl4]; exact hramA)]
    simp only [zsim, hhl4]
  obtain ⟨v5, hmem5⟩ := hmem5
  have ha5 : c5.a = c4.a := by rw [hc5]; simp only [zsim]
  have hsp5 : c5.sp = c4.sp := by rw [hc5]; simp only [zsim]
  have hh5 : c5.halted = c4.halted := by rw [hc5]; simp only [zsim]
  have hr5 : c5.ramStart = c4.ramStart := by rw [hc5]; simp only [zsim]
  have M5 : Mach Z c5 := by
    refine ⟨⟨by rw [hr5]; exact M4.1.rom, fun x b hx => ?_⟩, by rw [hh5]; exact M4.2⟩
    have hlt : x < Z.a.bytes.size := by
      rcases Nat.lt_or_ge x Z.a.bytes.data.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hx; cases hx
    have hrom := M4.1.rom
    rw [hmem5, getBang_set _ _ _ _ (by omega)]
    exact M4.1.bytes x b hx
  have hfree5 : ∀ c' : Cpu, c'.mem = c5.mem → FreeStack Z c c' := fun c' h x _ hnrt => by
    rw [h, hmem5, getBang_set _ _ _ _ (fun e : A = x => hnrt (e ▸ hrt)), hS4.1, hS03.1]
  have hsz5 : c5.mem.size = 65536 := by
    rw [hmem5]
    have : (c4.mem.set! A v5).size = c4.mem.size := by
      obtain ⟨bs⟩ := c4.mem
      simp [ByteArray.set!, ByteArray.size]
    rw [this, hS4.1, hS03.1]
    exact hmsz
  -- cp 1; jr z,rt_input_tick
  obtain ⟨st6, at7, M6, hS6⟩ := does_raw ok (does_cp_n 1) (hhas.get 6 rfl) M5 (at6 rfl)
  obtain ⟨c7, st7, M7, hS7, hK7, hbr7⟩ := jr_cc_step ok true (l := "rt_input_tick") (hhas.get 7 rfl)
    (hhas.get 12 rfl) M6 at7
  rw [cpN_z 1 (by decide), ha5, ha4, ha3] at hbr7
  have hS57 : Sys c5 c7 := hS6.trans hS7
  have st07 : WSteps Z (c, w) (c7, Z.dev w (.read p)) :=
    st03.trans (Steps.lift ok (((st4.trans st5).trans st6).trans st7) _)
  have hsp7 : c7.sp = c.sp := by rw [hS57.2.2.2, hsp5, hS4.2.2.2, hS03.2.2.2]
  have hh7 : c7.halted = false := by rw [hS57.2.2.1, hh5, hS4.2.2.1, hS03.2.2.1]; exact hh
  have hr7 : c7.ramStart = c.ramStart := by rw [hS57.2.1, hr5, hS4.2.1, hS03.2.1]
  have hmem7 : ∀ x, x ≠ A → c7.mem.get! x = c.mem.get! x := fun x hx => by
    rw [hS57.1, hmem5, getBang_set _ _ _ _ (fun e => hx e.symm), hS4.1, hS03.1]
  have hstk := ok.stack
  have hrd : ∀ c' : Cpu, c'.mem = c7.mem → c'.rd16 c.sp = c.rd16 c.sp := fun c' h => by
    have hA' := ok.rtStack A hrt
    have h1 : (c.sp + 1).toNat = c.sp.toNat + 1 := by
      rw [UInt16.toNat_add]
      show (c.sp.toNat + 1) % 65536 = _
      omega
    simp only [Cpu.rd16, Cpu.rd, h, h1]
    rw [hmem7 _ (by omega), hmem7 _ (by omega)]
  have hfree7 : ∀ c' : Cpu, c'.mem = c7.mem → FreeStack Z c c' := fun c' h => hfree5 c' (by rw [h, hS57.1])
  have hsz7 : c7.mem.size = 65536 := by rw [hS57.1]; exact hsz5
  by_cases hk1 : kindOf (H.view w).1 = 1
  · -- a tick
    have hn : (H.view w).1.next.1 = 0x0100 := by
      unfold kindOf at hk1
      split at hk1
      · cases hk1
      · split at hk1
        · assumption
        · cases hk1
    rw [hk1] at hbr7
    simp only [show ((1 : UInt8).toNat == 1) = true from rfl, if_true] at hbr7
    obtain ⟨c', st8, hpc', hsp', hmem', hh', hrs', hhl'⟩ := ld_hl_ret ok 0x0100 (by decide) (hhas.get 13 rfl)
      (hhas.get 14 rfl) M7 (at_label ok (hhas.get 12 rfl) hbr7)
    refine ⟨c', _, st07.trans (Steps.lift ok st8 _), ?_, by rw [hsp', hsp7], by rw [hh', hh7], by rw [hrs', hr7],
      by rw [hmem']; exact hsz7, hfree7 c' hmem', by rw [hv1], ?_⟩
    · rw [hpc', hsp7, ← hrd c7 rfl]
    · rw [hhl', hn]
      rfl
  · -- a byte
    have hn : (H.view w).1.next.1.toNat < 256 := by
      rcases next_cases (H.view w).1 with h | h | h
      · exact absurd (by simp [kindOf, h]) hk2
      · exact absurd (by simp [kindOf, h]) hk1
      · exact h
    have hne1 : ((kindOf (H.view w).1).toNat == 1) = false := by
      simpa using fun h => hk1 (UInt8.toNat_inj.mp h)
    rw [hne1] at hbr7
    simp only [Bool.false_eq_true, if_false] at hbr7
    -- in a,(0xD2)
    obtain ⟨p2, hp2⟩ : ∃ p2 : UInt16, p2 = mk16 (op1 c7).a (byteOf (Int.ofNat 0xD2)) := ⟨_, rfl⟩
    have hlo2 : lo p2 = 0xD2 := by rw [hp2, lo_mk16]; rfl
    obtain ⟨c8, hc8⟩ : ∃ c8 : Cpu, c8 = (({ (skip (op1 c7) 1) with
        a := Z.bus (Z.dev w (.read p)) p2, io := .read p2 } : Cpu).tick 11) := ⟨_, rfl⟩
    obtain ⟨st8, at9⟩ := wstep_item ok (hhas.get 8 rfl) M7 hbr7 (Z.dev w (.read p)) (s' := c8)
      (fun ad _ => by rw [hc8, hp2]; rfl)
    have hio8 : c8.io = .read p2 := by rw [hc8]; rfl
    rw [hio8] at st8
    have hS8 : Sys c7 c8 := by rw [hc8]; simp only [Sys, skip, zsim, and_self]
    have ha8 : c8.a = lo (H.view w).1.next.1 := by
      rw [hc8]
      simp only [zsim]
      rw [H.busByte _ p2 hlo2, hv1]
    have M8 := M7.sys hS8
    obtain ⟨st9, at10, M9, hS9⟩ := does_raw ok does_ld_l_a (hhas.get 9 rfl) M8 (at9 rfl)
    obtain ⟨st10, at11, M10, hS10⟩ := does_raw ok does_ld_h_0 (hhas.get 10 rfl) M9 at10
    obtain ⟨c', st11, hpc', hsp', hmem', hh', hrs', hh2, hl2, _⟩ := ret_raw ok (hhas.get 11 rfl) M10 at11
    have hS : Sys c7 (ldH0 (ldRA 5 c8)) := (hS8.trans hS9).trans hS10
    refine ⟨c', _, (st07.trans st8).trans (Steps.lift ok ((st9.trans st10).trans st11) _), ?_, by rw [hsp', hS.2.2.2, hsp7],
      by rw [hh', hS.2.2.1, hh7], by rw [hrs', hS.2.1, hr7], by rw [hmem', hS.1]; exact hsz7,
      hfree7 c' (by rw [hmem', hS.1]), ?_, ?_⟩
    · rw [hpc', hS.2.2.2, hsp7, ← hrd (ldH0 (ldRA 5 c8)) hS.1]
    · rw [H.rdByte _ p2 hlo2, hv1]
    · rw [show c'.hl = (ldH0 (ldRA 5 c8)).hl from by simp only [Cpu.hl, hh2, hl2]]
      have : (ldH0 (ldRA 5 c8)).hl = mk16 0 c8.a := by
        simp only [ldH0, ldRA, skip, zsim]
        rfl
      rw [this, mk16_toNat, ha8]
      show 0 * 256 + (H.view w).1.next.1.toUInt8.toNat = _
      rw [UInt16.toNat_toUInt8]
      omega

theorem harness_input (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k A : Nat}
    (hhas : Has Z k inputItems) (hcons : Z.sym "rt_consumed" A) (hrt : Z.rt A) (hA : A < 65536) (e : Effect)
    (he : e = .inputNext ∨ e = .ringPop) : RtEff Z e := by
  intro _
  obtain ⟨entry, hsym, hent, hrun⟩ := harness_input_core ok H hsz hhas hcons hrt hA
  have hname : effectRoutine e = "rt_input" := by rcases he with rfl | rfl <;> rfl
  have heff : ∀ wd vs, IR.Sem.effect Z.c wd e vs = (some wd.next.1.toNat, wd.next.2) := by
    intro wd vs
    rcases he with rfl | rfl <;> rfl
  refine ⟨entry, by rw [hname]; exact hsym, hent, fun c w wd vs hpc I hh hrs hmsz hroom htop hw _ => ?_⟩
  obtain ⟨c', w', st, hpc', hsp', hh', hrs', hsz', hfree, hview, hhl⟩ := hrun c w hpc I hh hrs hmsz (by omega) htop
  have hwd := (H.wrel wd w).mp hw
  refine ⟨c', w', st, hpc', hsp', hh', hrs', hsz', hfree, ?_, ?_⟩
  · rw [heff, H.wrel, hview, hwd]
  · intro r hr
    rw [heff] at hr
    cases hr
    rw [hhl, hwd]

/-! ## `rt_bound` -/

/-- `sbc hl,bc` as the model runs it. -/
def sbcHLBC (s : Cpu) : Cpu := ((op2 s).sbc16 ((op2 s).rp .hl 0)).tick 15

theorem does_sbc_hl_bc : Does ⟨.sbc, [.hl, .bc]⟩ sbcHLBC :=
  ⟨fun _ _ _ => rfl, rfl, fun s => by simp only [Sys, sbcHLBC, zsim, and_self], fun s => by simp only [sbcHLBC, zsim]⟩

def boundItems : List Item :=
  [.label "rt_bound", .ins ⟨.or, [.a]⟩, .ins ⟨.sbc, [.hl, .bc]⟩, .ins ⟨.add, [.hl, .bc]⟩, .ins ⟨.ret, [.c]⟩,
   .ins ⟨.jp, [.imm (.sym "rt_trap")]⟩]

/-- **`rt_bound`**: it returns when `HL < BC`, with `A`, `DE` and `HL` as
they were, and is at `rt_trap` when not.  It uses no stack. -/
theorem rt_bound_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k j : Nat} (hhas : Has Z k boundItems)
    (htrap : Z.items[j]? = some (.label "rt_trap")) : RtBound Z := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 0 rfl)
  refine ⟨T, hsym, by omega, fun c hpc I hh hrs hmsz _ _ => ?_⟩
  have M : Mach Z c := ⟨I, hh⟩
  have at1 : At Z.addrs (k + 1) c := at_label ok (hhas.get 0 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at2, M1, hS1⟩ := does_raw ok does_or_a (hhas.get 1 rfl) M at1
  obtain ⟨st2, at3, M2, hS2⟩ := does_raw ok does_sbc_hl_bc (hhas.get 2 rfl) M1 at2
  obtain ⟨st3, at4, M3, hS3⟩ := does_raw ok does_add_hl_bc (hhas.get 3 rfl) M2 at3
  obtain ⟨c3, hc3⟩ : ∃ c3 : Cpu, c3 = addHLBC (sbcHLBC (orA c)) := ⟨_, rfl⟩
  rw [← hc3] at st3 at4 M3 hS3
  have hS : Sys c c3 := by rw [hc3]; exact (hS1.trans hS2).trans (by rw [hc3] at hS3; exact hS3)
  -- the registers
  have hfc1 : (orA c).flag FC = false := by
    unfold orA
    rw [flag_tick]
    exact alu6_flag _ _
  have hhl1 : (orA c).hl = c.hl := by simp only [orA, zsim]
  have hbc1 : (orA c).bc = c.bc := by simp only [orA, zsim]
  have hhl2 : (sbcHLBC (orA c)).hl.toNat = (c.hl.toNat + 65536 - c.bc.toNat) % 65536 := by
    unfold sbcHLBC
    simp only [zsim]
    rw [sbc16_val _ _ (by simpa only [zsim] using hfc1)]
    simp only [zsim, hhl1, hbc1]
  have hbc2 : (sbcHLBC (orA c)).bc = c.bc := by simp only [sbcHLBC, zsim]; exact hbc1
  have hhl3 : c3.hl = c.hl := by
    apply UInt16.toNat_inj.mp
    rw [hc3]
    unfold addHLBC
    simp only [zsim]
    rw [add16_val, hhl2, hbc2]
    have := c.hl.toNat_lt
    have := c.bc.toNat_lt
    omega
  have hfc3 : c3.flag FC = decide (c.hl.toNat < c.bc.toNat) := by
    rw [hc3]
    unfold addHLBC
    simp only [zsim]
    rw [add16_fc, hhl2, hbc2]
    have := c.hl.toNat_lt
    have := c.bc.toNat_lt
    congr 1
    apply propext
    constructor <;> intro h <;> omega
  have ha3 : c3.a = c.a := by
    rw [hc3]
    simp only [addHLBC, sbcHLBC, zsim]
    exact orA_a c
  have hde3 : c3.de = c.de := by
    rw [hc3]
    simp only [addHLBC, sbcHLBC, orA, zsim]
  -- ret c
  obtain ⟨ad, had, hpcad⟩ := at4
  obtain ⟨c4, hc4⟩ : ∃ c4 : Cpu, c4 = (if (op1 c3).cond 3 then (retTo (op1 c3)).tick 11 else (op1 c3).tick 5) :=
    ⟨_, rfl⟩
  have hst4 := fun inp => (step_item ok.placed M3.1 (hhas.get 4 rfl) had hpcad M3.2 (inp := inp) (s' := c4)
    (by rw [hc4]; rfl)).1
  have hcond : (op1 c3).cond 3 = decide (c.hl.toNat < c.bc.toNat) := by
    rw [cond_op1]
    exact hfc3
  by_cases hlt : c.hl.toNat < c.bc.toNat
  · rw [hcond, decide_eq_true hlt, if_pos rfl] at hc4
    have st4 : Steps c3 c4 := Steps.one hst4 (by rw [hc4]; simp only [retTo, zsim])
    refine ⟨c4, ((st1.trans st2).trans st3).trans st4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc4]; simp only [retTo, zsim]; rw [hS.2.2.1]; exact hh
    · rw [hc4]; simp only [retTo, zsim]; exact hS.2.1
    · rw [hc4]; simp only [retTo, zsim]; rw [hS.1]; exact hmsz
    · intro x _ _
      rw [hc4]; simp only [retTo, zsim]; rw [hS.1]
    · rw [hc4]; simp only [retTo, zsim]; exact ha3
    · rw [hc4]; simp only [retTo, zsim]; exact hde3
    · rw [if_pos hlt]
      refine ⟨?_, ?_, ?_⟩
      · rw [hc4]; simp only [retTo, zsim]
        rw [hS.2.2.2]
        simp only [Cpu.rd16, Cpu.rd, hS.1]
      · rw [hc4]; simp only [retTo, zsim]; rw [hS.2.2.2]
      · rw [hc4]; simp only [retTo, zsim]; exact hhl3
  · rw [hcond, decide_eq_false hlt] at hc4
    simp only [Bool.false_eq_true, if_false] at hc4
    have st4 : Steps c3 c4 := Steps.one hst4 (by rw [hc4]; simp only [zsim])
    have hS4 : Sys c3 c4 := by rw [hc4]; simp only [Sys, zsim, and_self]
    -- the item after `ret c`
    obtain ⟨bs, hbs, hnext, hlt65⟩ := ok.placed.next M3.1 (hhas.get 4 rfl) had
    have hbs' : bs = [0xD8] := by
      have : Item.encode (.ins ⟨.ret, [.c]⟩) (Z.a.env ad) = .ok [0xD8] := rfl
      rw [this] at hbs
      exact (Except.ok.inj hbs).symm
    have at5 : At Z.addrs (k + 5) c4 := by
      refine ⟨ad + 1, by rw [hbs'] at hnext; exact hnext, ?_⟩
      rw [hc4]
      simp only [zsim]
      have hb := hlt65 (by rw [hbs']; exact List.cons_ne_nil _ _)
      rw [hbs'] at hb
      have hb' : ad + 1 < 65536 := hb
      rw [UInt16.toNat_add, hpcad]
      show (ad + 1) % 65536 = ad + 1
      omega
    obtain ⟨c5, st5, at6, M5, hS5, hK5⟩ := jp_step ok (hhas.get 5 rfl) htrap (M3.sys hS4) at5
    have hS' : Sys c c5 := (hS.trans hS4).trans hS5
    refine ⟨c5, (((st1.trans st2).trans st3).trans st4).trans st5, M5.2, hS'.2.1, by rw [hS'.1]; exact hmsz,
      fun x _ _ => by rw [hS'.1], ?_, ?_, ?_⟩
    · rw [hK5.1, hc4]; simp only [zsim]; exact ha3
    · simp only [Cpu.de, hK5.2.2.2.2.1, hK5.2.2.2.2.2.1]
      have : c4.de = c.de := by rw [hc4]; simp only [zsim]; exact hde3
      simpa only [Cpu.de] using this
    · rw [if_neg hlt]
      exact ⟨j, htrap, at6⟩

end

end Ember.Proof.Z80Gen
