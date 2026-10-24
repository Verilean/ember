import Ember.Proof.Z80Prog
import Ember.Proof.Z80Cmp
import Ember.Proof.Z80Ext
import Ember.Proof.Z80Addr
import Ember.Proof.Z80Una
import Ember.Proof.Z80Shift

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

None of these routines uses the stack or writes memory: they hold for any `rtK`.
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
world, and the byte latched by the last read of the port `0xD1` that
took one.  The bus answers the kind of the next input at `0xD1` and the
latch at `0xD2`; a read of `0xD1` takes the next input; writes to
`0xD3`, `0xD4` and `0xD5` are a byte of the frame, its end, a drop.
What a port does is said of `Z.wrel` — the machine stands for the world
before, and for the world after — so that a relation that says more of
the machine than its world can be used.  (This is what
`Ember.Z80.Machine` does at these ports: `Z80Machine`.) -/
structure Harness (Z : ZCtx) where
  view : Z.W → World × UInt8
  wrelView : ∀ wd w, Z.wrel wd w → (view w).1 = wd
  busKind : ∀ w p, lo p = 0xD1 → Z.bus w p = kindOf (view w).1
  busByte : ∀ w p, lo p = 0xD2 → Z.bus w p = (view w).2
  rdNext : ∀ wd w p, lo p = 0xD1 → Z.wrel wd w → Z.wrel wd.next.2 (Z.dev w (.read p))
  /-- A byte taken is latched (a tick, or nothing, leaves the latch). -/
  rdLatch : ∀ w p, lo p = 0xD1 → (view w).1.next.1.toNat < 256 → (view (Z.dev w (.read p))).2 = lo (view w).1.next.1
  rdByte : ∀ wd w p, lo p = 0xD2 → Z.wrel wd w → Z.wrel wd (Z.dev w (.read p))
  wrByte : ∀ wd w p v, lo p = 0xD3 → Z.wrel wd w →
    Z.wrel (IR.Sem.effect Z.c wd .outByte [v.toNat]).2 (Z.dev w (.write p v))
  wrEnd : ∀ wd w p v, lo p = 0xD4 → Z.wrel wd w → Z.wrel (IR.Sem.effect Z.c wd .outEnd []).2 (Z.dev w (.write p v))
  wrDrop : ∀ wd w p v, lo p = 0xD5 → Z.wrel wd w →
    Z.wrel (IR.Sem.effect Z.c wd .drop [v.toNat]).2 (Z.dev w (.write p v))
  /-- A note: the four bytes of its value to `0xDA`, least significant first, then its code to `0xD6`. -/
  wrNote : ∀ wd w p0 p1 p2 p3 p (b0 b1 b2 b3 k : UInt8), lo p0 = 0xDA → lo p1 = 0xDA → lo p2 = 0xDA →
    lo p3 = 0xDA → lo p = 0xD6 → Z.wrel wd w →
    Z.wrel (IR.Sem.effect Z.c wd .note
        [k.toNat, b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 * 0)))]).2
      (Z.dev (Z.dev (Z.dev (Z.dev (Z.dev w (.write p0 b0)) (.write p1 b1)) (.write p2 b2)) (.write p3 b3)) (.write p k))

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
theorem harness_out (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat} {port : Nat}
    (hport : port < 256) (e : Effect)
    (hhas : Has Z k [.label (effectRoutine e), .ins ⟨.out, [.mem (.num (Int.ofNat port)), .a]⟩, .ins ⟨.ret, []⟩])
    (hdev : ∀ (wd : World) (w : Z.W) (p : UInt16) (c : Cpu) (vs : List Nat), lo p = UInt8.ofNat port →
      EffArgs Z e vs c → Z.wrel wd w → Z.wrel (IR.Sem.effect Z.c wd e vs).2 (Z.dev w (.write p c.a)))
    (hnone : ∀ wd vs, (IR.Sem.effect Z.c wd e vs).1 = none) : RtEff Z e := by
  intro _
  obtain ⟨entry, hsym, hent, hrun⟩ := out_routine ok hsz hport hhas
  refine ⟨entry, hsym, hent, fun c w wd vs hpc I hh hrs hmsz _ _ hw hargs => ?_⟩
  obtain ⟨c', p, hp, st, hpc', hsp', hh', hrs', hmem'⟩ := hrun c w hpc I hh
  refine ⟨c', _, st, hpc', hsp', hh', hrs', by rw [hmem']; exact hmsz, fun x _ _ => by rw [hmem'],
    hdev wd w p c vs hp hargs hw, ?_⟩
  intro r hr
  rw [hnone] at hr
  cases hr

theorem harness_out_byte (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k [.label "rt_out_byte", .ins ⟨.out, [.mem (.num 0xD3), .a]⟩, .ins ⟨.ret, []⟩]) :
    RtEff Z .outByte :=
  harness_out ok hsz (port := 0xD3) (by decide) .outByte hhas
    (fun wd w p c vs hp hargs hw => by
      have hv : vs = [c.a.toNat] := hargs
      rw [hv]
      exact H.wrByte wd w p c.a hp hw) (fun _ _ => rfl)

theorem harness_out_end (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k [.label "rt_out_end", .ins ⟨.out, [.mem (.num 0xD4), .a]⟩, .ins ⟨.ret, []⟩]) :
    RtEff Z .outEnd :=
  harness_out ok hsz (port := 0xD4) (by decide) .outEnd hhas
    (fun wd w p c vs hp hargs hw => by
      have hv : vs = [] := hargs
      rw [hv]
      exact H.wrEnd wd w p c.a hp hw) (fun _ _ => rfl)

theorem harness_drop (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k [.label "rt_drop", .ins ⟨.out, [.mem (.num 0xD5), .a]⟩, .ins ⟨.ret, []⟩]) :
    RtEff Z .drop :=
  harness_out ok hsz (port := 0xD5) (by decide) .drop hhas
    (fun wd w p c vs hp hargs hw => by
      have hv : vs = [c.a.toNat] := hargs
      rw [hv]
      exact H.wrDrop wd w p c.a hp hw) (fun _ _ => rfl)

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
   .ins ⟨.cp, [.imm (.num 1)]⟩, .ins ⟨.jr, [.z, .imm (.sym "rt_input_tick")]⟩,
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

/-- **The harness's `rt_input`**: it takes the next item of input.  It writes no memory. -/
theorem harness_input_core (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k inputItems) :
    ∃ entry, Z.sym "rt_input" entry ∧ entry < 65536 ∧
      ∀ (c : Cpu) (w : Z.W) (wd : World), c.pc.toNat = entry → Img Z.a 0 c → c.halted = false → Z.wrel wd w →
        ∃ c' w', WSteps Z (c, w) (c', w') ∧ c'.pc = c.rd16 c.sp ∧ c'.sp = c.sp + 2 ∧ c'.halted = false ∧
          c'.ramStart = c.ramStart ∧ c'.mem = c.mem ∧ Z.wrel wd.next.2 w' ∧ c'.hl.toNat = wd.next.1.toNat := by
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 0 rfl)
  refine ⟨T, hsym, by omega, fun c w wd hpc I hh hw => ?_⟩
  have hwd : (H.view w).1 = wd := H.wrelView wd w hw
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
  have ha1 : c1.a = kindOf wd := by rw [hc1]; simp only [zsim]; rw [H.busKind w p hlo, hwd]
  have hw1 : Z.wrel wd.next.2 (Z.dev w (.read p)) := H.rdNext wd w p hlo hw
  have hv1l := H.rdLatch w p hlo
  rw [hwd] at hv1l
  have M1 := M.sys hS1
  -- cp 2; jr z,rt_input_none
  obtain ⟨st2, at3, M2, hS2⟩ := does_raw ok (does_cp_n 2) (hhas.get 2 rfl) M1 (at2 rfl)
  obtain ⟨c3, st3, M3, hS3, hK3, hbr3⟩ := jr_cc_step ok true (l := "rt_input_none") (hhas.get 3 rfl)
    (hhas.get 13 rfl) M2 at3
  rw [cpN_z 2 (by decide), ha1] at hbr3
  have hS03 : Sys c c3 := (hS1.trans hS2).trans hS3
  have ha3 : c3.a = kindOf wd := by rw [hK3.1, cpN_a, ha1]
  have st03 : WSteps Z (c, w) (c3, Z.dev w (.read p)) :=
    st1.trans (Steps.lift ok (st2.trans st3) _)
  by_cases hk2 : kindOf wd = 2
  · -- nothing
    have hn : wd.next.1 = 0xFFFF := by
      unfold kindOf at hk2
      split at hk2
      · assumption
      · split at hk2 <;> cases hk2
    rw [hk2] at hbr3
    simp only [show ((2 : UInt8).toNat == 2) = true from rfl, if_true] at hbr3
    obtain ⟨c', st4, hpc', hsp', hmem', hh', hrs', hhl'⟩ := ld_hl_ret ok 0xFFFF (by decide) (hhas.get 14 rfl)
      (hhas.get 15 rfl) M3 (at_label ok (hhas.get 13 rfl) hbr3)
    refine ⟨c', _, st03.trans (Steps.lift ok st4 _), ?_, by rw [hsp', hS03.2.2.2], by rw [hh', hS03.2.2.1]; exact hh,
      by rw [hrs', hS03.2.1], by rw [hmem', hS03.1], hw1, ?_⟩
    · rw [hpc', hS03.2.2.2]
      simp only [Cpu.rd16, Cpu.rd, hS03.1]
    · rw [hhl', hn]
      rfl
  -- something: a tick or a byte
  have hne2 : ((kindOf wd).toNat == 2) = false := by
    simpa using fun h => hk2 (UInt8.toNat_inj.mp h)
  rw [hne2] at hbr3
  simp only [Bool.false_eq_true, if_false] at hbr3
  obtain ⟨st4, at5, M4, hS4⟩ := does_raw ok (does_cp_n 1) (hhas.get 4 rfl) M3 hbr3
  obtain ⟨c5, st5, M5, hS5, hK5, hbr5⟩ := jr_cc_step ok true (l := "rt_input_tick") (hhas.get 5 rfl)
    (hhas.get 10 rfl) M4 at5
  rw [cpN_z 1 (by decide), ha3] at hbr5
  have hS05 : Sys c c5 := (hS03.trans hS4).trans hS5
  have st05 : WSteps Z (c, w) (c5, Z.dev w (.read p)) := st03.trans (Steps.lift ok (st4.trans st5) _)
  by_cases hk1 : kindOf wd = 1
  · -- a tick
    have hn : wd.next.1 = 0x0100 := by
      unfold kindOf at hk1
      split at hk1
      · cases hk1
      · split at hk1
        · assumption
        · cases hk1
    rw [hk1] at hbr5
    simp only [show ((1 : UInt8).toNat == 1) = true from rfl, if_true] at hbr5
    obtain ⟨c', st6, hpc', hsp', hmem', hh', hrs', hhl'⟩ := ld_hl_ret ok 0x0100 (by decide) (hhas.get 11 rfl)
      (hhas.get 12 rfl) M5 (at_label ok (hhas.get 10 rfl) hbr5)
    refine ⟨c', _, st05.trans (Steps.lift ok st6 _), ?_, by rw [hsp', hS05.2.2.2], by rw [hh', hS05.2.2.1]; exact hh,
      by rw [hrs', hS05.2.1], by rw [hmem', hS05.1], hw1, ?_⟩
    · rw [hpc', hS05.2.2.2]
      simp only [Cpu.rd16, Cpu.rd, hS05.1]
    · rw [hhl', hn]
      rfl
  · -- a byte
    have hn : wd.next.1.toNat < 256 := by
      rcases next_cases wd with h | h | h
      · exact absurd (by simp [kindOf, h]) hk2
      · exact absurd (by simp [kindOf, h]) hk1
      · exact h
    have hne1 : ((kindOf wd).toNat == 1) = false := by
      simpa using fun h => hk1 (UInt8.toNat_inj.mp h)
    rw [hne1] at hbr5
    simp only [Bool.false_eq_true, if_false] at hbr5
    -- in a,(0xD2)
    obtain ⟨p2, hp2⟩ : ∃ p2 : UInt16, p2 = mk16 (op1 c5).a (byteOf (Int.ofNat 0xD2)) := ⟨_, rfl⟩
    have hlo2 : lo p2 = 0xD2 := by rw [hp2, lo_mk16]; rfl
    obtain ⟨c6, hc6⟩ : ∃ c6 : Cpu, c6 = (({ (skip (op1 c5) 1) with
        a := Z.bus (Z.dev w (.read p)) p2, io := .read p2 } : Cpu).tick 11) := ⟨_, rfl⟩
    obtain ⟨st6, at7⟩ := wstep_item ok (hhas.get 6 rfl) M5 hbr5 (Z.dev w (.read p)) (s' := c6)
      (fun ad _ => by rw [hc6, hp2]; rfl)
    have hio6 : c6.io = .read p2 := by rw [hc6]; rfl
    rw [hio6] at st6
    have hS6 : Sys c5 c6 := by rw [hc6]; simp only [Sys, skip, zsim, and_self]
    have ha6 : c6.a = lo wd.next.1 := by
      rw [hc6]
      simp only [zsim]
      rw [H.busByte _ p2 hlo2, hv1l hn]
    have M6 := M5.sys hS6
    obtain ⟨st7, at8, M7, hS7⟩ := does_raw ok does_ld_l_a (hhas.get 7 rfl) M6 (at7 rfl)
    obtain ⟨st8, at9, M8, hS8⟩ := does_raw ok does_ld_h_0 (hhas.get 8 rfl) M7 at8
    obtain ⟨c', st9, hpc', hsp', hmem', hh', hrs', hh2, hl2, _⟩ := ret_raw ok (hhas.get 9 rfl) M8 at9
    have hS : Sys c (ldH0 (ldRA 5 c6)) := ((hS05.trans hS6).trans hS7).trans hS8
    refine ⟨c', _, (st05.trans st6).trans (Steps.lift ok ((st7.trans st8).trans st9) _), ?_, by rw [hsp', hS.2.2.2],
      by rw [hh', hS.2.2.1]; exact hh, by rw [hrs', hS.2.1], by rw [hmem', hS.1],
      H.rdByte _ _ p2 hlo2 hw1, ?_⟩
    · rw [hpc', hS.2.2.2]
      simp only [Cpu.rd16, Cpu.rd, hS.1]
    · rw [show c'.hl = (ldH0 (ldRA 5 c6)).hl from by simp only [Cpu.hl, hh2, hl2]]
      have : (ldH0 (ldRA 5 c6)).hl = mk16 0 c6.a := by
        simp only [ldH0, ldRA, skip, zsim]
        rfl
      rw [this, mk16_toNat, ha6]
      show 0 * 256 + wd.next.1.toUInt8.toNat = _
      rw [UInt16.toNat_toUInt8]
      omega

theorem harness_input (ok : Z.OK) (H : Harness Z) (hsz : Z.a.bytes.size < 65536) {k : Nat}
    (hhas : Has Z k inputItems) (e : Effect) (he : e = .inputNext ∨ e = .ringPop) : RtEff Z e := by
  intro _
  obtain ⟨entry, hsym, hent, hrun⟩ := harness_input_core ok H hsz hhas
  have hname : effectRoutine e = "rt_input" := by rcases he with rfl | rfl <;> rfl
  have heff : ∀ wd vs, IR.Sem.effect Z.c wd e vs = (some wd.next.1.toNat, wd.next.2) := by
    intro wd vs
    rcases he with rfl | rfl <;> rfl
  refine ⟨entry, by rw [hname]; exact hsym, hent, fun c w wd vs hpc I hh hrs hmsz hroom htop hw _ => ?_⟩
  obtain ⟨c', w', st, hpc', hsp', hh', hrs', hmem', hw', hhl⟩ := hrun c w wd hpc I hh hw
  refine ⟨c', w', st, hpc', hsp', hh', hrs', by rw [hmem']; exact hmsz, fun x _ _ => by rw [hmem'], ?_, ?_⟩
  · rw [heff]
    exact hw'
  · intro r hr
    rw [heff] at hr
    cases hr
    exact hhl

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
      exact ⟨j, htrap, at6, M5.1⟩

/-! ## Routines on registers -/

/-- **Instructions that leave memory alone, one after the other**, from the image. -/
theorem does_list (ok : Z.OK) : ∀ (l : List (Instr × (Cpu → Cpu))), (∀ p, p ∈ l → Does p.1 p.2) →
    ∀ (k : Nat) (s : Cpu), Has Z k (l.map fun p => Item.ins p.1) → Mach Z s → At Z.addrs k s →
      Steps s (runL (l.map (·.2)) s) ∧ At Z.addrs (k + l.length) (runL (l.map (·.2)) s) ∧
        Mach Z (runL (l.map (·.2)) s) ∧ Sys s (runL (l.map (·.2)) s)
  | [], _, _, s, _, M, hat => ⟨Steps.refl s, hat, M, Sys.refl s⟩
  | p :: r, hd, k, s, hh, M, hat => by
    obtain ⟨st1, at1, M1, hS1⟩ := does_raw ok (hd p List.mem_cons_self) (hh.get 0 rfl) M hat
    have hr : Has Z (k + 1) (r.map fun p => Item.ins p.1) := fun j it hj => by
      have := hh (j + 1) it (by simpa using hj)
      rw [show k + 1 + j = k + (j + 1) by omega]
      exact this
    obtain ⟨st2, at2, M2, hS2⟩ := does_list ok r (fun q hq => hd q (List.mem_cons_of_mem _ hq)) (k + 1) (p.2 s) hr M1 at1
    refine ⟨st1.trans st2, ?_, M2, hS1.trans hS2⟩
    rw [show k + (p :: r).length = k + 1 + r.length by simp; omega]
    exact at2

theorem Has.tail {k : Nat} {x : Item} {l : List Item} (h : Has Z k (x :: l)) : Has Z (k + 1) l := fun j it hj => by
  have := h (j + 1) it (by simpa using hj)
  rw [show k + 1 + j = k + (j + 1) by omega]
  exact this

theorem Has.pre {k : Nat} {l1 l2 : List Item} (h : Has Z k (l1 ++ l2)) : Has Z k l1 := fun j it hj => by
  have hlt : j < l1.length := by
    rcases Nat.lt_or_ge j l1.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  exact h j it (by rw [List.getElem?_append_left hlt]; exact hj)

theorem cplA_h (s : Cpu) : (cplA s).h = s.h := by simp only [cplA, zsim]
theorem cplA_l (s : Cpu) : (cplA s).l = s.l := by simp only [cplA, zsim]
theorem ldRR74_a (s : Cpu) : (ldRR 7 4 s).a = s.h := by simp only [ldRR, zsim]
theorem ldRR74_l (s : Cpu) : (ldRR 7 4 s).l = s.l := by simp only [ldRR, zsim]
theorem ldRR75_a (s : Cpu) : (ldRR 7 5 s).a = s.l := by simp only [ldRR, zsim]
theorem ldRR75_h (s : Cpu) : (ldRR 7 5 s).h = s.h := by simp only [ldRR, zsim]
theorem ldRA4_h (s : Cpu) : (ldRA 4 s).h = s.a := by simp only [ldRA, zsim]
theorem ldRA4_l (s : Cpu) : (ldRA 4 s).l = s.l := by simp only [ldRA, zsim]
theorem ldRA5_l (s : Cpu) : (ldRA 5 s).l = s.a := by simp only [ldRA, zsim]
theorem ldRA5_h (s : Cpu) : (ldRA 5 s).h = s.h := by simp only [ldRA, zsim]

def not16Items : List Item :=
  [.label "rt_not16", .ins ⟨.ld, [.a, .h]⟩, .ins ⟨.cpl, []⟩, .ins ⟨.ld, [.h, .a]⟩, .ins ⟨.ld, [.a, .l]⟩, .ins ⟨.cpl, []⟩,
   .ins ⟨.ld, [.l, .a]⟩, .ins ⟨.ret, []⟩]

/-- **`rt_not16`**: `HL := ~HL`.  It uses no stack and writes no memory. -/
theorem rt_not16_ok (ok : Z.OK) (hsz : Z.a.bytes.size < 65536) {k : Nat} (hhas : Has Z k not16Items) :
    RtPure Z "rt_not16" (fun s s' => s'.hl.toNat = 65535 - s.hl.toNat) := by
  intro _
  obtain ⟨T, hT, hsym, hTle⟩ := label_sym ok (hhas.get 0 rfl)
  refine ⟨T, hsym, by omega, fun s hpc I hh hrs hmsz _ _ _ => ?_⟩
  have M : Mach Z s := ⟨I, hh⟩
  have at1 : At Z.addrs (k + 1) s := at_label ok (hhas.get 0 rfl) ⟨T, hT, hpc⟩
  obtain ⟨st1, at2, M2, hS⟩ := does_list ok
    [(⟨.ld, [.a, .h]⟩, ldRR 7 4), (⟨.cpl, []⟩, cplA), (⟨.ld, [.h, .a]⟩, ldRA 4), (⟨.ld, [.a, .l]⟩, ldRR 7 5),
     (⟨.cpl, []⟩, cplA), (⟨.ld, [.l, .a]⟩, ldRA 5)]
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact does_ld_a_h
      · exact does_cpl
      · exact does_ld_h_a
      · exact does_ld_a_l
      · exact does_cpl
      · exact does_ld_l_a)
    (k + 1) s (Has.pre (l2 := [.ins ⟨.ret, []⟩]) hhas.tail) M at1
  obtain ⟨c, hc⟩ : ∃ c : Cpu, c = ldRA 5 (cplA (ldRR 7 5 (ldRA 4 (cplA (ldRR 7 4 s))))) := ⟨_, rfl⟩
  have hrun : runL ([(⟨.ld, [.a, .h]⟩, ldRR 7 4), (⟨.cpl, []⟩, cplA), (⟨.ld, [.h, .a]⟩, ldRA 4),
      (⟨.ld, [.a, .l]⟩, ldRR 7 5), (⟨.cpl, []⟩, cplA), ((⟨.ld, [.l, .a]⟩ : Instr), ldRA 5)].map (·.2)) s = c := by
    rw [hc]
    rfl
  rw [hrun] at st1 at2 M2 hS
  obtain ⟨s', st2, hpc', hsp', hmem', hh', hrs', hh2, hl2, _⟩ := ret_raw ok (hhas.get 7 rfl) M2 at2
  refine ⟨s', st1.trans st2, ?_, by rw [hsp', hS.2.2.2], by rw [hh', hS.2.2.1]; exact hh, by rw [hrs', hS.2.1],
    by rw [hmem', hS.1]; exact hmsz, ?_, fun x _ _ => by rw [hmem', hS.1]⟩
  · rw [hpc', hS.2.2.2]
    simp only [Cpu.rd16, Cpu.rd, hS.1]
  · show s'.hl.toNat = 65535 - s.hl.toNat
    have hH : s'.h.toNat = 255 - s.h.toNat := by
      rw [hh2, hc, ldRA5_h, cplA_h, ldRR75_h, ldRA4_h, cplA_a, ldRR74_a]
    have hL : s'.l.toNat = 255 - s.l.toNat := by
      rw [hl2, hc, ldRA5_l, cplA_a, ldRR75_a, ldRA4_l, cplA_l, ldRR74_l]
    rw [hl_toNat, hl_toNat, hH, hL]
    have := s.h.toNat_lt
    have := s.l.toNat_lt
    omega

end

end Ember.Proof.Z80Gen
