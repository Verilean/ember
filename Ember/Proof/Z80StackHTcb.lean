import Ember.Proof.Z80StackHMachine
import Ember.Proof.TcbCheckpoint

/-!
# Ember.Proof.Z80StackHTcb — the connection's state in the IR's memory (plan M7.3, `tcb` lines)

`TcbCheckpoint.tcb_checkpoint` finds the Spec's control block, after
every input item, in the globals `t` and `pend` of the Ember semantics.
Here one level down: `lower_iter_mem` — `lower_iter` with the memory —
the IR's state after the same calls of `main` holds every global of the
Ember program at its address in the layout (`GRel`); and for the stack
(`stackH_tcb_ir`) the bytes at the addresses of `t` and `pend`, in the
IR's memory after `j + 1` calls of `main`, hold a connection record and
an echo buffer that hold the Spec's control block after the first
`j + 1` items, and describe as it does (`RawTcb.describe`).

And in the RAM of the machine the tests run (`stackH_tcb_ram`): at the
head of the harness's loop the RAM has the plan's shared bytes as the
IR's memory does (`AtLoop.mem`), and `t` and `pend` are shared bytes
(`inIv_tcb`), so after `j + 1` calls the RAM holds the same record and
buffer — or the machine stopped before, the input used up.  Which step
of the run that is, is said here only by its existence; the observer of
`Ember.Z80.TcbObs` and `Z80StackHTcbObs` fix it.

Not here: the lines themselves.
-/

namespace Ember.Proof.Z80Gen.StackH
open Ember Ember.Z80 Ember.Z80.Asm
open Ember.Proof.IRSim
open Ember.Proof.Refine (mainIter later main_run TcbRel RawTcb RawTcb.describe TcbRel.describe_eq specAfter
  tcb_checkpoint)
open Ember.Lang.Sem (bufVal)
open Ember.Proof.CSim (TyOK HasTy)
open Ember.Proof.Z80Enc (At)
open Ember.Proof.Z80Gen.LoopH (Sim mrun harnessMachine harness_reset run_sim_of)

theorem grel_layout {lp : Lang.Prog} {c c' : IR.Ctx} {m : ByteArray} {gs : Lang.Sem.Env} (h : GRel lp c m gs)
    (hl : c'.layout = c.layout) : GRel lp c' m gs := by
  have ha : ∀ x, gaddr c' x = gaddr c x := fun x => by unfold gaddr; rw [hl]
  refine ⟨h.names, fun g hg => ?_⟩
  rw [ha]
  exact h.vals g hg

/-- **`lower_iter` with the memory**: the IR's state after the calls
holds every global of the Ember semantics at its address. -/
theorem lower_iter_mem {lp : Lang.Prog} {q' : IR.Prog} (hl : IR.lower lp = .ok q') (l : IR.Layout)
    (hok : progOkB lp = true) (hir : irOkB lp l = true) (inputs : Array Trace.Input) (k j : Nat) (st' : Lang.Sem.St)
    (hi : callIter k lp j (Lang.Sem.initial lp inputs) = some st') :
    ∃ m ist', irIter m (irCtx lp q' l) j (irInit lp q' l inputs) = some ist' ∧ ist'.world = st'.world ∧
      ist'.mem.size = 65536 ∧ GRel lp (irCtx lp q' l) ist'.mem st'.globals := by
  obtain ⟨q, rfl, L, hlow, he, hslot, hG0⟩ := lower_rel hl l hok hir inputs
  obtain ⟨hPok, fd, hE, hpar⟩ := progOkB_sound hok
  obtain ⟨m, ist', hit, hG'⟩ := iter_sim L hlow hPok he fd hE hpar k j _ st' _ hG0 hi
  obtain ⟨m', hm'⟩ := tidy_iter (c := irCtx lp q l) hlow.uniq
    (fun g f hf => hslot f (List.mem_of_find?_eq_some hf)) j m _ _ hit
  exact ⟨m', ist', hm', hG'.2.1, hG'.1, grel_layout hG'.2.2 rfl⟩

/-- **The connection in the IR's memory, after every item**: for the
stack, after `j + 1` calls of `main` the IR's memory holds, at the
address of the global `t`, a connection record and, at that of `pend`,
an echo buffer that hold the Spec's control block after the first
`j + 1` items; the record describes as the control block does. -/
theorem stackH_tcb_ir (p : Lang.Prog) (S : StackSrc p) (inputs : Array Trace.Input) (j : Nat) :
    ∃ (st' : Lang.Sem.St) (m : Nat) (ist' : IR.Sem.St) (r : RawTcb) (pd : ByteArray) (gt gp : Lang.Global),
      mainIter 4716 p (j + 1) (Lang.Sem.initial p inputs) = some st' ∧
      irIter m img.ctx (j + 1) (st0 inputs) = some ist' ∧ ist'.world = st'.world ∧
      p.global? "t" = some gt ∧ Holds p ist'.mem (gaddr img.ctx "t") gt.ty r.val ∧
      p.global? "pend" = some gp ∧ Holds p ist'.mem (gaddr img.ctx "pend") gp.ty (bufVal pd) ∧
      TcbRel r pd (specAfter inputs (j + 1)).tcb ∧ r.describe = (specAfter inputs (j + 1)).tcb.describe ∧
      TyOK p gt.ty ∧ HasTy p gt.ty r.val ∧ TyOK p gp.ty ∧ HasTy p gp.ty (bufVal pd) := by
  have hctx : irCtx p Stack.ir layout = img.ctx := by
    unfold irCtx
    rw [S.drops, S.notes]
    rfl
  have hst0 : irInit p Stack.ir layout inputs = st0 inputs := by
    unfold irInit
    rw [S.framed]
    rfl
  have hinit : Lang.Sem.initial p inputs = Lang.Sem.initial Net.prog inputs :=
    Ember.Proof.CSim.initial_congr p Net.prog S.globals S.structs (by rw [S.framed]; rfl) inputs
  obtain ⟨st', r, pd, hit, ht, hpd, hrel, hdesc⟩ := tcb_checkpoint p S.all S.reasons S.main inputs 0 j
  rw [Nat.zero_add, ← hinit] at hit
  obtain ⟨m, ist', hiti, hw, _, hG⟩ := lower_iter_mem S.lowered layout S.okP S.okIR inputs 4716 (j + 1) st'
    (by rw [← mainIter_eq p S.entry]; exact hit)
  rw [hctx, hst0] at hiti
  rw [hctx] at hG
  have hgt : ∃ g, p.global? "t" = some g := by
    unfold Lang.Prog.global?
    rw [S.globals]
    exact ⟨_, rfl⟩
  have hgp : ∃ g, p.global? "pend" = some g := by
    unfold Lang.Prog.global?
    rw [S.globals]
    exact ⟨_, rfl⟩
  obtain ⟨gt, hgt⟩ := hgt
  obtain ⟨gp, hgp⟩ := hgp
  obtain ⟨vt, hvt, hTt, hVt, hHt, _⟩ := hG.lookup hgt
  obtain ⟨vp, hvp, hTp, hVp, hHp, _⟩ := hG.lookup hgp
  rw [ht] at hvt
  rw [hpd] at hvp
  cases hvt
  cases hvp
  exact ⟨st', m, ist', r, pd, gt, gp, hit, hiti, hw, hgt, hHt, hgp, hHp, hrel, hdesc, hTt, hVt, hTp, hVp⟩

/-- info: 'Ember.Proof.Z80Gen.StackH.stackH_tcb_ir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackH_tcb_ir

/-! ## In the Z80's RAM -/

theorem sizeOf_structs {p q : Lang.Prog} (h : p.structs = q.structs) : ∀ t, IR.sizeOf p t = IR.sizeOf q t := by
  intro t
  induction t with
  | arr el n ih => simp only [IR.sizeOf, ih]
  | record r => simp only [IR.sizeOf, Lang.Prog.struct?, h]
  | _ => rfl

theorem gaddr_t : gaddr img.ctx "t" = 32777 := by decide
theorem gaddr_pend : gaddr img.ctx "pend" = 32812 := by decide

theorem size_t (p : Lang.Prog) (S : StackSrc p) {g : Lang.Global} (h : p.global? "t" = some g) :
    IR.sizeOf p g.ty = 35 := by
  have h' : Net.prog.global? "t" = some g := by
    rw [← h]; unfold Lang.Prog.global?; rw [S.globals]
  rw [sizeOf_structs S.structs]
  obtain rfl : g = (Net.prog.global? "t").get! := by rw [h']; rfl
  decide

theorem size_pend (p : Lang.Prog) (S : StackSrc p) {g : Lang.Global} (h : p.global? "pend" = some g) :
    IR.sizeOf p g.ty = 256 := by
  have h' : Net.prog.global? "pend" = some g := by
    rw [← h]; unfold Lang.Prog.global?; rw [S.globals]
  rw [sizeOf_structs S.structs]
  obtain rfl : g = (Net.prog.global? "pend").get! := by rw [h']; rfl
  decide

/-- The bytes of `t` and `pend` are shared bytes of the plan: at the
head of the loop the RAM has them as the IR's memory does. -/
theorem inIv_tcb (x : Nat) (h1 : 32777 ≤ x) (h2 : x < 33068) : inIv img.plan.data x = true := by
  obtain ⟨rest, hd⟩ : ∃ rest, img.plan.data = (32777, 32812) :: (32812, 33068) :: rest := ⟨_, rfl⟩
  rw [hd]
  unfold inIv
  simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **The connection in the RAM of the machine the tests run, after
every item**: the image of the stack loaded and stepped as the tests do,
for any input and any `j`, either the machine gets to the head of its
loop after `j + 1` calls of `main`, its RAM holding at the address of
`t` a connection record and at that of `pend` an echo buffer that hold
the Spec's control block after the first `j + 1` items (and the record
describes as it does) — or it stopped before, the input used up after
`i ≤ j + 1` calls. -/
theorem stackH_tcb_ram (p : Lang.Prog) (S : StackSrc p) :
    ∃ (a : Assembled) (addrs : List Nat), assemble items = .ok a ∧
      ∀ (inputs : Array Trace.Input) (j : Nat),
        (∃ (n : Nat) (r : RawTcb) (pd : ByteArray) (gt gp : Lang.Global),
          At addrs 2589 (mrun n (harnessMachine a inputs)).cpu ∧
          (mrun n (harnessMachine a inputs)).cpu.halted = false ∧
          p.global? "t" = some gt ∧ Holds p (mrun n (harnessMachine a inputs)).cpu.mem 32777 gt.ty r.val ∧
          p.global? "pend" = some gp ∧ Holds p (mrun n (harnessMachine a inputs)).cpu.mem 32812 gp.ty (bufVal pd) ∧
          TcbRel r pd (specAfter inputs (j + 1)).tcb ∧ r.describe = (specAfter inputs (j + 1)).tcb.describe) ∨
        (∃ (n i : Nat) (sti : Lang.Sem.St), i ≤ j + 1 ∧ (mrun n (harnessMachine a inputs)).cpu.halted = true ∧
          mainIter 4716 p i (Lang.Sem.initial p inputs) = some sti ∧ sti.world.next.1 = 0xFFFF) := by
  obtain ⟨a, addrs, ha, hrun⟩ := stackH_run
  have hsz : a.bytes.size ≤ 0x8000 := by
    have h := assemble_items
    rw [ha] at h
    cases h
    simpa using rom_size
  refine ⟨a, addrs, ha, fun inputs j => ?_⟩
  have R := harness_reset a inputs hsz
  have S0 : Sim img.ctx (harnessMachine a inputs) ((st0 inputs).world, 0, (0, 0), (0, 0)) :=
    ⟨R.harness, R.noRx, R.rdrf, R.tick, R.prog, R.inputs, R.pos, R.off, R.cur, R.latch, R.mark, R.frame, rfl, by
      rw [R.events]
      rfl, R.nval, by rw [R.events]; show false = _; simp [LoopH.trapIn]⟩
  obtain ⟨lang, det, hmv⟩ := src_facts p S inputs
  obtain ⟨st', m, ist', r, pd, gt, gp, _, hiti, _, hgt, hHt, hgp, hHp, hrel, hdesc, hTt, hVt, hTp, hVp⟩ :=
    stackH_tcb_ir p S inputs j
  rcases hrun inputs _ R.pc R.img R.run R.rs R.msz (j + 1) m ist' (hmv m) hiti with
    ⟨s', w', ⟨n, hn⟩, L⟩ | ⟨i, isti, s', w', hi, hiti', ⟨n, hn⟩, hh, _, _, hex⟩
  · obtain ⟨hc, _⟩ := run_sim_of img a addrs n _ _ S0
    have hn' : wrun (img.ZH a addrs (0, 0)) n ((harnessMachine a inputs).cpu, ((st0 inputs).world, 0, (0, 0), (0, 0))) =
        (s', w') := hn
    rw [hn'] at hc
    simp only at hc
    have st := size_t p S hgt
    have sp := size_pend p S hgp
    left
    refine ⟨n, r, pd, gt, gp, by rw [hc]; exact L.at_, by rw [hc]; exact L.run, hgt, ?_, hgp, ?_, hrel, hdesc⟩
    · rw [hc]
      rw [gaddr_t] at hHt
      exact Holds.frame hTt hVt (by rw [st]; decide) hHt
        (fun x h1 h2 => L.mem x (inIv_tcb x h1 (by rw [st] at h2; omega)))
    · rw [hc]
      rw [gaddr_pend] at hHp
      exact Holds.frame hTp hVp (by rw [sp]; decide) hHp
        (fun x h1 h2 => L.mem x (inIv_tcb x (by omega) (by rw [sp] at h2; omega)))
  · obtain ⟨hc, _⟩ := run_sim_of img a addrs n _ _ S0
    have hn' : wrun (img.ZH a addrs (0, 0)) n ((harnessMachine a inputs).cpu, ((st0 inputs).world, 0, (0, 0), (0, 0))) =
        (s', w') := hn
    rw [hn'] at hc
    simp only at hc
    obtain ⟨sti, m', isti', hk, _, hiti2, hw2⟩ := lang i
    have e : isti = isti' := det i _ _ _ _ hiti' hiti2
    right
    exact ⟨n, i, sti, hi, by rw [hc]; exact hh, hk, by rw [← hw2, ← e]; exact hex⟩

/-- info: 'Ember.Proof.Z80Gen.StackH.stackH_tcb_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackH_tcb_ram

end Ember.Proof.Z80Gen.StackH
