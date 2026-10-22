import Ember.Proof.Z80Image
import Ember.Proof.Z80World

/-!
# Ember.Proof.Z80HarnessW — the machine of the test harness, for any image (plan M7.3)

The world behind the harness's ports (`hbus`, `hdev`), what the machine
stands for (`hrel`), and for an image `I` the setting of the proofs in
that machine (`ImgIn.ZH`) with what the routines of the harness's
effects need of it (`ImgIn.harness`).  Used for the loopback image
(`Z80LoopH`) and for the image of the stack (`Z80StackH`).
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc Ember.Proof.IRSim
open Ember.Lang (World Effect)

/-! ## The machine of the harness -/

/-- The machine's state: the world, the byte latched by the last read
of `0xD1` that took one, and the position in the input when `0xD9` was
last read, and the value of the note to come (what has been written
of it to `0xDA`, and how many bytes). -/
abbrev HW := World × UInt8 × (Nat × Nat) × (Nat × Nat)

def hbus (w : HW) (p : UInt16) : UInt8 :=
  if lo p = 0xD0 then (if kindOf w.1 = 2 then 0 else 1)
  else if lo p = 0xD1 then kindOf w.1
  else if lo p = 0xD2 then w.2.1
  else if lo p = 0xD8 then 0      -- which program of the image: the first
  else if lo p = 0xD9 then (if (w.1.pos, w.1.off) ≠ w.2.2.1 then 1 else 0)
  else 0xFF

def hdev (c : IR.Ctx) (w : HW) : IoEvent → HW
  | .none => w
  | .read p =>
    if lo p = 0xD1 then (w.1.next.2, if w.1.next.1.toNat < 256 then lo w.1.next.1 else w.2.1, w.2.2)
    else if lo p = 0xD9 then (w.1, w.2.1, (w.1.pos, w.1.off), w.2.2.2)
    else w
  | .write p v =>
    if lo p = 0xD3 then ((IR.Sem.effect c w.1 .outByte [v.toNat]).2, w.2)
    else if lo p = 0xD4 then ((IR.Sem.effect c w.1 .outEnd []).2, w.2)
    else if lo p = 0xD5 then ((IR.Sem.effect c w.1 .drop [v.toNat]).2, w.2)
    else if lo p = 0xDA then (w.1, w.2.1, w.2.2.1, (w.2.2.2.1 + v.toNat * 2 ^ (8 * w.2.2.2.2), w.2.2.2.2 + 1))
    else if lo p = 0xD6 then ((IR.Sem.effect c w.1 .note [v.toNat, w.2.2.2.1]).2, w.2.1, w.2.2.1, (0, 0))
    else if lo p = 0xD7 then ({ w.1 with trapped := true }, w.2)  -- the trap, recorded in the world
    else w

/-- The machine stands for the world `wd`, its mark at `μ`, no byte of
a note's value pending. -/
def hrel (μ : Nat × Nat) (wd : World) (w : HW) : Prop := w.1 = wd ∧ w.2.2.1 = μ ∧ w.2.2.2 = (0, 0)

/-- The setting: the plan of the image, the image, the harness.  `μ` is
where the mark is — the functions leave it (only the loop reads `0xD9`),
which is said by taking it into what the machine stands for. -/
def ImgIn.ZH (I : ImgIn) (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) : ZCtx :=
  I.plan.toZ (I.around a addrs HW hbus (hdev I.ctx) (hrel μ))

def ImgIn.harness (I : ImgIn) (a : Assembled) (addrs : List Nat) (μ : Nat × Nat) : Harness (I.ZH a addrs μ) where
  view := fun w => (w.1, w.2.1)
  wrelView := fun _ _ h => h.1
  busKind := fun w p h => by show hbus w p = _; simp [hbus, h]
  busByte := fun w p h => by show hbus w p = _; simp [hbus, h]
  rdNext := fun wd w p h hw => by
    show hrel μ _ (hdev I.ctx w (.read p))
    obtain ⟨h1, h2⟩ := hw
    simp only [hdev, h, if_true]
    exact ⟨by rw [h1], h2⟩
  rdLatch := fun w p h hn => by show (hdev I.ctx w (.read p)).2.1 = _; simp [hdev, h, hn]
  rdByte := fun wd w p h hw => by
    show hrel μ _ (hdev I.ctx w (.read p))
    have : hdev I.ctx w (.read p) = w := by simp [hdev, h]
    rw [this]
    exact hw
  wrByte := fun wd w p v h hw => by
    show hrel μ _ (hdev I.ctx w (.write p v))
    obtain ⟨h1, h2⟩ := hw
    simp only [hdev, h, if_true]
    exact ⟨by rw [h1]; rfl, h2⟩
  wrEnd := fun wd w p v h hw => by
    show hrel μ _ (hdev I.ctx w (.write p v))
    obtain ⟨h1, h2⟩ := hw
    have : hdev I.ctx w (.write p v) = ((IR.Sem.effect I.ctx w.1 .outEnd []).2, w.2) := by simp [hdev, h]
    rw [this]
    exact ⟨by rw [h1]; rfl, h2⟩
  wrNote := fun wd w p0 p1 p2 p3 p b0 b1 b2 b3 k h0 h1 h2 h3 h hw => by
    show hrel μ _ (hdev I.ctx (hdev I.ctx (hdev I.ctx (hdev I.ctx (hdev I.ctx w (.write p0 b0))
      (.write p1 b1)) (.write p2 b2)) (.write p3 b3)) (.write p k))
    obtain ⟨e1, e2, e3⟩ := hw
    simp only [hdev, h0, h1, h2, h3, h, e3, show ¬ ((0xDA : UInt8) = 0xD3) by decide, show ¬ ((0xDA : UInt8) = 0xD4) by decide,
      show ¬ ((0xDA : UInt8) = 0xD5) by decide, show ¬ ((0xD6 : UInt8) = 0xD3) by decide,
      show ¬ ((0xD6 : UInt8) = 0xD4) by decide, show ¬ ((0xD6 : UInt8) = 0xD5) by decide,
      show ¬ ((0xD6 : UInt8) = 0xDA) by decide, if_true, if_false]
    refine ⟨?_, e2, rfl⟩
    rw [e1]
    have hv : 0 + b0.toNat * 2 ^ (8 * 0) + b1.toNat * 2 ^ (8 * (0 + 1)) + b2.toNat * 2 ^ (8 * (0 + 1 + 1)) +
        b3.toNat * 2 ^ (8 * (0 + 1 + 1 + 1)) =
        b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 * 0))) := by
      rw [show (2 : Nat) ^ (8 * 0) = 1 from rfl, show (2 : Nat) ^ (8 * (0 + 1)) = 256 from rfl,
        show (2 : Nat) ^ (8 * (0 + 1 + 1)) = 65536 from rfl, show (2 : Nat) ^ (8 * (0 + 1 + 1 + 1)) = 16777216 from rfl]
      omega
    rw [hv]
    rfl
  wrDrop := fun wd w p v h hw => by
    show hrel μ _ (hdev I.ctx w (.write p v))
    obtain ⟨h1, h2⟩ := hw
    have : hdev I.ctx w (.write p v) = ((IR.Sem.effect I.ctx w.1 .drop [v.toNat]).2, w.2) := by simp [hdev, h]
    rw [this]
    exact ⟨by rw [h1]; rfl, h2⟩

/-- The machine runs the same whatever the mark is taken to be. -/
theorem ImgIn.wrun_mark (I : ImgIn) (a : Assembled) (addrs : List Nat) (μ μ' : Nat × Nat) : ∀ (n : Nat) (x : Cpu × HW),
    wrun (I.ZH a addrs μ) n x = wrun (I.ZH a addrs μ') n x
  | 0, _ => rfl
  | n + 1, x => by
    show wrun (I.ZH a addrs μ) n (wstep (I.ZH a addrs μ) x) = wrun (I.ZH a addrs μ') n (wstep (I.ZH a addrs μ') x)
    rw [ImgIn.wrun_mark I a addrs μ μ' n]
    rfl

theorem ImgIn.wsteps_mark {I : ImgIn} {a : Assembled} {addrs : List Nat} {μ μ' : Nat × Nat} {x y : Cpu × HW}
    (h : WSteps (I.ZH a addrs μ) x y) : WSteps (I.ZH a addrs μ') x y := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [← ImgIn.wrun_mark I a addrs μ μ' n]; exact hn⟩

end Ember.Proof.Z80Gen
