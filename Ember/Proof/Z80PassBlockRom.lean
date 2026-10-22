import Ember.Proof.Z80PassBlock

/-!
# Ember.Proof.Z80PassBlockRom — a routine of the runtime reading a literal of the ROM, in both machines (plan M7.3)

`ld hl,lit` before the call: each machine's `HL` points to the literal in
its own image (the two literals the same bytes, at other addresses), so
`H` and `L` are free in the relation; the routine reads the bytes there,
the same in both, and writes in the RAM kept equal.  The loops are
followed in both machines at once (`HL` of each).
-/

namespace Ember.Proof.PassSim
open Ember.Z80 Ember.Z80.Asm Ember.Z80.Cpu Ember.Proof.Z80Enc Ember.Proof.Z80Gen Ember.Proof.PassLocal

/-- **All the rounds of an `ldir` from the ROM to the RAM kept equal**, in both machines, `H` and `L`
free: the bytes each reads from its own `HL` on the same, below the RAM; the bytes written in it. -/
theorem ldir_rom_rounds (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame} {kA kB : Nat}
    (hA : A.items[kA]? = some (.ins ⟨.ldir, []⟩)) (hB : B.items[kB]? = some (.ins ⟨.ldir, []⟩)) :
    ∀ (n : Nat) (x y : Cpu × D.W), Sync D A B lo hi G kA kB true true x y → x.1.bc.toNat = n + 1 →
      x.1.hl.toNat + n + 1 ≤ lo → y.1.hl.toNat + n + 1 ≤ lo →
      (∀ i, i ≤ n → x.1.mem.get! (x.1.hl.toNat + i) = y.1.mem.get! (y.1.hl.toNat + i)) →
      lo ≤ x.1.de.toNat → x.1.de.toNat + n + 1 ≤ hi →
      Sync D A B lo hi G (kA + 1) (kB + 1) true true (mrun D (n + 1) x) (mrun D (n + 1) y)
  | n, x, y, S, hbc, h1, g1, hby, d1, d2 => by
    have hv : x.1.mem.get! x.1.hl.toNat = y.1.mem.get! y.1.hl.toNat := by
      have := hby 0 (by omega); simpa using this
    have st := seg_ldir D hhi hA hB S hv ⟨d1, by omega⟩
    obtain ⟨eA, _⟩ := ldir_mstep D hA S.LA S.atA x.2
    obtain ⟨eB, _⟩ := ldir_mstep D hB S.LB S.atB y.2
    have hx : mstep D x = (ldirS x.1, x.2) := eA
    have hy : mstep D y = (ldirS y.1, y.2) := eB
    obtain ⟨rh, rd, rb⟩ := ldirS_regs x.1
    obtain ⟨rh', _, _⟩ := ldirS_regs y.1
    cases n with
    | zero =>
      have h0 : x.1.bc - 1 = 0 := by apply UInt16.toNat_inj.mp; rw [toNat_sub1 _ (by omega)]; simp [hbc]
      have hne : ¬ ((x.1.bc - 1 != 0) = true) := by rw [h0]; decide
      rw [if_neg hne] at st
      exact st
    | succ m =>
      have hne : (x.1.bc - 1 != 0) = true := by
        have h' : (x.1.bc - 1).toNat = m + 1 := by rw [toNat_sub1 _ (by omega)]; omega
        have : x.1.bc - 1 ≠ 0 := by intro e; rw [e] at h'; simp at h'
        simp [this]
      rw [if_pos hne] at st
      have hszA : x.1.mem.size = 65536 := S.msz
      have hszB : y.1.mem.size = 65536 := by
        have := S.E.msz; have h2 : (mask true true x.1 y.1).mem = y.1.mem := by cases y.1; rfl
        rw [h2] at this; rw [← this]; exact hszA
      have hrsA : x.1.ramStart.toNat ≤ lo := S.rs
      have hrsB : y.1.ramStart.toNat ≤ lo := by
        have := RegsS.ramStart S.E.regs; rw [mask_ramStart] at this; rw [← this]; exact hrsA
      have hdeB : y.1.de = x.1.de := by
        have := RegsS.de S.E.regs; rw [mask_de] at this; exact this.symm
      have rA : x.1.ramStart.toNat ≤ x.1.de.toNat := by omega
      have rB : y.1.ramStart.toNat ≤ y.1.de.toNat := by rw [hdeB]; omega
      have hyde : lo ≤ y.1.de.toNat := by rw [hdeB]; omega
      have r := ldir_rom_rounds D hhi hA hB m (mstep D x) (mstep D y) st
        (by rw [hx]; simp only; rw [rb, toNat_sub1 _ (by omega)]; omega)
        (by rw [hx]; simp only; rw [rh, toNat_add1 _ (by omega)]; omega)
        (by rw [hy]; simp only; rw [rh', toNat_add1 _ (by omega)]; omega)
        (fun i hi' => by
          rw [hx, hy]; simp only
          rw [rh, rh', toNat_add1 _ (by omega), toNat_add1 _ (by omega),
            ldirS_mem x.1 _ hszA rA, ldirS_mem y.1 _ hszB rB, if_neg (by omega), if_neg (by omega)]
          have := hby (i + 1) (by omega)
          rw [show x.1.hl.toNat + 1 + i = x.1.hl.toNat + (i + 1) by omega,
            show y.1.hl.toNat + 1 + i = y.1.hl.toNat + (i + 1) by omega]
          exact this)
        (by rw [hx]; simp only; rw [rd, toNat_add1 _ (by omega)]; omega)
        (by rw [hx]; simp only; rw [rd, toNat_add1 _ (by omega)]; omega)
      exact r

/-- info: 'Ember.Proof.PassSim.ldir_rom_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ldir_rom_rounds

/-- The bytes of a `db` item are where the item is, in the memory of a CPU running the image. -/
theorem db_mem {C : Code} {d : Nat} {vs : List Val} (hd : C.items[d]? = some (.db vs)) {s : Cpu} (L : Loaded C s)
    {bs : List UInt8} (henc : ∀ ad, Item.encode (.db vs) (C.a.env ad) = .ok bs) :
    ∃ ad, C.addrs[d]? = some ad ∧ ad + bs.length ≤ s.ramStart.toNat ∧
      ∀ j b, bs[j]? = some b → s.mem.get! (ad + j) = b := by
  obtain ⟨ad, bs', h1, h2, _, _, h5, h6, _⟩ := C.placed.2 d _ hd
  rw [henc ad] at h2
  cases h2
  refine ⟨ad, h1, by have := L.1.rom; omega, fun j b hj => ?_⟩
  have := L.1.bytes (ad - 0 + j) b (h5 j b hj)
  simpa using this

/-- A label is where the next item is. -/
theorem label_next {C : Code} {d : Nat} {l : String} (hd : C.items[d]? = some (.label l)) {ad : Nat}
    (had : C.addrs[d]? = some ad) : C.addrs[d + 1]? = some ad := by
  obtain ⟨ad', bs, h1, h2, h3, _⟩ := C.placed.2 d _ hd
  rw [had] at h1; cases h1
  cases h2; simpa using h3

theorem ldHL_hl (s : Cpu) (n : UInt16) : (ldHL s n).hl = n := by
  rw [ldHL_eq]; simp only [Cpu.hl, Ember.Proof.Z80Gen.mk16_hi_lo]

theorem exec_ld_hl_sym (env : Env) (l : String) (s : Cpu) (inp : UInt16 → UInt8) :
    exec env ⟨.ld, [.hl, .imm (.sym l 0)]⟩ s inp = some (ldHL s (Instr.immW env ⟨.ld, [.hl, .imm (.sym l 0)]⟩)) := rfl

theorem mrun_9'' (D : Dev) (x : Cpu × D.W) :
    mrun D 9 x = mstep D (mrun D 4 (mstep D (mstep D (mstep D (mstep D x))))) := by
  show mrun D (4 + (4 + 1)) x = _
  rw [mrun_add, mrun_add]; rfl

set_option maxHeartbeats 4000000 in
/-- **`ld hl,lit` then `call rt_ld32` in both machines**: each image's literal (`.db`, the same bytes in
both) into the accumulator; nine steps of each, the relation at the items after the calls, `H` and
`L` free. -/
theorem blkR_ld32 (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) (hlo : lo ≤ hi) (h1 : 1 ≤ hi)
    {G : List Frame} {kA kB r q acc dA dB : Nat} {lit : String} {vs : List Val} {bs : List UInt8} {th tl : Bool}
    (hA0 : A.items[kA]? = some (.ins ⟨.ld, [.hl, .imm (.sym lit 0)]⟩))
    (hB0 : B.items[kB]? = some (.ins ⟨.ld, [.hl, .imm (.sym lit 0)]⟩))
    (hA : A.items[kA + 1]? = some (.ins ⟨.call, [.imm (.sym "rt_ld32" 0)]⟩))
    (hB : B.items[kB + 1]? = some (.ins ⟨.call, [.imm (.sym "rt_ld32" 0)]⟩))
    (hLA : Has A r ldItems) (hLB : Has B q ldItems)
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : lo ≤ acc ∧ acc + 4 ≤ hi)
    (hlA : A.items[dA]? = some (.label lit)) (hdA : A.items[dA + 1]? = some (.db vs))
    (hlB : B.items[dB]? = some (.label lit)) (hdB : B.items[dB + 1]? = some (.db vs))
    (hencA : ∀ ad, Item.encode (.db vs) (A.a.env ad) = .ok bs)
    (hencB : ∀ ad, Item.encode (.db vs) (B.a.env ad) = .ok bs) (hbs : bs.length = 4)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB th tl x y) (room : hi + 2 ≤ top x.1.sp) :
    Sync D A B lo hi G (kA + 2) (kB + 2) true true (mrun D 9 x) (mrun D 9 y) := by
  have l3A : A.items[r + 3]? = some (.label "rt_ld32") := hLA.get 3 rfl
  have l3B : B.items[q + 3]? = some (.label "rt_ld32") := hLB.get 3 rfl
  have i4A : A.items[r + 4]? = some (.ins (Form.ldBCI (.num 4)).instr) := hLA.get 4 rfl
  have i4B : B.items[q + 4]? = some (.ins (Form.ldBCI (.num 4)).instr) := hLB.get 4 rfl
  have l5A : A.items[r + 5]? = some (.label "rt_ldw") := hLA.get 5 rfl
  have l5B : B.items[q + 5]? = some (.label "rt_ldw") := hLB.get 5 rfl
  have i6A : A.items[r + 6]? = some (.ins (Form.ldDEI (.sym "rt_acc" 0)).instr) := hLA.get 6 rfl
  have i6B : B.items[q + 6]? = some (.ins (Form.ldDEI (.sym "rt_acc" 0)).instr) := hLB.get 6 rfl
  have i7A : A.items[r + 7]? = some (.ins ⟨.ldir, []⟩) := hLA.get 7 rfl
  have i7B : B.items[q + 7]? = some (.ins ⟨.ldir, []⟩) := hLB.get 7 rfl
  have i8A : A.items[r + 8]? = some (.ins ⟨.ret, (none : Option Arg).toList⟩) := hLA.get 8 rfl
  have i8B : B.items[q + 8]? = some (.ins ⟨.ret, (none : Option Arg).toList⟩) := hLB.get 8 rfl
  have hvacc : ∀ pa pb, (A.a.env pa).val (.sym "rt_acc" 0) = (B.a.env pb).val (.sym "rt_acc" 0) := by
    intro pa pb; rw [haccA, haccB]
  -- the literals: where each image has them
  obtain ⟨TA, hTA, hvalA, hTAlt⟩ := label_addr S.LA hlA
  obtain ⟨TB, hTB, hvalB, hTBlt⟩ := label_addr S.LB hlB
  have hTA' := label_next hlA hTA
  have hTB' := label_next hlB hTB
  obtain ⟨sA, w⟩ := x
  obtain ⟨sB, w'⟩ := y
  have hw : w' = w := S.w
  subst hw
  simp only at room
  rw [mrun_9'', mrun_9'']
  -- `ld hl,lit`
  have S0 := seg_ldhl D hhi hA0 hB0 S
  have hnA : ∀ pa, (Instr.immW (A.a.env pa) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩).toNat = TA :=
    fun pa => immW_toNat _ _ _ TA rfl (hvalA pa) hTAlt
  have hnB : ∀ pb, (Instr.immW (B.a.env pb) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩).toNat = TB :=
    fun pb => immW_toNat _ _ _ TB rfl (hvalB pb) hTBlt
  have eA0 : mstep D (sA, w') = (ldHL sA (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩), w') :=
    mstep_exec D hA0 S.LA S.atA w' (fun pa inp => by
      rw [exec_ld_hl_sym]
      rw [show Instr.immW (A.a.env pa) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ =
        Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ from UInt16.toNat_inj.mp (by rw [hnA, hnA])])
      (by rw [ldHL_eq]; rfl)
  have eB0 : mstep D (sB, w') = (ldHL sB (Instr.immW (B.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩), w') :=
    mstep_exec D hB0 S.LB S.atB w' (fun pb inp => by
      rw [exec_ld_hl_sym]
      rw [show Instr.immW (B.a.env pb) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ =
        Instr.immW (B.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ from UInt16.toNat_inj.mp (by rw [hnB, hnB])])
      (by rw [ldHL_eq]; rfl)
  rw [eA0, eB0] at S0 ⊢
  have hlA0 := ldHL_hl sA (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩)
  have hlB0 := ldHL_hl sB (Instr.immW (B.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩)
  have spA0 : (ldHL sA (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩)).sp = sA.sp := by rw [ldHL_eq]; rfl
  have hnA0 := hnA 0
  have hnB0 := hnB 0
  generalize Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ = nA at S0 hlA0 spA0 hnA0 ⊢
  generalize Instr.immW (B.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ = nB at S0 hlB0 hnB0 ⊢
  generalize ldHL sA nA = a0 at S0 hlA0 spA0 ⊢
  generalize ldHL sB nB = b0 at S0 hlB0 ⊢
  -- the call
  obtain ⟨TcA, _, _, _, _, _, eA1, _⟩ := call_mstep D hA l3A S0.LA S0.atA w'
  obtain ⟨TcB, _, _, _, _, _, eB1, _⟩ := call_mstep D hB l3B S0.LB S0.atB w'
  have S1 := (seg_call D hhi hA l3A hB l3B S0 hlo h1 (by simp only; rw [spA0]; exact room)).skip l3A l3B
  rw [eA1, eB1] at S1 ⊢
  obtain ⟨hlA1, _, _⟩ := called_regs a0 (UInt16.ofNat TcA)
  obtain ⟨hlB1, _, _⟩ := called_regs b0 (UInt16.ofNat TcB)
  generalize called a0 (UInt16.ofNat TcA) = a1 at S1 hlA1 ⊢
  generalize called b0 (UInt16.ofNat TcB) = b1 at S1 hlB1 ⊢
  -- `ld bc,4`
  have S2 := (seg_ord D hhi (Form.ldBCI (.num 4)) (by intro h; cases h) i4A i4B
    (imm_same _ _ rfl ⟨by decide, by decide⟩ (val_num 4)) (by simp [Form.readsH]) (by simp [Form.readsL]) S1
    (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)).skip l5A l5B
  have eA2 : mstep D (a1, w') = (ldRP a1 0 (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩), w') :=
    mstep_exec D i4A S1.LA S1.atA w' (fun pa inp => by
      show exec (A.a.env pa) ⟨.ld, [.bc, .imm (.num 4)]⟩ a1 inp = _
      rw [exec_ld_rp _ .bc 0 rfl (by decide)]; rfl) rfl
  have eB2 : mstep D (b1, w') = (ldRP b1 0 (Instr.immW (B.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩), w') :=
    mstep_exec D i4B S1.LB S1.atB w' (fun pb inp => by
      show exec (B.a.env pb) ⟨.ld, [.bc, .imm (.num 4)]⟩ b1 inp = _
      rw [exec_ld_rp _ .bc 0 rfl (by decide)]; rfl) rfl
  have hn4 : (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩).toNat = 4 :=
    immW_toNat _ _ (.num 4) 4 rfl rfl (by decide)
  rw [eA2, eB2] at S2 ⊢
  obtain ⟨bc2, hlA2, _⟩ := ldRP_bc a1 (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩)
  obtain ⟨_, hlB2, _⟩ := ldRP_bc b1 (Instr.immW (B.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩)
  generalize ldRP a1 0 (Instr.immW (A.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩) = a2 at S2 bc2 hlA2 ⊢
  generalize ldRP b1 0 (Instr.immW (B.a.env 0) ⟨.ld, [.bc, .imm (.num 4)]⟩) = b2 at S2 hlB2 ⊢
  simp only [Form.writesH, Form.writesL] at S2
  -- `ld de,rt_acc`
  have S3 := seg_ord D hhi (Form.ldDEI (.sym "rt_acc" 0)) (by intro h; cases h) i6A i6B
    (imm_same _ _ rfl ⟨by decide, by decide⟩ hvacc) (by simp [Form.readsH]) (by simp [Form.readsL]) S2
    (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
  have eA3 : mstep D (a2, w') = (ldRP a2 1 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩), w') :=
    mstep_exec D i6A S2.LA S2.atA w' (fun pa inp => by
      show exec (A.a.env pa) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩ a2 inp = _
      rw [exec_ld_rp _ .de 1 rfl (by decide)]
      congr 2
      apply UInt16.toNat_inj.mp
      rw [immW_toNat _ _ _ acc rfl (haccA pa) (by omega), immW_toNat _ _ _ acc rfl (haccA 0) (by omega)]) rfl
  have eB3 : mstep D (b2, w') = (ldRP b2 1 (Instr.immW (B.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩), w') :=
    mstep_exec D i6B S2.LB S2.atB w' (fun pb inp => by
      show exec (B.a.env pb) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩ b2 inp = _
      rw [exec_ld_rp _ .de 1 rfl (by decide)]
      congr 2
      apply UInt16.toNat_inj.mp
      rw [immW_toNat _ _ _ acc rfl (haccB pb) (by omega), immW_toNat _ _ _ acc rfl (haccB 0) (by omega)]) rfl
  have hacc3 : (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩).toNat = acc :=
    immW_toNat _ _ _ acc rfl (haccA 0) (by omega)
  rw [eA3, eB3] at S3 ⊢
  obtain ⟨de3, hlA3, bc3⟩ := ldRP_de a2 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩)
  obtain ⟨_, hlB3, _⟩ := ldRP_de b2 (Instr.immW (B.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩)
  generalize ldRP a2 1 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩) = a3 at S3 de3 hlA3 bc3 ⊢
  generalize ldRP b2 1 (Instr.immW (B.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩) = b3 at S3 hlB3 ⊢
  simp only [Form.writesH, Form.writesL] at S3
  -- the literals' bytes, in each machine's memory now
  obtain ⟨adA, hadA, hfA, hbA⟩ := db_mem hdA S3.LA hencA
  obtain ⟨adB, hadB, hfB, hbB⟩ := db_mem hdB S3.LB hencB
  simp only at hfA hfB hbA hbB
  rw [hTA'] at hadA; cases hadA
  rw [hTB'] at hadB; cases hadB
  have hrsA : a3.ramStart.toNat ≤ lo := S3.rs
  have hrsB : b3.ramStart.toNat ≤ lo := by
    have := RegsS.ramStart S3.E.regs; rw [mask_ramStart] at this; rw [← this]; exact hrsA
  have hxA : a3.hl.toNat = TA := by rw [hlA3, hlA2, hlA1, hlA0, hnA0]
  have hxB : b3.hl.toNat = TB := by rw [hlB3, hlB2, hlB1, hlB0, hnB0]
  -- `ldir`, four rounds
  have S7 := ldir_rom_rounds D hhi i7A i7B 3 _ _ S3 (by simp only; rw [bc3, bc2, hn4])
    (by simp only; rw [hxA]; omega) (by simp only; rw [hxB]; omega)
    (fun i hi' => by
      simp only; rw [hxA, hxB]
      obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨bs[i]'(by omega), by simp⟩
      rw [hbA i b hb, hbB i b hb])
    (by simp only; rw [de3, hacc3]; exact hacc.1) (by simp only; rw [de3, hacc3]; omega)
  -- `ret`
  have S8 := seg_ret D (cc := none) (fun _ h => by cases h) i8A i8B S7
  simp only [taken, if_true] at S8
  exact S8

/-- info: 'Ember.Proof.PassSim.blkR_ld32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkR_ld32

/-! ## The loop over the bytes, reading the ROM -/

/-- The `n` bytes of the ROM at `a` in the first image the same as those at `b` in the second, in any
CPU running each. -/
def RomEq (A B : Code) (a b n : Nat) : Prop :=
  ∀ s t, Loaded A s → Loaded B t → ∀ i, i < n → s.mem.get! (a + i) = t.mem.get! (b + i)

/-- **All the rounds of the loop of `rt_add32`, `rt_sub32`, `rt_or32` reading the ROM**, in both machines,
`H` and `L` free: the bytes at each machine's `HL` the same (`RomEq`), the RAM at `DE` kept equal. -/
theorem loop_rom_rounds (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame}
    {j m : Nat} {l : String} {i : Instr} (k : UInt8) (hexec : ∀ env s inp, exec env i s inp = some (aluMS k s))
    (hfi : i.falls = true) (hLA : Has A j (loopItems l i)) (hLB : Has B m (loopItems l i)) :
    ∀ (n : Nat) (x y : Cpu × D.W), Sync D A B lo hi G (j + 1) (m + 1) true true x y → x.1.b.toNat = n + 1 →
      RomEq A B x.1.hl.toNat y.1.hl.toNat (n + 1) → x.1.hl.toNat + n + 1 ≤ lo → y.1.hl.toNat + n + 1 ≤ lo →
      lo ≤ x.1.de.toNat → x.1.de.toNat + n + 1 ≤ hi →
      Sync D A B lo hi G (j + 7) (m + 7) true true (mrun D (6 * (n + 1)) x) (mrun D (6 * (n + 1)) y)
  | n, (s, w), (t, w'), S, hb, hr, h1, g1, d1, d2 => by
    have l0A : A.items[j]? = some (.label l) := hLA.get 0 rfl
    have l0B : B.items[m]? = some (.label l) := hLB.get 0 rfl
    have i1A : A.items[j + 1]? = some (.ins Form.ldADE.instr) := hLA.get 1 rfl
    have i1B : B.items[m + 1]? = some (.ins Form.ldADE.instr) := hLB.get 1 rfl
    have i2A : A.items[j + 2]? = some (.ins i) := hLA.get 2 rfl
    have i2B : B.items[m + 2]? = some (.ins i) := hLB.get 2 rfl
    have i3A : A.items[j + 3]? = some (.ins Form.stDEA.instr) := hLA.get 3 rfl
    have i3B : B.items[m + 3]? = some (.ins Form.stDEA.instr) := hLB.get 3 rfl
    have i4A : A.items[j + 4]? = some (.ins ⟨.inc, [.hl]⟩) := hLA.get 4 rfl
    have i4B : B.items[m + 4]? = some (.ins ⟨.inc, [.hl]⟩) := hLB.get 4 rfl
    have i5A : A.items[j + 5]? = some (.ins Form.incDE.instr) := hLA.get 5 rfl
    have i5B : B.items[m + 5]? = some (.ins Form.incDE.instr) := hLB.get 5 rfl
    have i6A : A.items[j + 6]? = some (.ins ⟨.djnz, [.imm (.sym l 0)]⟩) := hLA.get 6 rfl
    have i6B : B.items[m + 6]? = some (.ins ⟨.djnz, [.imm (.sym l 0)]⟩) := hLB.get 6 rfl
    have hw : w' = w := S.w
    subst hw
    simp only at hb hr h1 g1 d1 d2
    rw [show 6 * (n + 1) = 6 + 6 * n by omega, mrun_add, mrun_add, mrun_6, mrun_6]
    -- `ld a,(de)`
    have S1 := seg_ord D hhi Form.ldADE (by intro h; cases h) i1A i1B (fun _ _ => ⟨rfl, rfl⟩)
      (by simp [Form.readsH]) (by simp [Form.readsL]) S
      (by simp [Form.viaHL]) (fun _ => by simp only; exact ⟨d1, by omega⟩) (fun _ h => by simp [Form.viaNN] at h)
    rw [mstep_exec D i1A S.LA S.atA w' (fun _ _ => exec_ld_a_de _ _ _) rfl,
      mstep_exec D i1B S.LB S.atB w' (fun _ _ => exec_ld_a_de _ _ _) rfl] at S1 ⊢
    obtain ⟨a1, b1, c1⟩ := ldADES_regs s
    obtain ⟨a1', _, _⟩ := ldADES_regs t
    generalize ldADES s = s1 at S1 a1 b1 c1 ⊢
    generalize ldADES t = t1 at S1 a1' ⊢
    simp only [Form.writesH, Form.writesL] at S1
    -- the operation on `A` with the byte at `(HL)`: the ROM's, the same in both
    have S2 := seg_aluM D hhi k hexec hfi i2A i2B S1 (by
      simp only; rw [a1, a1']; have := hr s1 t1 S1.LA S1.LB 0 (by omega); simpa using this)
    rw [mstep_exec D i2A S1.LA S1.atA w' (fun _ _ => hexec _ _ _) (by rw [aluMS_eq]; rfl),
      mstep_exec D i2B S1.LB S1.atB w' (fun _ _ => hexec _ _ _) (by rw [aluMS_eq]; rfl)] at S2 ⊢
    obtain ⟨a2, b2, c2⟩ := aluMS_regs k s1
    obtain ⟨a2', _, _⟩ := aluMS_regs k t1
    generalize aluMS k s1 = s2 at S2 a2 b2 c2 ⊢
    generalize aluMS k t1 = t2 at S2 a2' ⊢
    -- `ld (de),a`
    have S3 := seg_ord D hhi Form.stDEA (by intro h; cases h) i3A i3B (fun _ _ => ⟨rfl, rfl⟩)
      (by simp [Form.readsH]) (by simp [Form.readsL]) S2
      (by simp [Form.viaHL]) (fun _ => ⟨by rw [b2, b1]; exact d1, by rw [b2, b1]; omega⟩)
      (fun _ h => by simp [Form.viaNN] at h)
    rw [mstep_exec D i3A S2.LA S2.atA w' (fun _ _ => exec_ld_de_a _ _ _) (by simp only [stDEAS, Cpu.wr, Cpu.tick]; split <;> rfl),
      mstep_exec D i3B S2.LB S2.atB w' (fun _ _ => exec_ld_de_a _ _ _) (by simp only [stDEAS, Cpu.wr, Cpu.tick]; split <;> rfl)] at S3 ⊢
    obtain ⟨a3, b3, c3⟩ := stDEAS_regs s2
    obtain ⟨a3', _, _⟩ := stDEAS_regs t2
    generalize stDEAS s2 = s3 at S3 a3 b3 c3 ⊢
    generalize stDEAS t2 = t3 at S3 a3' ⊢
    simp only [Form.writesH, Form.writesL] at S3
    -- `inc hl`
    have S4 := seg_inchl_free D hhi i4A i4B S3
    rw [mstep_exec D i4A S3.LA S3.atA w' (fun _ _ => exec_inc_hl _ _ _) (by rw [incHLS_eq]; rfl),
      mstep_exec D i4B S3.LB S3.atB w' (fun _ _ => exec_inc_hl _ _ _) (by rw [incHLS_eq]; rfl)] at S4 ⊢
    obtain ⟨a4, b4, c4⟩ := incHLS_regs s3
    obtain ⟨a4', _, _⟩ := incHLS_regs t3
    generalize incHLS s3 = s4 at S4 a4 b4 c4 ⊢
    generalize incHLS t3 = t4 at S4 a4' ⊢
    -- `inc de`
    have S5 := seg_ord D hhi Form.incDE (by intro h; cases h) i5A i5B (fun _ _ => ⟨rfl, rfl⟩)
      (by simp [Form.readsH]) (by simp [Form.readsL]) S4
      (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
    rw [mstep_exec D i5A S4.LA S4.atA w' (fun _ _ => exec_inc_de _ _ _) rfl,
      mstep_exec D i5B S4.LB S4.atB w' (fun _ _ => exec_inc_de _ _ _) rfl] at S5 ⊢
    obtain ⟨a5, b5, c5⟩ := incDES_regs s4
    obtain ⟨a5', _, _⟩ := incDES_regs t4
    generalize incDES s4 = s5 at S5 a5 b5 c5 ⊢
    generalize incDES t4 = t5 at S5 a5' ⊢
    simp only [Form.writesH, Form.writesL] at S5
    -- `djnz`
    have S6 := seg_djnz D i6A l0A i6B l0B S5
    obtain ⟨p6, q6, e6, _, _⟩ := djnz_mstep D i6A l0A S5.LA S5.atA w'
    obtain ⟨p6', q6', e6', _, _⟩ := djnz_mstep D i6B l0B S5.LB S5.atB w'
    have hb5 : s5.b.toNat = n + 1 := by rw [c5, c4, c3, c2, c1]; exact hb
    obtain ⟨d6h, d6d, d6b⟩ := djnzed_regs s5 p6 q6
    obtain ⟨d6h', _, _⟩ := djnzed_regs t5 p6' q6'
    cases n with
    | zero =>
      have h0 : s5.b - 1 = 0 := by apply UInt8.toNat_inj.mp; rw [toNat_sub1_8 _ (by omega)]; simp [hb5]
      have hne : ¬ ((s5.b - 1 != 0) = true) := by rw [h0]; decide
      rw [if_neg hne] at S6
      simpa only [Nat.mul_zero, mrun, Bool.not_false, Bool.and_self] using S6
    | succ n' =>
      have hne : (s5.b - 1 != 0) = true := by
        have h' : (s5.b - 1).toNat = n' + 1 := by rw [toNat_sub1_8 _ (by omega)]; omega
        have : s5.b - 1 ≠ 0 := by intro e; rw [e] at h'; simp at h'
        simp [this]
      rw [if_pos hne] at S6
      have S6' := S6.skip l0A l0B
      rw [e6, e6'] at S6' ⊢
      simp only [Bool.not_false, Bool.and_self] at S6'
      have hA6 : (djnzed s5 p6 q6).hl.toNat = s.hl.toNat + 1 := by
        rw [d6h, a5, a4, toNat_add1 _ (by rw [a3, a2, a1]; omega), a3, a2, a1]
      have hB6 : (djnzed t5 p6' q6').hl.toNat = t.hl.toNat + 1 := by
        rw [d6h', a5', a4', toNat_add1 _ (by rw [a3', a2', a1']; omega), a3', a2', a1']
      exact loop_rom_rounds D hhi k hexec hfi hLA hLB n' _ _ S6'
        (by simp only; rw [d6b, toNat_sub1_8 _ (by omega)]; omega)
        (fun u v Lu Lv i' hi' => by
          simp only; rw [hA6, hB6]
          have := hr u v Lu Lv (i' + 1) (by omega)
          rw [show s.hl.toNat + 1 + i' = s.hl.toNat + (i' + 1) by omega,
            show t.hl.toNat + 1 + i' = t.hl.toNat + (i' + 1) by omega]
          exact this)
        (by simp only; rw [hA6]; omega) (by simp only; rw [hB6]; omega)
        (by simp only; rw [d6d, b5, toNat_add1 _ (by rw [b4, b3, b2, b1]; omega), b4, b3, b2, b1]; omega)
        (by simp only; rw [d6d, b5, toNat_add1 _ (by rw [b4, b3, b2, b1]; omega), b4, b3, b2, b1]; omega)

/-- info: 'Ember.Proof.PassSim.loop_rom_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loop_rom_rounds

/-- **`ld hl,lit` in both machines**: each machine's `HL` on its own image's literal (`.db`, the same
bytes), `H` and `L` free after; the bytes there the same in any CPU running each image, below the RAM. -/
theorem ldhl_lit (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame}
    {kA kB dA dB : Nat} {lit : String} {vs : List Val} {bs : List UInt8} {th tl : Bool}
    (hA0 : A.items[kA]? = some (.ins ⟨.ld, [.hl, .imm (.sym lit 0)]⟩))
    (hB0 : B.items[kB]? = some (.ins ⟨.ld, [.hl, .imm (.sym lit 0)]⟩))
    (hlA : A.items[dA]? = some (.label lit)) (hdA : A.items[dA + 1]? = some (.db vs))
    (hlB : B.items[dB]? = some (.label lit)) (hdB : B.items[dB + 1]? = some (.db vs))
    (hencA : ∀ ad, Item.encode (.db vs) (A.a.env ad) = .ok bs)
    (hencB : ∀ ad, Item.encode (.db vs) (B.a.env ad) = .ok bs)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB th tl x y) :
    Sync D A B lo hi G (kA + 1) (kB + 1) true true (mstep D x) (mstep D y) ∧
      (mstep D x).1.sp = x.1.sp ∧ (mstep D x).1.hl.toNat + bs.length ≤ lo ∧
      (mstep D y).1.hl.toNat + bs.length ≤ lo ∧
      RomEq A B (mstep D x).1.hl.toNat (mstep D y).1.hl.toNat bs.length := by
  obtain ⟨TA, hTA, hvalA, hTAlt⟩ := label_addr S.LA hlA
  obtain ⟨TB, hTB, hvalB, hTBlt⟩ := label_addr S.LB hlB
  have hTA' := label_next hlA hTA
  have hTB' := label_next hlB hTB
  -- the bytes of the literals, in any CPU running each image
  have romA : ∀ s, Loaded A s → TA + bs.length ≤ s.ramStart.toNat ∧ ∀ j b, bs[j]? = some b → s.mem.get! (TA + j) = b := by
    intro s L
    obtain ⟨ad, had, hf, hb⟩ := db_mem hdA L hencA
    rw [hTA'] at had; cases had
    exact ⟨hf, hb⟩
  have romB : ∀ t, Loaded B t → TB + bs.length ≤ t.ramStart.toNat ∧ ∀ j b, bs[j]? = some b → t.mem.get! (TB + j) = b := by
    intro t L
    obtain ⟨ad, had, hf, hb⟩ := db_mem hdB L hencB
    rw [hTB'] at had; cases had
    exact ⟨hf, hb⟩
  have hR : RomEq A B TA TB bs.length := fun s t Ls Lt i hi' => by
    obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨bs[i], by simp [hi']⟩
    rw [(romA s Ls).2 i b hb, (romB t Lt).2 i b hb]
  have hrsA : x.1.ramStart.toNat ≤ lo := S.rs
  have hrsB : y.1.ramStart.toNat ≤ lo := by
    have := RegsS.ramStart S.E.regs; rw [mask_ramStart] at this; rw [← this]; exact hrsA
  have fA := (romA x.1 S.LA).1
  have fB := (romB y.1 S.LB).1
  obtain ⟨sA, w⟩ := x
  obtain ⟨sB, w'⟩ := y
  have hw : w' = w := S.w
  subst hw
  simp only at hrsA hrsB fA fB
  have S0 := seg_ldhl D hhi hA0 hB0 S
  have hnA : ∀ pa, (Instr.immW (A.a.env pa) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩).toNat = TA :=
    fun pa => immW_toNat _ _ _ TA rfl (hvalA pa) hTAlt
  have hnB : ∀ pb, (Instr.immW (B.a.env pb) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩).toNat = TB :=
    fun pb => immW_toNat _ _ _ TB rfl (hvalB pb) hTBlt
  have eA0 : mstep D (sA, w') = (ldHL sA (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩), w') :=
    mstep_exec D hA0 S.LA S.atA w' (fun pa inp => by
      rw [exec_ld_hl_sym]
      rw [show Instr.immW (A.a.env pa) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ =
        Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ from UInt16.toNat_inj.mp (by rw [hnA, hnA])])
      (by rw [ldHL_eq]; rfl)
  have eB0 : mstep D (sB, w') = (ldHL sB (Instr.immW (B.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩), w') :=
    mstep_exec D hB0 S.LB S.atB w' (fun pb inp => by
      rw [exec_ld_hl_sym]
      rw [show Instr.immW (B.a.env pb) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ =
        Instr.immW (B.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ from UInt16.toNat_inj.mp (by rw [hnB, hnB])])
      (by rw [ldHL_eq]; rfl)
  rw [eA0, eB0] at S0 ⊢
  have hlA0 := ldHL_hl sA (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩)
  have hlB0 := ldHL_hl sB (Instr.immW (B.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩)
  have spA0 : (ldHL sA (Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩)).sp = sA.sp := by rw [ldHL_eq]; rfl
  have hnA0 := hnA 0
  have hnB0 := hnB 0
  generalize Instr.immW (A.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ = nA at S0 hlA0 spA0 hnA0 ⊢
  generalize Instr.immW (B.a.env 0) ⟨.ld, [.hl, .imm (.sym lit 0)]⟩ = nB at S0 hlB0 hnB0 ⊢
  generalize ldHL sA nA = a0 at S0 hlA0 spA0 ⊢
  generalize ldHL sB nB = b0 at S0 hlB0 ⊢
  simp only
  rw [hlA0, hlB0, hnA0, hnB0]
  exact ⟨S0, spA0, by omega, by omega, hR⟩

/-- info: 'Ember.Proof.PassSim.ldhl_lit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ldhl_lit

set_option maxHeartbeats 2000000 in
/-- The beginning of `rt_add32`, `rt_sub32`, `rt_or32` with `H` and `L` free: the call, `ld b,4`,
`ld de,rt_acc`; the relation at the item after (`r + 7`), `B` four, `DE` the accumulator, each
machine's `HL` as at the call. -/
theorem bytesR_head (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) (hlo : lo ≤ hi) (h1 : 1 ≤ hi)
    {G : List Frame} {kA kB r q acc : Nat} {n64 n32 nw : String} {rest : List Item}
    (hA : A.items[kA]? = some (.ins ⟨.call, [.imm (.sym n32 0)]⟩))
    (hB : B.items[kB]? = some (.ins ⟨.call, [.imm (.sym n32 0)]⟩))
    (hLA : Has A r ([.label n64, .ins ⟨.ld, [.b, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym nw)]⟩,
      .label n32, .ins ⟨.ld, [.b, .imm (.num 4)]⟩, .label nw, .ins ⟨.ld, [.de, .imm (.sym "rt_acc")]⟩] ++ rest))
    (hLB : Has B q ([.label n64, .ins ⟨.ld, [.b, .imm (.num 8)]⟩, .ins ⟨.jr, [.imm (.sym nw)]⟩,
      .label n32, .ins ⟨.ld, [.b, .imm (.num 4)]⟩, .label nw, .ins ⟨.ld, [.de, .imm (.sym "rt_acc")]⟩] ++ rest))
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : acc + 4 ≤ hi)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB true true x y) (room : hi + 2 ≤ top x.1.sp) :
    Sync D A B lo hi (.ret (kA + 1) (kB + 1) (r + 3) :: G) (r + 7) (q + 7) true true (mrun D 3 x) (mrun D 3 y) ∧
      (mrun D 3 x).1.b.toNat = 4 ∧ (mrun D 3 x).1.hl = x.1.hl ∧ (mrun D 3 y).1.hl = y.1.hl ∧
      (mrun D 3 x).1.de.toNat = acc := by
  have l3A : A.items[r + 3]? = some (.label n32) := hLA.get 3 rfl
  have l3B : B.items[q + 3]? = some (.label n32) := hLB.get 3 rfl
  have i4A : A.items[r + 4]? = some (.ins (Form.ldBI (.num 4)).instr) := hLA.get 4 rfl
  have i4B : B.items[q + 4]? = some (.ins (Form.ldBI (.num 4)).instr) := hLB.get 4 rfl
  have l5A : A.items[r + 5]? = some (.label nw) := hLA.get 5 rfl
  have l5B : B.items[q + 5]? = some (.label nw) := hLB.get 5 rfl
  have i6A : A.items[r + 6]? = some (.ins (Form.ldDEI (.sym "rt_acc" 0)).instr) := hLA.get 6 rfl
  have i6B : B.items[q + 6]? = some (.ins (Form.ldDEI (.sym "rt_acc" 0)).instr) := hLB.get 6 rfl
  have hvacc : ∀ pa pb, (A.a.env pa).val (.sym "rt_acc" 0) = (B.a.env pb).val (.sym "rt_acc" 0) := by
    intro pa pb; rw [haccA, haccB]
  obtain ⟨sA, w⟩ := x
  obtain ⟨sB, w'⟩ := y
  have hw : w' = w := S.w
  subst hw
  simp only at room
  show Sync D A B lo hi _ (r + 7) (q + 7) true true (mstep D (mstep D (mstep D (sA, w')))) (mstep D (mstep D (mstep D (sB, w')))) ∧
    (mstep D (mstep D (mstep D (sA, w')))).1.b.toNat = 4 ∧ (mstep D (mstep D (mstep D (sA, w')))).1.hl = sA.hl ∧
    (mstep D (mstep D (mstep D (sB, w')))).1.hl = sB.hl ∧ (mstep D (mstep D (mstep D (sA, w')))).1.de.toNat = acc
  obtain ⟨T, _, _, _, _, _, eA1, _⟩ := call_mstep D hA l3A S.LA S.atA w'
  obtain ⟨T', _, _, _, _, _, eB1, _⟩ := call_mstep D hB l3B S.LB S.atB w'
  have S1 := (seg_call D hhi hA l3A hB l3B S hlo h1 room).skip l3A l3B
  rw [eA1, eB1] at S1 ⊢
  obtain ⟨hl1, _, _⟩ := called_regs sA (UInt16.ofNat T)
  obtain ⟨hl1', _, _⟩ := called_regs sB (UInt16.ofNat T')
  generalize called sA (UInt16.ofNat T) = s1 at S1 hl1 ⊢
  generalize called sB (UInt16.ofNat T') = t1 at S1 hl1' ⊢
  have S2 := (seg_ord D hhi (Form.ldBI (.num 4)) (by intro h; cases h) i4A i4B
    (imm_same _ _ rfl ⟨by decide, by decide⟩ (val_num 4)) (by simp [Form.readsH]) (by simp [Form.readsL]) S1
    (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)).skip l5A l5B
  rw [mstep_exec D i4A S1.LA S1.atA w' (s' := ldRN s1 0 (Instr.immB (A.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩))
      (fun pa inp => by
        show exec (A.a.env pa) ⟨.ld, [.b, .imm (.num 4)]⟩ s1 inp = _
        rw [exec_ld_b_n]; rfl) rfl,
    mstep_exec D i4B S1.LB S1.atB w' (s' := ldRN t1 0 (Instr.immB (B.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩))
      (fun pb inp => by
        show exec (B.a.env pb) ⟨.ld, [.b, .imm (.num 4)]⟩ t1 inp = _
        rw [exec_ld_b_n]; rfl) rfl] at S2 ⊢
  have hb2 : (ldRN s1 0 (Instr.immB (A.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩)).b.toNat = 4 := rfl
  obtain ⟨_, hl2, _⟩ := ldRN_b s1 (Instr.immB (A.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩)
  obtain ⟨_, hl2', _⟩ := ldRN_b t1 (Instr.immB (B.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩)
  generalize ldRN s1 0 (Instr.immB (A.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩) = s2 at S2 hb2 hl2 ⊢
  generalize ldRN t1 0 (Instr.immB (B.a.env 0) ⟨.ld, [.b, .imm (.num 4)]⟩) = t2 at S2 hl2' ⊢
  simp only [Form.writesH, Form.writesL] at S2
  have S3 := seg_ord D hhi (Form.ldDEI (.sym "rt_acc" 0)) (by intro h; cases h) i6A i6B
    (imm_same _ _ rfl ⟨by decide, by decide⟩ hvacc) (by simp [Form.readsH]) (by simp [Form.readsL]) S2
    (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
  have e3 : mstep D (s2, w') = (ldRP s2 1 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩), w') :=
    mstep_exec D i6A S2.LA S2.atA w' (fun pa inp => by
      show exec (A.a.env pa) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩ s2 inp = _
      rw [exec_ld_rp _ .de 1 rfl (by decide)]
      congr 2
      apply UInt16.toNat_inj.mp
      rw [immW_toNat _ _ _ acc rfl (haccA pa) (by omega), immW_toNat _ _ _ acc rfl (haccA 0) (by omega)]) rfl
  have e3' : mstep D (t2, w') = (ldRP t2 1 (Instr.immW (B.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩), w') :=
    mstep_exec D i6B S2.LB S2.atB w' (fun pb inp => by
      show exec (B.a.env pb) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩ t2 inp = _
      rw [exec_ld_rp _ .de 1 rfl (by decide)]
      congr 2
      apply UInt16.toNat_inj.mp
      rw [immW_toNat _ _ _ acc rfl (haccB pb) (by omega), immW_toNat _ _ _ acc rfl (haccB 0) (by omega)]) rfl
  have hacc3 : (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩).toNat = acc :=
    immW_toNat _ _ _ acc rfl (haccA 0) (by omega)
  rw [e3, e3'] at S3 ⊢
  obtain ⟨de3, hl3, _⟩ := ldRP_de s2 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩)
  obtain ⟨_, hl3', _⟩ := ldRP_de t2 (Instr.immW (B.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩)
  have hb3 := ldRP_b1 s2 (Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩)
  simp only [Form.writesH, Form.writesL] at S3
  generalize Instr.immW (A.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩ = nacc at S3 de3 hl3 hb3 hacc3 ⊢
  generalize Instr.immW (B.a.env 0) ⟨.ld, [.de, .imm (.sym "rt_acc" 0)]⟩ = nacc' at S3 hl3' ⊢
  refine ⟨S3, by simp only; rw [hb3]; exact hb2, by simp only; rw [hl3, hl2, hl1],
    by simp only; rw [hl3', hl2', hl1'], by simp only; rw [de3, hacc3]⟩

/-- info: 'Ember.Proof.PassSim.bytesR_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bytesR_head

/-- The loop of four rounds reading the ROM and the `ret` after it, in both machines (the frame of the
call on top). -/
theorem loopR_ret (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) {G : List Frame}
    {L M rA rB e : Nat} {l : String} {i : Instr} (k : UInt8)
    (hexec : ∀ env s inp, exec env i s inp = some (aluMS k s)) (hfi : i.falls = true)
    (hLA : Has A L (loopItems l i ++ [.ins ⟨.ret, []⟩])) (hLB : Has B M (loopItems l i ++ [.ins ⟨.ret, []⟩]))
    {x y : Cpu × D.W} (S : Sync D A B lo hi (.ret rA rB e :: G) (L + 1) (M + 1) true true x y)
    (hb : x.1.b.toNat = 4) (hr : RomEq A B x.1.hl.toNat y.1.hl.toNat 4)
    (g1 : x.1.hl.toNat + 4 ≤ lo) (g2 : y.1.hl.toNat + 4 ≤ lo)
    (d1 : lo ≤ x.1.de.toNat ∧ x.1.de.toNat + 4 ≤ hi) :
    Sync D A B lo hi G rA rB true true (mrun D 25 x) (mrun D 25 y) := by
  have S7 := loop_rom_rounds D hhi k hexec hfi hLA.left hLB.left 3 x y S hb hr (by omega) (by omega) d1.1 (by omega)
  have iA : A.items[L + 7]? = some (.ins ⟨.ret, (none : Option Arg).toList⟩) := by
    have := hLA.right; exact this.get 0 rfl
  have iB : B.items[M + 7]? = some (.ins ⟨.ret, (none : Option Arg).toList⟩) := by
    have := hLB.right; exact this.get 0 rfl
  have S8 := seg_ret D (cc := none) (fun _ h => by cases h) iA iB S7
  simp only [taken, if_true] at S8
  rw [mrun_25, mrun_25]; exact S8

/-- **`ld hl,lit` then `call rt_add32`, `rt_sub32`, `rt_or32` in both machines**: the four bytes of each
image's literal (`.db`, the same bytes in both) with the accumulator in the RAM; the relation at the
items after the calls, `H` and `L` free. -/
theorem blkR_bytes (D : Dev) {A B : Code} {lo hi : Nat} (hhi : hi ≤ 65536) (hlo : lo ≤ hi) (h1 : 1 ≤ hi)
    {G : List Frame} {kA kB r q acc dA dB : Nat} {name lit : String} {vs : List Val} {bs : List UInt8}
    {th tl : Bool} {pre : List Item} {i : Instr} (k : UInt8)
    (hpre : pre = [] ∨ pre = [.ins Form.orA.instr])
    (hexec : ∀ env s inp, exec env i s inp = some (aluMS k s)) (hfi : i.falls = true)
    (hA0 : A.items[kA]? = some (.ins ⟨.ld, [.hl, .imm (.sym lit 0)]⟩))
    (hB0 : B.items[kB]? = some (.ins ⟨.ld, [.hl, .imm (.sym lit 0)]⟩))
    (hA : A.items[kA + 1]? = some (.ins ⟨.call, [.imm (.sym s!"rt_{name}32" 0)]⟩))
    (hB : B.items[kB + 1]? = some (.ins ⟨.call, [.imm (.sym s!"rt_{name}32" 0)]⟩))
    (hLA : Has A r (bytewiseItems name pre i)) (hLB : Has B q (bytewiseItems name pre i))
    (haccA : ∀ pa, (A.a.env pa).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (haccB : ∀ pb, (B.a.env pb).val (.sym "rt_acc" 0) = Int.ofNat acc)
    (hacc : lo ≤ acc ∧ acc + 4 ≤ hi)
    (hlA : A.items[dA]? = some (.label lit)) (hdA : A.items[dA + 1]? = some (.db vs))
    (hlB : B.items[dB]? = some (.label lit)) (hdB : B.items[dB + 1]? = some (.db vs))
    (hencA : ∀ ad, Item.encode (.db vs) (A.a.env ad) = .ok bs)
    (hencB : ∀ ad, Item.encode (.db vs) (B.a.env ad) = .ok bs) (hbs : bs.length = 4)
    {x y : Cpu × D.W} (S : Sync D A B lo hi G kA kB th tl x y) (room : hi + 2 ≤ top x.1.sp) :
    Sync D A B lo hi G (kA + 2) (kB + 2) true true (mrun D (29 + pre.length) x) (mrun D (29 + pre.length) y) := by
  obtain ⟨S0, sp0, g0A, g0B, hR⟩ := ldhl_lit D hhi hA0 hB0 hlA hdA hlB hdB hencA hencB S
  rw [hbs] at g0A g0B hR
  rw [show 29 + pre.length = 1 + (28 + pre.length) by omega, mrun_add D 1 _ x, mrun_add D 1 _ y]
  show Sync D A B lo hi G (kA + 1 + 1) (kB + 1 + 1) true true (mrun D (28 + pre.length) (mstep D x))
    (mrun D (28 + pre.length) (mstep D y))
  generalize mstep D x = x' at S0 sp0 g0A g0B hR
  generalize mstep D y = y' at S0 g0B hR
  rw [bytewise_split] at hLA hLB
  obtain ⟨S3, hb3, hl3, hl3', de3⟩ := bytesR_head D hhi hlo h1 hA hB hLA hLB haccA haccB hacc.2 S0
    (by rw [sp0]; exact room)
  have tA := hLA.right
  have tB := hLB.right
  simp only [List.length_cons, List.length_nil] at tA tB
  rcases hpre with rfl | rfl
  · have lA : A.items[r + 7]? = some (.label s!"rt_{name}w_l") := tA.get 0 rfl
    have lB : B.items[q + 7]? = some (.label s!"rt_{name}w_l") := tB.get 0 rfl
    have R := loopR_ret D hhi k hexec hfi (L := r + 7) (M := q + 7) (by simpa using tA) (by simpa using tB)
      (S3.skip lA lB) hb3 (by rw [hl3, hl3']; exact hR) (by rw [hl3]; exact g0A) (by rw [hl3']; exact g0B)
      (by rw [de3]; exact ⟨hacc.1, hacc.2⟩)
    rw [show 28 + ([] : List Item).length = 3 + 25 from rfl, mrun_add, mrun_add]
    exact R
  · have iA : A.items[r + 7]? = some (.ins Form.orA.instr) := tA.get 0 rfl
    have iB : B.items[q + 7]? = some (.ins Form.orA.instr) := tB.get 0 rfl
    have S4 := seg_ord D hhi Form.orA (by intro h; cases h) iA iB (fun _ _ => ⟨rfl, rfl⟩)
      (by simp [Form.readsH]) (by simp [Form.readsL]) S3
      (by simp [Form.viaHL]) (by simp [Form.viaDE]) (fun _ h => by simp [Form.viaNN] at h)
    simp only [Form.writesH, Form.writesL] at S4
    have lA : A.items[r + 7 + 1]? = some (.label s!"rt_{name}w_l") := tA.get 1 rfl
    have lB : B.items[q + 7 + 1]? = some (.label s!"rt_{name}w_l") := tB.get 1 rfl
    have e4 : mstep D (mrun D 3 x') = (orAS (mrun D 3 x').1, (mrun D 3 x').2) :=
      mstep_exec D iA S3.LA S3.atA _ (fun _ _ => rfl) rfl
    have e4' : mstep D (mrun D 3 y') = (orAS (mrun D 3 y').1, (mrun D 3 y').2) :=
      mstep_exec D iB S3.LB S3.atB _ (fun _ _ => rfl) rfl
    obtain ⟨hl4, de4, b4⟩ := orAS_regs (mrun D 3 x').1
    obtain ⟨hl4', _, _⟩ := orAS_regs (mrun D 3 y').1
    have tA' : Has A (r + 7 + 1) (loopItems s!"rt_{name}w_l" i ++ [.ins ⟨.ret, []⟩]) := by
      have := tA.right; simpa using this
    have tB' : Has B (q + 7 + 1) (loopItems s!"rt_{name}w_l" i ++ [.ins ⟨.ret, []⟩]) := by
      have := tB.right; simpa using this
    have R := loopR_ret D hhi k hexec hfi tA' tB' (S4.skip lA lB)
      (by rw [e4]; simp only; rw [b4]; exact hb3)
      (by rw [e4, e4']; simp only; rw [hl4, hl3, hl4', hl3']; exact hR)
      (by rw [e4]; simp only; rw [hl4, hl3]; exact g0A)
      (by rw [e4']; simp only; rw [hl4', hl3']; exact g0B)
      (by rw [e4]; simp only; rw [de4, de3]; exact ⟨hacc.1, hacc.2⟩)
    rw [show 28 + [Item.ins Form.orA.instr].length = 3 + (1 + 25) from rfl, mrun_add, mrun_add, mrun_add, mrun_add]
    exact R

/-- info: 'Ember.Proof.PassSim.blkR_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkR_bytes
