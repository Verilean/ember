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
