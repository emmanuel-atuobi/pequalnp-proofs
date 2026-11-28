import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8839_4
    (hAndInput :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        let V : Type := Fin x2 → Bool;
        (199 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
        ∀ (x9 : ℕ) (x10 : Finset ℕ) (x11 : ℕ → Set (V × V)) (w1 w2 : ℕ),
          have x12 : ℕ := x2 + x2;
          have x13 : ℕ := x12 + x9 - (1 : ℕ);
          have x14 : Fin x2 → V := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);
          have x15 : ℕ → Prop := fun (x15 : ℕ) => ∀ (x16 x17 : Fin x2), x3 x16 x17 → (x14 x16, x14 x17) ∈ x11 x15;
          have x16 : ℕ → Prop := fun (x16 : ℕ) => ∀ (x17 : V), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x11 x16;
          x12 ≤ x9 + (1 : ℕ) →
          x9 < x2 * (x1 / (100 : ℕ) + (1 : ℕ)) →
          (∀ (x19 : Fin x2), x11 ↑x19 = {x20 : V × V | x20.1 x19 = Bool.true} ∧ x11 (x2 + ↑x19) = {x20 : V × V | x20.2 x19 = Bool.true}) →
          (∀ x20 < x9, ∃ (x22 : ℕ) (x23 : ℕ), Max.max x22 x23 < x12 + x20 ∧ (x11 (x12 + x20) ∈ [x11 x22 ∪ x11 x23, x11 x22, ∅] ∨ x11 (x12 + x20) = x11 x22 ∩ x11 x23 ∧ (x20 ∈ x10 ∨ ∃ (x24 : Set V) (x25 : Set V), x11 x22 = x24 ×ˢ Set.univ ∧ x11 x23 = Set.univ ×ˢ x25))) →
          x16 x13 →
          (∀ x22 < x13, ¬(x15 x22 ∧ x16 x22)) →
          x12 ≤ w1 ∧ w1 < x13 ∧ x12 ≤ w2 ∧ w2 < x13 →
          x11 x13 = x11 w1 ∩ x11 w2 →
          x15 w1 ∧ x15 w2 ∧ ¬x16 w1 ∧ ¬x16 w2 →
          (∃ (u v : ℕ), Max.max u v < w1 ∧ x11 w1 = x11 u ∩ x11 v) →
          x9 - (1 : ℕ) ∈ x10 →
          (100 : ℕ) * x10.card < x2 * x1 →
          x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9)
    (hBothOr :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        let V : Type := Fin x2 → Bool;
        (199 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
        ∀ (x9 : ℕ) (x10 : Finset ℕ) (x11 : ℕ → Set (V × V)) (w1 w2 : ℕ),
          have x12 : ℕ := x2 + x2;
          have x13 : ℕ := x12 + x9 - (1 : ℕ);
          have x14 : Fin x2 → V := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);
          have x15 : ℕ → Prop := fun (x15 : ℕ) => ∀ (x16 x17 : Fin x2), x3 x16 x17 → (x14 x16, x14 x17) ∈ x11 x15;
          have x16 : ℕ → Prop := fun (x16 : ℕ) => ∀ (x17 : V), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x11 x16;
          x12 ≤ x9 + (1 : ℕ) →
          x9 < x2 * (x1 / (100 : ℕ) + (1 : ℕ)) →
          (∀ (x19 : Fin x2), x11 ↑x19 = {x20 : V × V | x20.1 x19 = Bool.true} ∧ x11 (x2 + ↑x19) = {x20 : V × V | x20.2 x19 = Bool.true}) →
          (∀ x20 < x9, ∃ (x22 : ℕ) (x23 : ℕ), Max.max x22 x23 < x12 + x20 ∧ (x11 (x12 + x20) ∈ [x11 x22 ∪ x11 x23, x11 x22, ∅] ∨ x11 (x12 + x20) = x11 x22 ∩ x11 x23 ∧ (x20 ∈ x10 ∨ ∃ (x24 : Set V) (x25 : Set V), x11 x22 = x24 ×ˢ Set.univ ∧ x11 x23 = Set.univ ×ˢ x25))) →
          x16 x13 →
          (∀ x22 < x13, ¬(x15 x22 ∧ x16 x22)) →
          x12 ≤ w1 ∧ w1 < x13 ∧ x12 ≤ w2 ∧ w2 < x13 →
          x11 x13 = x11 w1 ∩ x11 w2 →
          x15 w1 ∧ x15 w2 ∧ ¬x16 w1 ∧ ¬x16 w2 →
          (∃ (u v : ℕ), Max.max u v < w1 ∧ x11 w1 = x11 u ∪ x11 v) →
          (∃ (u v : ℕ), Max.max u v < w2 ∧ x11 w2 = x11 u ∪ x11 v) →
          x9 - (1 : ℕ) ∈ x10 →
          (100 : ℕ) * x10.card < x2 * x1 →
          x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (199 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 : ℕ) (x10 : Finset ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : ℕ := x12 + x9 - (1 : ℕ);             have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);             have x15 : ℕ → Prop := fun (x15 : ℕ) => ∀ (x16 x17 : Fin x2), x3 x16 x17 → (x14 x16, x14 x17) ∈ x11 x15;             have x16 : ℕ → Prop := fun (x16 : ℕ) => ∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x11 x16;             x12 ≤ x9 + (1 : ℕ) → x9 < x2 * (x1 / (100 : ℕ) + (1 : ℕ)) → (∀ (x19 : Fin x2), x11 ↑x19 = {x20 : (Fin x2 → Bool) × (Fin x2 → Bool) | x20.1 x19 = Bool.true} ∧ x11 (x2 + ↑x19) = {x20 : (Fin x2 → Bool) × (Fin x2 → Bool) | x20.2 x19 = Bool.true}) → (∀ x20 < x9, ∃ (x22 : ℕ) (x23 : ℕ), Max.max x22 x23 < x12 + x20 ∧ (x11 (x12 + x20) ∈ [x11 x22 ∪ x11 x23, x11 x22, ∅] ∨ x11 (x12 + x20) = x11 x22 ∩ x11 x23 ∧ (x20 ∈ x10 ∨ ∃ (x24 : Set (Fin x2 → Bool)) (x25 : Set (Fin x2 → Bool)), x11 x22 = x24 ×ˢ Set.univ ∧ x11 x23 = Set.univ ×ˢ x25))) → x15 x13 ∧ x16 x13 → (∀ x22 < x13, ¬(x15 x22 ∧ x16 x22)) → (∃ (x23 : ℕ) (x24 : ℕ), Max.max x23 x24 < x13 ∧ x11 x13 = x11 x23 ∩ x11 x24 ∧ ¬x16 x23 ∧ ¬x16 x24) → x9 - (1 : ℕ) ∈ x10 → (100 : ℕ) * x10.card < x2 * x1 → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9 := by
  classical
  intro q N inc _ hq hN hCard hProj s B W base out ind pos neg hsGe hsLt hInit hSteps hOut hMin hTop hLastIn hBcard
  have hN2 : 2 ≤ N := by
    have hq2 : 1 ≤ q ^ 2 := by
      have : 1 * 1 ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
      simpa only [sq] using this
    rw [hN]
    omega
  have hNotRaw : ∀ w, pos w → base ≤ w := by
    intro w hpw
    by_contra hlt
    have hlt : w < N + N := Nat.lt_of_not_ge hlt
    by_cases h1 : w < N
    · let p0 : Fin N := ⟨w, h1⟩
      let l0 : Fin N := ⟨0, by omega⟩
      have hsub : (Finset.univ.filter fun p : Fin N => inc p l0) ⊆ {p0} := by
        intro p hp
        have hmem := hpw p l0 (Finset.mem_filter.mp hp).2
        have hW := (hInit p0).1
        change W w = {z : (Fin N → Bool) × (Fin N → Bool) | z.1 p0 = Bool.true} at hW
        rw [hW] at hmem
        simp only [Set.mem_ofPred_eq, ind, decide_eq_true_eq] at hmem
        exact Finset.mem_singleton.mpr hmem.symm
      have hc1 : (Finset.univ.filter fun p : Fin N => inc p l0).card ≤ 1 :=
        le_trans (Finset.card_le_card hsub) (by simp only [Finset.card_singleton]; rfl)
      have hc2 : (Finset.univ.filter fun p : Fin N => inc p l0).card = Fintype.card { p : Fin N // inc p l0 } := by
        rw [Fintype.card_subtype]
      have hc3 := hCard l0
      omega
    · let l0 : Fin N := ⟨w - N, by omega⟩
      let l1 : Fin N := if l0.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hne : l1 ≠ l0 := by
        intro heq
        have hv := congrArg Fin.val heq
        by_cases h0 : l0.val = 0
        · simp only [l1, h0, ↓reduceIte] at hv
          omega
        · simp only [l1, h0, ↓reduceIte] at hv
          exact h0 hv.symm
      have hpos1 : 0 < Fintype.card { p : Fin N // inc p l1 } := by
        rw [hCard l1]
        omega
      obtain ⟨⟨p1, hp1⟩⟩ := Fintype.card_pos_iff.mp hpos1
      have hmem := hpw p1 l1 hp1
      have hw_eq : N + l0.val = w := by change N + (w - N) = w; omega
      have hW := (hInit l0).2
      rw [hw_eq] at hW
      rw [hW] at hmem
      simp only [Set.mem_ofPred_eq, ind, decide_eq_true_eq] at hmem
      exact hne hmem.symm
  have hStepKind : ∀ w, base ≤ w → w < out → pos w → (∀ u < w, W u ≠ W w) →
      (∃ u v, Max.max u v < w ∧ W w = W u ∪ W v) ∨ (∃ u v, Max.max u v < w ∧ W w = W u ∩ W v) := by
    intro w hge hlt hpw hmin
    have hg : w - base < s := by
      change w < base + s - 1 at hlt
      omega
    have hweq : base + (w - base) = w := by omega
    obtain ⟨u, v, huv, hst⟩ := hSteps (w - base) hg
    rw [hweq] at huv hst
    rcases hst with hor | ⟨hand, _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hor
      rcases hor with heq | heq | heq
      · exact Or.inl ⟨u, v, huv, heq⟩
      · have hu : u < w := lt_of_le_of_lt (le_max_left u v) huv
        exact False.elim (hmin u hu heq.symm)
      · let l0 : Fin N := ⟨0, by omega⟩
        have hpos0 : 0 < Fintype.card { p : Fin N // inc p l0 } := by rw [hCard l0]; omega
        obtain ⟨⟨p0, hp0⟩⟩ := Fintype.card_pos_iff.mp hpos0
        have hmem := hpw p0 l0 hp0
        rw [heq] at hmem
        exact False.elim hmem
    · exact Or.inr ⟨u, v, huv, hand⟩
  obtain ⟨a, b, habLt, hInter, hna, hnb⟩ := hTop
  let w1 : ℕ := Nat.find (⟨a, rfl⟩ : ∃ w, W w = W a)
  let w2 : ℕ := Nat.find (⟨b, rfl⟩ : ∃ w, W w = W b)
  have hw1_eq : W w1 = W a := Nat.find_spec (⟨a, rfl⟩ : ∃ w, W w = W a)
  have hw2_eq : W w2 = W b := Nat.find_spec (⟨b, rfl⟩ : ∃ w, W w = W b)
  have hw1_min : ∀ u < w1, W u ≠ W w1 := by
    intro u hu hEq
    exact Nat.find_min (⟨a, rfl⟩ : ∃ w, W w = W a) hu (hEq.trans hw1_eq)
  have hw2_min : ∀ u < w2, W u ≠ W w2 := by
    intro u hu hEq
    exact Nat.find_min (⟨b, rfl⟩ : ∃ w, W w = W b) hu (hEq.trans hw2_eq)
  have hw1_lt : w1 < out := lt_of_le_of_lt (Nat.find_min' (⟨a, rfl⟩ : ∃ w, W w = W a) rfl) (lt_of_le_of_lt (le_max_left a b) habLt)
  have hw2_lt : w2 < out := lt_of_le_of_lt (Nat.find_min' (⟨b, rfl⟩ : ∃ w, W w = W b) rfl) (lt_of_le_of_lt (le_max_right a b) habLt)
  have hInter' : W out = W w1 ∩ W w2 := by rw [hInter, hw1_eq, hw2_eq]
  have hpos1 : pos w1 := fun p l hpl => by
    have h := hOut.1 p l hpl
    rw [hInter'] at h
    exact h.1
  have hpos2 : pos w2 := fun p l hpl => by
    have h := hOut.1 p l hpl
    rw [hInter'] at h
    exact h.2
  have hneg1 : ¬neg w1 := fun h => hna (by intro Y hY; rw [← hw1_eq]; exact h Y hY)
  have hneg2 : ¬neg w2 := fun h => hnb (by intro Y hY; rw [← hw2_eq]; exact h Y hY)
  have hw1_ge : base ≤ w1 := hNotRaw w1 hpos1
  have hw2_ge : base ≤ w2 := hNotRaw w2 hpos2
  rcases hStepKind w1 hw1_ge hw1_lt hpos1 hw1_min with hor1 | hand1
  · rcases hStepKind w2 hw2_ge hw2_lt hpos2 hw2_min with hor2 | hand2
    · exact @hBothOr q N inc _ hq hN hCard hProj s B W w1 w2 hsGe hsLt hInit hSteps hOut.2 hMin
        ⟨hw1_ge, hw1_lt, hw2_ge, hw2_lt⟩ hInter' ⟨hpos1, hpos2, hneg1, hneg2⟩ hor1 hor2 hLastIn hBcard
    · exact @hAndInput q N inc _ hq hN hCard hProj s B W w2 w1 hsGe hsLt hInit hSteps hOut.2 hMin
        ⟨hw2_ge, hw2_lt, hw1_ge, hw1_lt⟩ (hInter'.trans (Set.inter_comm _ _)) ⟨hpos2, hpos1, hneg2, hneg1⟩ hand2 hLastIn hBcard
  · exact @hAndInput q N inc _ hq hN hCard hProj s B W w1 w2 hsGe hsLt hInit hSteps hOut.2 hMin
      ⟨hw1_ge, hw1_lt, hw2_ge, hw2_lt⟩ hInter' ⟨hpos1, hpos2, hneg1, hneg2⟩ hand1 hLastIn hBcard
