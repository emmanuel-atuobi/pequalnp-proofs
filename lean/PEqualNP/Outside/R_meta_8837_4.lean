import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8837_4
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
          x15 x13 →
          (∀ x22 < x13, ¬(x15 x22 ∧ x16 x22)) →
          x12 ≤ w1 ∧ w1 < x13 ∧ x12 ≤ w2 ∧ w2 < x13 →
          x11 x13 = x11 w1 ∪ x11 w2 →
          x16 w1 ∧ x16 w2 ∧ ¬x15 w1 ∧ ¬x15 w2 →
          (∃ (u v : ℕ), Max.max u v < w1 ∧ x11 w1 = x11 u ∩ x11 v) →
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
          x15 x13 →
          (∀ x22 < x13, ¬(x15 x22 ∧ x16 x22)) →
          x12 ≤ w1 ∧ w1 < x13 ∧ x12 ≤ w2 ∧ w2 < x13 →
          x11 x13 = x11 w1 ∪ x11 w2 →
          x16 w1 ∧ x16 w2 ∧ ¬x15 w1 ∧ ¬x15 w2 →
          (∃ (u v : ℕ), Max.max u v < w1 ∧ x11 w1 = x11 u ∪ x11 v) →
          (∃ (u v : ℕ), Max.max u v < w2 ∧ x11 w2 = x11 u ∪ x11 v) →
          (100 : ℕ) * x10.card < x2 * x1 →
          x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (199 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 : ℕ) (x10 : Finset ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : ℕ := x12 + x9 - (1 : ℕ);             have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);             have x15 : ℕ → Prop := fun (x15 : ℕ) => ∀ (x16 x17 : Fin x2), x3 x16 x17 → (x14 x16, x14 x17) ∈ x11 x15;             have x16 : ℕ → Prop := fun (x16 : ℕ) => ∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x11 x16;             x12 ≤ x9 + (1 : ℕ) → x9 < x2 * (x1 / (100 : ℕ) + (1 : ℕ)) → (∀ (x19 : Fin x2), x11 ↑x19 = {x20 : (Fin x2 → Bool) × (Fin x2 → Bool) | x20.1 x19 = Bool.true} ∧ x11 (x2 + ↑x19) = {x20 : (Fin x2 → Bool) × (Fin x2 → Bool) | x20.2 x19 = Bool.true}) → (∀ x20 < x9, ∃ (x22 : ℕ) (x23 : ℕ), Max.max x22 x23 < x12 + x20 ∧ (x11 (x12 + x20) ∈ [x11 x22 ∪ x11 x23, x11 x22, ∅] ∨ x11 (x12 + x20) = x11 x22 ∩ x11 x23 ∧ (x20 ∈ x10 ∨ ∃ (x24 : Set (Fin x2 → Bool)) (x25 : Set (Fin x2 → Bool)), x11 x22 = x24 ×ˢ Set.univ ∧ x11 x23 = Set.univ ×ˢ x25))) → x15 x13 ∧ x16 x13 → (∀ x22 < x13, ¬(x15 x22 ∧ x16 x22)) → (∃ (x23 : ℕ) (x24 : ℕ), Max.max x23 x24 < x13 ∧ x11 x13 = x11 x23 ∪ x11 x24 ∧ ¬x15 x23 ∧ ¬x15 x24) → (100 : ℕ) * x10.card < x2 * x1 → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9 := by
  classical
  intro q N inc _ hq hN hCard hProj s B W base out ind pos neg hsGe hsLt hInit hSteps hOut hMin hTop hBcard
  have hNotRaw : ∀ w, neg w → base ≤ w := by
    intro w hnw
    by_contra hlt
    have hlt : w < N + N := Nat.lt_of_not_ge hlt
    by_cases h1 : w < N
    · let p0 : Fin N := ⟨w, h1⟩
      let Y : Fin N → Bool := fun _ => Bool.false
      have hYcard : Fintype.card { l : Fin N // Y l = Bool.true } ≤ q := by
        rw [@Fintype.card_eq_zero _ _ ⟨fun x => Bool.noConfusion x.2⟩]
        omega
      have hnot := hnw Y hYcard
      have hW := (hInit p0).1
      change W w = {z : (Fin N → Bool) × (Fin N → Bool) | z.1 p0 = Bool.true} at hW
      rw [hW] at hnot
      apply hnot
      simp only [Set.mem_setOf_eq, Y, Bool.false_eq_true, and_false, exists_false, not_false_eq_true, decide_true]
    · let l0 : Fin N := ⟨w - N, by omega⟩
      let Y : Fin N → Bool := fun l => Decidable.decide (l = l0)
      have hYcard : Fintype.card { l : Fin N // Y l = Bool.true } ≤ q := by
        rw [Fintype.card_subtype]
        have hsub : (Finset.univ.filter fun l : Fin N => Y l = Bool.true) ⊆ {l0} := by
          intro l hl
          have hm := (Finset.mem_filter.mp hl).2
          simp only [Y, decide_eq_true_eq] at hm
          exact Finset.mem_singleton.mpr hm
        have hc := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at hc
        omega
      have hnot := hnw Y hYcard
      have hw_eq : N + l0.val = w := by change N + (w - N) = w; omega
      have hW := (hInit l0).2
      rw [hw_eq] at hW
      rw [hW] at hnot
      apply hnot
      simp only [Set.mem_setOf_eq, Y, decide_true]
  have hStepKind : ∀ w, base ≤ w → w < out → W w ≠ ∅ → (∀ u < w, W u ≠ W w) →
      (∃ u v, Max.max u v < w ∧ W w = W u ∪ W v) ∨ (∃ u v, Max.max u v < w ∧ W w = W u ∩ W v) := by
    intro w hge hlt hne hmin
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
      · exact False.elim (hne heq)
    · exact Or.inr ⟨u, v, huv, hand⟩
  obtain ⟨a, b, habLt, hUnion, hna, hnb⟩ := hTop
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
  have hUnion' : W out = W w1 ∪ W w2 := by rw [hUnion, hw1_eq, hw2_eq]
  have hneg1 : neg w1 := fun Y hY hmem => by
    apply hOut.2 Y hY
    rw [hUnion']
    exact Or.inl hmem
  have hneg2 : neg w2 := fun Y hY hmem => by
    apply hOut.2 Y hY
    rw [hUnion']
    exact Or.inr hmem
  have hpos1 : ¬pos w1 := fun h => hna (by intro p l hpl; rw [← hw1_eq]; exact h p l hpl)
  have hpos2 : ¬pos w2 := fun h => hnb (by intro p l hpl; rw [← hw2_eq]; exact h p l hpl)
  have hne1 : W w1 ≠ ∅ := by
    intro hE
    apply hpos2
    intro p l hpl
    have hm := hOut.1 p l hpl
    rw [hUnion', hE, Set.empty_union] at hm
    exact hm
  have hne2 : W w2 ≠ ∅ := by
    intro hE
    apply hpos1
    intro p l hpl
    have hm := hOut.1 p l hpl
    rw [hUnion', hE, Set.union_empty] at hm
    exact hm
  have hw1_ge : base ≤ w1 := hNotRaw w1 hneg1
  have hw2_ge : base ≤ w2 := hNotRaw w2 hneg2
  rcases hStepKind w1 hw1_ge hw1_lt hne1 hw1_min with hor1 | hand1
  · rcases hStepKind w2 hw2_ge hw2_lt hne2 hw2_min with hor2 | hand2
    · exact @hBothOr q N inc _ hq hN hCard hProj s B W w1 w2 hsGe hsLt hInit hSteps hOut.1 hMin
        ⟨hw1_ge, hw1_lt, hw2_ge, hw2_lt⟩ hUnion' ⟨hneg1, hneg2, hpos1, hpos2⟩ hor1 hor2 hBcard
    · exact @hAndInput q N inc _ hq hN hCard hProj s B W w2 w1 hsGe hsLt hInit hSteps hOut.1 hMin
        ⟨hw2_ge, hw2_lt, hw1_ge, hw1_lt⟩ (hUnion'.trans (Set.union_comm _ _)) ⟨hneg2, hneg1, hpos2, hpos1⟩ hand2 hBcard
  · exact @hAndInput q N inc _ hq hN hCard hProj s B W w1 w2 hsGe hsLt hInit hSteps hOut.1 hMin
      ⟨hw1_ge, hw1_lt, hw2_ge, hw2_lt⟩ hUnion' ⟨hneg1, hneg2, hpos1, hpos2⟩ hand1 hBcard
