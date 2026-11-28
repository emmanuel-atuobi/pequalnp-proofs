import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17259_3
    (hNoBadAnd :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        let x5 : Type := Fin x2 → Bool;
        have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);
        (299 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →
        (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →
        ∀ (x11 x12 : ℕ) (x14 : ℕ → Set (x5 × x5)),
          x2 + x2 ≤ x12 →
          x12 < x2 + x2 + x11 →
          (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →
          (∀ x17 < x11,
            ∃ x19 < x2 + x2 + x17,
              ∃ x20 < x2 + x2 + x17,
                have x21 : Set (x5 × x5) := x14 (x2 + x2 + x17);
                x21 ∈ [x14 x19 ∪ x14 x20, x14 x19, ∅] ∨
                x21 = x14 x19 ∩ x14 x20 ∧ (∃ (x22 : Set x5) (x23 : Set x5), x14 x19 = x22 ×ˢ Set.univ ∧ x14 x20 = Set.univ ×ˢ x23)) →
          (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) →
          (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 →
            (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) →
          ¬x1 % (2 : ℕ) = (0 : ℕ) →
          x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11)
    (hHasBadAnd :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        let x5 : Type := Fin x2 → Bool;
        have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);
        (299 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →
        (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →
        ∀ (x11 x12 : ℕ) (x13 : Finset ℕ) (x14 : ℕ → Set (x5 × x5)),
          x2 + x2 ≤ x12 →
          x12 < x2 + x2 + x11 →
          x13.Nonempty →
          (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →
          (∀ x17 < x11,
            ∃ x19 < x2 + x2 + x17,
              ∃ x20 < x2 + x2 + x17,
                have x21 : Set (x5 × x5) := x14 (x2 + x2 + x17);
                x21 ∈ [x14 x19 ∪ x14 x20, x14 x19, ∅] ∨
                x21 = x14 x19 ∩ x14 x20 ∧ (x17 ∈ x13 ∨ ∃ (x22 : Set x5) (x23 : Set x5), x14 x19 = x22 ×ˢ Set.univ ∧ x14 x20 = Set.univ ×ˢ x23)) →
          (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) →
          (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 →
            (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) →
          (100 : ℕ) * x13.card < x2 * x1 →
          ¬x1 % (2 : ℕ) = (0 : ℕ) →
          x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);   (299 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           ∀ (x11 x12 : ℕ) (x13 : Finset ℕ) (x14 : ℕ → Set (x5 × x5)),             x12 < x2 + x2 + x11 →               (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →                 (∀ x17 < x11,                     ∃ x19 < x2 + x2 + x17,                       ∃ x20 < x2 + x2 + x17,                         have x21 : Set (x5 × x5) := x14 (x2 + x2 + x17);                         x21 ∈ [x14 x19 ∪ x14 x20, x14 x19, ∅] ∨ x21 = x14 x19 ∩ x14 x20 ∧ (x17 ∈ x13 ∨ ∃ (x22 : Set x5) (x23 : Set x5), x14 x19 = x22 ×ˢ Set.univ ∧ x14 x20 = Set.univ ×ˢ x23)) →                   (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) → (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) → (100 : ℕ) * x13.card < x2 * x1 → ¬x1 % (2 : ℕ) = (0 : ℕ) → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11 := by
  intro q N inc _ V ind hq hN hCard hProj s out B W houtLt hInit hSteps hPos hNeg hBcard hOdd
  have hNpos : 0 < N := by rw [hN]; omega
  have houtGe : N + N ≤ out := by
    by_contra hlt
    have hlt : out < N + N := Nat.lt_of_not_ge hlt
    by_cases h1 : out < N
    · let p0 : Fin N := ⟨out, h1⟩
      let l0 : Fin N := ⟨0, hNpos⟩
      have hcard_l0 : Fintype.card { p : Fin N // inc p l0 } = q + 1 := hCard l0
      have hsub : (Finset.univ.filter fun p : Fin N => inc p l0) ⊆ {p0} := by
        intro p hp
        have hinc : inc p l0 := (Finset.mem_filter.mp hp).2
        have hmem := hPos p l0 hinc
        have hW := (hInit p0).1
        change W out = {z : V × V | z.1 p0 = Bool.true} at hW
        rw [hW] at hmem
        change decide (p0 = p) = true at hmem
        exact Finset.mem_singleton.mpr (of_decide_eq_true hmem).symm
      have hc1 : (Finset.univ.filter fun p : Fin N => inc p l0).card ≤ 1 :=
        le_trans (Finset.card_le_card hsub) (by simp only [Finset.card_singleton]; rfl)
      have hc2 : (Finset.univ.filter fun p : Fin N => inc p l0).card = Fintype.card { p : Fin N // inc p l0 } := by
        rw [Fintype.card_subtype]
      omega
    · let l0 : Fin N := ⟨out - N, by omega⟩
      have hout_eq : N + l0.val = out := by change N + (out - N) = out; omega
      have hcard1 : Fintype.card { l : Fin N // ind l0 l = Bool.true } ≤ q := by
        have hsub : (Finset.univ.filter fun l : Fin N => ind l0 l = Bool.true) ⊆ {l0} := by
          intro l hl
          have ht := (Finset.mem_filter.mp hl).2
          simp only [ind, decide_eq_true_eq] at ht
          exact Finset.mem_singleton.mpr ht
        have hc1 : (Finset.univ.filter fun l : Fin N => ind l0 l = Bool.true).card ≤ 1 :=
          le_trans (Finset.card_le_card hsub) (by simp only [Finset.card_singleton]; rfl)
        rw [Fintype.card_subtype]
        omega
      have hnot := hNeg (ind l0) hcard1
      have hW := (hInit l0).2
      rw [hout_eq] at hW
      rw [hW] at hnot
      exact hnot (show decide (l0 = l0) = true from decide_eq_true rfl)
  by_cases hBemp : B = ∅
  · apply @hNoBadAnd q N inc _ hq hN hCard hProj s out W houtGe houtLt hInit _ hPos hNeg hOdd
    intro g hg
    obtain ⟨u, hu, v, hv, hst⟩ := hSteps g hg
    refine ⟨u, hu, v, hv, ?_⟩
    rcases hst with hor | ⟨hand, hB | hRect⟩
    · exact Or.inl hor
    · rw [hBemp] at hB
      exact False.elim (Finset.notMem_empty g hB)
    · exact Or.inr ⟨hand, hRect⟩
  · exact @hHasBadAnd q N inc _ hq hN hCard hProj s out B W houtGe houtLt
      (Finset.nonempty_iff_ne_empty.mpr hBemp) hInit hSteps hPos hNeg hBcard hOdd
