import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3364_3
    (hNoBadAnd :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        let x5 : Type := Fin x2 → Bool;
        have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);
        (100 : ℕ) < x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
        ∀ (x9 x10 : ℕ) (x12 : ℕ → Set (x5 × x5)),
          x2 + x2 ≤ x10 →
          x10 < x2 + x2 + x9 →
          (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : x5 × x5 | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : x5 × x5 | x15.2 x14 = Bool.true}) →
          (∀ x15 < x9,
            ∃ x17 < x2 + x2 + x15,
              ∃ x18 < x2 + x2 + x15,
                have x19 : Set (x5 × x5) := x12 (x2 + x2 + x15);
                x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨
                x19 = x12 x17 ∩ x12 x18 ∧ (∃ (x20 : Set x5) (x21 : Set x5), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →
          (∀ (x16 x17 : Fin x2), x3 x16 x17 → (x6 x16, x6 x17) ∈ x12 x10) →
          (∀ (x17 : x5), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 →
            (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) →
          x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9)
    (hHasBadAnd :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        let x5 : Type := Fin x2 → Bool;
        have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);
        (100 : ℕ) < x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
        ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set (x5 × x5)),
          x2 + x2 ≤ x10 →
          x10 < x2 + x2 + x9 →
          x11.Nonempty →
          (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : x5 × x5 | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : x5 × x5 | x15.2 x14 = Bool.true}) →
          (∀ x15 < x9,
            ∃ x17 < x2 + x2 + x15,
              ∃ x18 < x2 + x2 + x15,
                have x19 : Set (x5 × x5) := x12 (x2 + x2 + x15);
                x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨
                x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set x5) (x21 : Set x5), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →
          (∀ (x16 x17 : Fin x2), x3 x16 x17 → (x6 x16, x6 x17) ∈ x12 x10) →
          (∀ (x17 : x5), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 →
            (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) →
          (100 : ℕ) * x11.card < x2 * x1 →
          x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → ∃ (x19 : Fin x9 → Finset (Fin x2)) (x20 : Fin x9 → Finset (Fin x2)), (∀ (x21 : Fin x9), ∀ x22 ∈ x19 x21, ∀ x24 ∈ x20 x21, x3 x22 x24) ∧ (∀ (x21 x22 : Fin x2), x3 x21 x22 → ∃ (x24 : Fin x9), x21 ∈ x19 x24 ∧ x22 ∈ x20 x24) ∧ ∑ x21 : Fin x9, ((x19 x21).card + (x20 x21).card) ≤ (100 : ℕ) * x9 + x2 := by
  classical
  intro q N inc _ hq hN hCard hProj s out B W houtLt hInit hSteps hPos hNeg hBcard
  let V : Type := Fin N → Bool
  let ind : Fin N → Fin N → Bool := fun a b => Decidable.decide (b = a)
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
  have hBound : N * (q + 1) ≤ 100 * s := by
    by_cases hBemp : B = ∅
    · apply @hNoBadAnd q N inc _ hq hN hCard hProj s out W houtGe houtLt hInit _ hPos hNeg
      intro g hg
      obtain ⟨u, hu, v, hv, hst⟩ := hSteps g hg
      refine ⟨u, hu, v, hv, ?_⟩
      rcases hst with hor | hcopy | hemp | ⟨hand, hB | hRect⟩
      · exact Or.inl hor
      · exact Or.inr (Or.inl hcopy)
      · exact Or.inr (Or.inr (Or.inl hemp))
      · rw [hBemp] at hB
        exact False.elim (Finset.notMem_empty g hB)
      · exact Or.inr (Or.inr (Or.inr ⟨hand, hRect⟩))
    · exact @hHasBadAnd q N inc _ hq hN hCard hProj s out B W houtGe houtLt
        (Finset.nonempty_iff_ne_empty.mpr hBemp) hInit hSteps hPos hNeg hBcard
  have hNs : N ≤ s := by
    have h100 : 100 * N ≤ N * (q + 1) := by
      calc 100 * N = N * 100 := Nat.mul_comm 100 N
        _ ≤ N * (q + 1) := Nat.mul_le_mul_left N (by omega)
    omega
  let A : Fin s → Finset (Fin N) := fun i =>
    if h : i.val < N then Finset.univ.filter (fun p : Fin N => inc p ⟨i.val, h⟩) else ∅
  let Bset : Fin s → Finset (Fin N) := fun i =>
    if h : i.val < N then {⟨i.val, h⟩} else ∅
  refine ⟨A, Bset, ?_, ?_, ?_⟩
  · intro i p hp l hl
    by_cases h : i.val < N
    · simp only [A, Bset, h, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hp hl
      rw [hl]
      exact hp
    · simp only [A, h, ↓reduceDIte] at hp
      exact False.elim (Finset.notMem_empty p hp)
  · intro p l hinc
    refine ⟨⟨l.val, Nat.lt_of_lt_of_le l.isLt hNs⟩, ?_, ?_⟩
    · simp only [A, l.isLt, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hinc
    · simp only [Bset, l.isLt, ↓reduceDIte, Finset.mem_singleton]
  · have hterm : ∀ i : Fin s, (A i).card + (Bset i).card = if i.val < N then q + 2 else 0 := by
      intro i
      by_cases h : i.val < N
      · simp only [A, Bset, h, ↓reduceDIte, ↓reduceIte, Finset.card_singleton]
        rw [← Fintype.card_subtype, hCard ⟨i.val, h⟩]
      · simp only [A, Bset, h, ↓reduceDIte, ↓reduceIte, Finset.card_empty, Nat.add_zero]
    have hsum_eq : ∑ i : Fin s, ((A i).card + (Bset i).card) =
        (Finset.univ.filter fun i : Fin s => i.val < N).card * (q + 2) := by
      calc ∑ i : Fin s, ((A i).card + (Bset i).card)
          = ∑ i : Fin s, (if i.val < N then q + 2 else 0) := Finset.sum_congr rfl (fun i _ => hterm i)
        _ = (Finset.univ.filter fun i : Fin s => i.val < N).card * (q + 2) := by
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    have hfilt_le : (Finset.univ.filter fun i : Fin s => i.val < N).card ≤ N := by
      calc (Finset.univ.filter fun i : Fin s => i.val < N).card
          = ((Finset.univ.filter fun i : Fin s => i.val < N).image Fin.val).card :=
            (Finset.card_image_of_injective _ Fin.val_injective).symm
        _ ≤ (Finset.range N).card := Finset.card_le_card (by
            intro k hk
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
        _ = N := Finset.card_range N
    rw [hsum_eq]
    have hmul : (Finset.univ.filter fun i : Fin s => i.val < N).card * (q + 2) ≤ N * (q + 2) :=
      Nat.mul_le_mul_right (q + 2) hfilt_le
    have hdist : N * (q + 2) = N * (q + 1) + N := by
      calc N * (q + 2) = N * ((q + 1) + 1) := rfl
        _ = N * (q + 1) + N * 1 := Nat.mul_add N (q + 1) 1
        _ = N * (q + 1) + N := by rw [Nat.mul_one]
    omega
