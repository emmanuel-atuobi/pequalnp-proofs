import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18023_4
    (hIrred :
      ∀ (m n : ℕ) (E : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        E.Nonempty →
        (∀ a a' : Fin m, ∀ b b' : Fin n, a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        PEqualNP.TopForm.IsAO2 (m + n) C →
        (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C x =
          Decidable.decide (∃ p ∈ E, x (Fin.castAdd n p.1) = Bool.true ∧ x (Fin.natAdd m p.2) = Bool.true)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ C.size ∧
          PEqualNP.TopForm.IsAO2 (m + n) D ∧
          (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) D x =
            Decidable.decide (∃ p ∈ E, x (Fin.castAdd n p.1) = Bool.true ∧ x (Fin.natAdd m p.2) = Bool.true)) ∧
          (∀ g ∈ D.gates, g.inputs.Nodup) ∧
          (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (m + n) → Bool,
            (D.wires (List.ofFn x)).getD (m + n + i.val) Bool.false ≠
            (D.wires (List.ofFn x)).getD (m + n + j.val) Bool.false))
    (hCover :
      ∀ (m n : ℕ) (E : Finset (Fin m × Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        E.Nonempty →
        (∀ a a' : Fin m, ∀ b b' : Fin n, a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        PEqualNP.TopForm.IsAO2 (m + n) D →
        (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) D x =
          Decidable.decide (∃ p ∈ E, x (Fin.castAdd n p.1) = Bool.true ∧ x (Fin.natAdd m p.2) = Bool.true)) →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (m + n) → Bool,
          (D.wires (List.ofFn x)).getD (m + n + i.val) Bool.false ≠
          (D.wires (List.ofFn x)).getD (m + n + j.val) Bool.false) →
        ∃ (L : Finset (Fin m)) (R : Finset (Fin n)),
          (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ) := by
  classical
  intro m n I _ C hC4 hAO hFun
  let E : Finset (Fin m × Fin n) := Finset.univ.filter fun e => I e.1 e.2
  have hEmem : ∀ (a : Fin m) (b : Fin n), (a, b) ∈ E ↔ I a b := by
    intro a b
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hEmp : E = ∅
  · refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro a b hab
      have hm : (a, b) ∈ E := (hEmem a b).mpr hab
      rw [hEmp] at hm
      exact False.elim (Finset.notMem_empty _ hm)
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.zero_le]
  have hEne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmp
  have hC4E : ∀ a a' : Fin m, ∀ b b' : Fin n, a ≠ a' → b ≠ b' →
      ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E) := by
    intro a a' b b' ha hb h
    exact hC4 a a' b b' ha hb ⟨(hEmem a b).mp h.1, (hEmem a b').mp h.2.1, (hEmem a' b).mp h.2.2.1, (hEmem a' b').mp h.2.2.2⟩
  have hFunE : ∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C x =
      Decidable.decide (∃ p ∈ E, x (Fin.castAdd n p.1) = Bool.true ∧ x (Fin.natAdd m p.2) = Bool.true) := by
    intro x
    rw [hFun x]
    simp only [decide_eq_decide]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨(a, b), (hEmem a b).mpr hab, ha, hb⟩
    · rintro ⟨p, hp, ha, hb⟩
      exact ⟨p.1, p.2, (hEmem p.1 p.2).mp hp, ha, hb⟩
  obtain ⟨D, hDle, hDAO, hDfun, hDnd, hDdist⟩ := hIrred m n E C hEne hC4E hAO hFunE
  obtain ⟨L, R, hCov, hCard⟩ := hCover m n E D hEne hC4E hDAO hDfun hDnd hDdist
  let Bstar : Fin m → Finset (Fin n) := fun a => Finset.univ.filter fun b => (a, b) ∈ E
  let Astar : Fin n → Finset (Fin m) := fun b => Finset.univ.filter fun a => (a, b) ∈ E ∧ a ∉ L
  let L1 : Finset (Fin m) := L.filter fun a => (Bstar a).Nonempty
  let R1 : Finset (Fin n) := R.filter fun b => (Astar b).Nonempty
  let eL1 : ↥L1 ≃ Fin L1.card := L1.equivFin
  let eR1 : ↥R1 ≃ Fin R1.card := R1.equivFin
  let Afn : Fin (L1.card + R1.card) → Finset (Fin m) :=
    Fin.addCases (fun i => {(eL1.symm i).1}) (fun j => Astar (eR1.symm j).1)
  let Bfn : Fin (L1.card + R1.card) → Finset (Fin n) :=
    Fin.addCases (fun i => Bstar (eL1.symm i).1) (fun j => {(eR1.symm j).1})
  refine ⟨L1.card + R1.card, Afn, Bfn, ?_, ?_, ?_, ?_⟩
  · intro idx
    refine Fin.addCases ?_ ?_ idx
    · intro i
      simp only [Afn, Bfn, Fin.addCases_left]
      exact ⟨Finset.singleton_nonempty _, (Finset.mem_filter.mp (eL1.symm i).2).2⟩
    · intro j
      simp only [Afn, Bfn, Fin.addCases_right]
      exact ⟨(Finset.mem_filter.mp (eR1.symm j).2).2, Finset.singleton_nonempty _⟩
  · intro idx
    refine Fin.addCases ?_ ?_ idx
    · intro i a ha b hb
      simp only [Afn, Bfn, Fin.addCases_left, Finset.mem_singleton] at ha hb
      rw [ha]
      exact (hEmem _ _).mp (Finset.mem_filter.mp hb).2
    · intro j a ha b hb
      simp only [Afn, Bfn, Fin.addCases_right, Finset.mem_singleton] at ha hb
      rw [hb]
      exact (hEmem _ _).mp (Finset.mem_filter.mp ha).2.1
  · intro a b hab
    have he : (a, b) ∈ E := (hEmem a b).mpr hab
    by_cases haL : a ∈ L
    · have haL1 : a ∈ L1 := Finset.mem_filter.mpr ⟨haL, ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, he⟩⟩⟩
      refine ⟨Fin.castAdd R1.card (eL1 ⟨a, haL1⟩), ?_, ?_⟩
      · simp only [Afn, Fin.addCases_left, Equiv.symm_apply_apply, Finset.mem_singleton]
      · simp only [Bfn, Fin.addCases_left, Equiv.symm_apply_apply, Bstar, Finset.mem_filter, Finset.mem_univ, true_and]
        exact he
    · have hbR : b ∈ R := (hCov (a, b) he).resolve_left haL
      have hbR1 : b ∈ R1 := Finset.mem_filter.mpr ⟨hbR, ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, he, haL⟩⟩⟩
      refine ⟨Fin.natAdd L1.card (eR1 ⟨b, hbR1⟩), ?_, ?_⟩
      · simp only [Afn, Fin.addCases_right, Equiv.symm_apply_apply, Astar, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨he, haL⟩
      · simp only [Bfn, Fin.addCases_right, Equiv.symm_apply_apply, Finset.mem_singleton]
  · rw [Fin.sum_univ_add]
    have hLeftSum : ∑ i : Fin L1.card, ((Afn (Fin.castAdd R1.card i)).card + (Bfn (Fin.castAdd R1.card i)).card) =
        L1.card + (E.filter fun e => e.1 ∈ L).card := by
      have h1 : ∑ i : Fin L1.card, ((Afn (Fin.castAdd R1.card i)).card + (Bfn (Fin.castAdd R1.card i)).card) =
          ∑ a ∈ L1, (1 + (Bstar a).card) := by
        rw [← Finset.sum_coe_sort L1]
        refine Fintype.sum_equiv eL1.symm _ _ ?_
        intro i
        simp only [Afn, Bfn, Fin.addCases_left, Finset.card_singleton]
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      have hsub : E.filter (fun e => e.1 ∈ L) = L1.biUnion (fun a => (Bstar a).image (fun b => (a, b))) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image, L1, Bstar, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨he, haL⟩
          exact ⟨a, ⟨haL, ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, he⟩⟩⟩, b, he, rfl⟩
        · rintro ⟨a', ⟨ha'L, _⟩, b', he', hEq⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
          exact ⟨he', ha'L⟩
      rw [hsub, Finset.card_biUnion]
      · refine Finset.sum_congr rfl ?_
        intro a _
        exact (Finset.card_image_of_injective (Bstar a) (fun _ _ h => (Prod.mk.inj h).2)).symm
      · intro a1 _ a2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_image] at hp1 hp2
        obtain ⟨b1, _, rfl⟩ := hp1
        obtain ⟨b2, _, hEq⟩ := hp2
        exact hne (Prod.mk.inj hEq).1.symm
    have hRightSum : ∑ j : Fin R1.card, ((Afn (Fin.natAdd L1.card j)).card + (Bfn (Fin.natAdd L1.card j)).card) =
        (E.filter fun e => e.1 ∉ L).card + R1.card := by
      have h1 : ∑ j : Fin R1.card, ((Afn (Fin.natAdd L1.card j)).card + (Bfn (Fin.natAdd L1.card j)).card) =
          ∑ b ∈ R1, ((Astar b).card + 1) := by
        rw [← Finset.sum_coe_sort R1]
        refine Fintype.sum_equiv eR1.symm _ _ ?_
        intro j
        simp only [Afn, Bfn, Fin.addCases_right, Finset.card_singleton]
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      have hsub : E.filter (fun e => e.1 ∉ L) = R1.biUnion (fun b => (Astar b).image (fun a => (a, b))) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image, R1, Astar, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨he, haL⟩
          have hbR : b ∈ R := (hCov (a, b) he).resolve_left haL
          exact ⟨b, ⟨hbR, ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, he, haL⟩⟩⟩, a, ⟨he, haL⟩, rfl⟩
        · rintro ⟨b', _, a', ⟨he', ha'L⟩, hEq⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
          exact ⟨he', ha'L⟩
      rw [hsub, Finset.card_biUnion]
      · refine Finset.sum_congr rfl ?_
        intro b _
        exact (Finset.card_image_of_injective (Astar b) (fun _ _ h => (Prod.mk.inj h).1)).symm
      · intro b1 _ b2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_image] at hp1 hp2
        obtain ⟨a1, _, rfl⟩ := hp1
        obtain ⟨a2, _, hEq⟩ := hp2
        exact hne (Prod.mk.inj hEq).2.symm
    have hL1le : L1.card ≤ L.card := Finset.card_filter_le _ _
    have hR1le : R1.card ≤ R.card := Finset.card_filter_le _ _
    have hEpart : (E.filter fun e => e.1 ∈ L).card + (E.filter fun e => e.1 ∉ L).card = E.card := by
      have hd : Disjoint (E.filter fun e => e.1 ∈ L) (E.filter fun e => e.1 ∉ L) := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        exact (Finset.mem_filter.mp he2).2 (Finset.mem_filter.mp he1).2
      have hu : (E.filter fun e => e.1 ∈ L) ∪ (E.filter fun e => e.1 ∉ L) = E := by
        ext e
        simp only [Finset.mem_union, Finset.mem_filter]
        by_cases h : e.1 ∈ L <;> tauto
      rw [← Finset.card_union_of_disjoint hd, hu]
    rw [hLeftSum, hRightSum]
    omega
