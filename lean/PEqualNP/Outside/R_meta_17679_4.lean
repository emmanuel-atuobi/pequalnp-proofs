import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17679_4
    (hIrred :
      ∀ (m n : ℕ) (E : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        have fE : Finset (Fin m × Fin n) → (Fin (m + n) → Bool) → Bool :=
          fun E0 z => Decidable.decide (∃ e ∈ E0, z (Fin.castAdd n e.1) = Bool.true ∧ z (Fin.natAdd m e.2) = Bool.true);
        (4 : ℕ) ≤ E.card →
        (∀ a b : Fin m, ∀ c d : Fin n, a ≠ b → c ≠ d →
          ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (m + n) C →
        PEqualNP.MetaComplexity.circuitFun (m + n) C = fE E →
        m % (2 : ℕ) = (0 : ℕ) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ C.size ∧
          PEqualNP.TopForm.IsAO2 (m + n) D ∧
          PEqualNP.MetaComplexity.circuitFun (m + n) D = fE E ∧
          (∀ g ∈ D.gates, g.inputs.Nodup) ∧
          (∀ i j : Fin D.size, i ≠ j → ∃ z : Fin (m + n) → Bool,
            PEqualNP.EdgeOwnership.gateVal (m + n) D i.val z ≠
            PEqualNP.EdgeOwnership.gateVal (m + n) D j.val z))
    (hPeel :
      ∀ (m n : ℕ) (E : Finset (Fin m × Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        let inc : Fin (m + n) → Fin m × Fin n → Prop :=
          fun v e => Fin.castAdd n e.1 = v ∨ Fin.natAdd m e.2 = v;
        have fE : Finset (Fin m × Fin n) → (Fin (m + n) → Bool) → Bool :=
          fun E0 z => Decidable.decide (∃ e ∈ E0, z (Fin.castAdd n e.1) = Bool.true ∧ z (Fin.natAdd m e.2) = Bool.true);
        (4 : ℕ) ≤ E.card →
        (∀ a b : Fin m, ∀ c d : Fin n, a ≠ b → c ≠ d →
          ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (m + n) D →
        PEqualNP.MetaComplexity.circuitFun (m + n) D = fE E →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ z : Fin (m + n) → Bool,
          PEqualNP.EdgeOwnership.gateVal (m + n) D i.val z ≠
          PEqualNP.EdgeOwnership.gateVal (m + n) D j.val z) →
        (∃ u : Fin (m + n), (Finset.filter (inc u) E).card = (1 : ℕ)) →
        (∀ u v : Fin (m + n), u ≠ v → (Finset.filter (inc u) E).card = (1 : ℕ) →
          (∃ e ∈ E, inc u e ∧ inc v e) → (3 : ℕ) ≤ (Finset.filter (inc v) E).card) →
        (∀ v : Fin (m + n), {e ∈ E | ¬inc v e}.Nonempty) →
        m % (2 : ℕ) = (0 : ℕ) →
        ∃ v : Fin (m + n), (Finset.filter (inc v) E).Nonempty ∧
          ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
            PEqualNP.MetaComplexity.Monotone2 C' ∧
            PEqualNP.MetaComplexity.circuitFun (m + n) C' = fE ({e ∈ E | ¬inc v e}) ∧
            C'.size + (Finset.filter (inc v) E).card + (1 : ℕ) ≤ D.size) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → (Fin (x1 + x2) → Bool) → Bool := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : Fin (x1 + x2) → Bool) => Decidable.decide (∃ x8 ∈ x6, x7 (Fin.castAdd x2 x8.1) = Bool.true ∧ x7 (Fin.natAdd x1 x8.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 = x6 x3 → (∃ (x10 : Fin (x1 + x2)), (Finset.filter (x5 x10) x3).card = (1 : ℕ)) → (∀ (x11 x12 : Fin (x1 + x2)), x11 ≠ x12 → (Finset.filter (x5 x11) x3).card = (1 : ℕ) → (∃ x15 ∈ x3, x5 x11 x15 ∧ x5 x12 x15) → (3 : ℕ) ≤ (Finset.filter (x5 x12) x3).card) → (∀ (x12 : Fin (x1 + x2)), {x13 ∈ x3 | ¬x5 x12 x13}.Nonempty) → x1 % (2 : ℕ) = (0 : ℕ) → ∃ (x14 : Fin (x1 + x2)), (Finset.filter (x5 x14) x3).Nonempty ∧ ∃ (x15 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x15 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x15 = x6 ({x16 ∈ x3 | ¬x5 x14 x16}) ∧ x15.size + (Finset.filter (x5 x14) x3).card + (1 : ℕ) ≤ x4.size := by
  classical
  intro m n E C inc fE hC4 hAO hFun hLeaf hNbr3 hDelNE hEven
  have hSepLR : ∀ (a : Fin m) (b : Fin n), Fin.castAdd n a ≠ Fin.natAdd m b := by
    intro a b h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hE4 : (4 : ℕ) ≤ E.card := by
    obtain ⟨u, hu1⟩ := hLeaf
    have hune : (Finset.filter (inc u) E).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e0, he0⟩ := hune
    have he0E : e0 ∈ E := (Finset.mem_filter.mp he0).1
    have he0u : inc u e0 := (Finset.mem_filter.mp he0).2
    have hv_ex : ∃ v : Fin (m + n), u ≠ v ∧ inc v e0 := by
      rcases he0u with hL | hR
      · refine ⟨Fin.natAdd m e0.2, ?_, Or.inr rfl⟩
        rw [← hL]
        exact hSepLR e0.1 e0.2
      · refine ⟨Fin.castAdd n e0.1, ?_, Or.inl rfl⟩
        rw [← hR]
        exact (hSepLR e0.1 e0.2).symm
    obtain ⟨v, huv, he0v⟩ := hv_ex
    have hv3 : (3 : ℕ) ≤ (Finset.filter (inc v) E).card :=
      hNbr3 u v huv hu1 ⟨e0, he0E, he0u, he0v⟩
    have hvdel : (1 : ℕ) ≤ ({e ∈ E | ¬inc v e}).card :=
      Finset.card_pos.mpr (hDelNE v)
    have hpart : (Finset.filter (inc v) E).card + ({e ∈ E | ¬inc v e}).card = E.card := by
      have hd : Disjoint (Finset.filter (inc v) E) ({e ∈ E | ¬inc v e}) := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        exact (Finset.mem_filter.mp he2).2 (Finset.mem_filter.mp he1).2
      have hu : Finset.filter (inc v) E ∪ ({e ∈ E | ¬inc v e}) = E := by
        ext e
        simp only [Finset.mem_union, Finset.mem_filter]
        by_cases h : inc v e <;> tauto
      rw [← Finset.card_union_of_disjoint hd, hu]
    omega
  obtain ⟨D, hDle, hDAO, hDFun, hDNodup, hDDist⟩ := hIrred m n E C hE4 hC4 hAO hFun hEven
  obtain ⟨v, hvNE, C', hC'M, hC'Fun, hC'Sz⟩ :=
    hPeel m n E D hE4 hC4 hDAO hDFun hDNodup hDDist hLeaf hNbr3 hDelNE hEven
  exact ⟨v, hvNE, C', hC'M, hC'Fun, le_trans hC'Sz hDle⟩
