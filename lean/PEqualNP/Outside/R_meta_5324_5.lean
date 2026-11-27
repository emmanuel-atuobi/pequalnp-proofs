import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5324_5
    (hPureOr :
      ∀ (m n : ℕ) (E F M : Finset (Fin m × Fin n))
        (C : PEqualNP.CircuitLowerBounds.Circuit) (P : Finset (ℕ × ℕ)),
        P.card < F.card →
        F.Nonempty →
        P.Nonempty →
        (∀ a b : Fin m, ∀ c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (m + n) C →
        (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (∀ p ∈ P, ∀ x : Fin (m + n) → Bool,
          (C.wires (List.ofFn x)).getD p.1 Bool.false = Bool.true →
          (C.wires (List.ofFn x)).getD p.2 Bool.false = Bool.true →
          ∃ (a : Fin m) (b : Fin n), (a, b) ∈ E ∧ x (Fin.castAdd n a) = Bool.true ∧ x (Fin.natAdd m b) = Bool.true) →
        (∀ e ∈ F, e ∈ E ∧ ∃ p ∈ P,
          (C.wires (List.ofFn fun i : Fin (m + n) => Decidable.decide (i = Fin.castAdd n e.1 ∨ i = Fin.natAdd m e.2))).getD p.1 Bool.false = Bool.true ∧
          (C.wires (List.ofFn fun i : Fin (m + n) => Decidable.decide (i = Fin.castAdd n e.1 ∨ i = Fin.natAdd m e.2))).getD p.2 Bool.false = Bool.true) →
        M ⊆ F →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1.1 = e2.1 → e1 = e2) →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1.2 = e2.2 → e1 = e2) →
        F.card + M.card ≤ C.size + (2 : ℕ) * P.card)
    (hHasAnd :
      ∀ (m n : ℕ) (E F M : Finset (Fin m × Fin n))
        (C : PEqualNP.CircuitLowerBounds.Circuit) (P : Finset (ℕ × ℕ)),
        P.card < F.card →
        F.Nonempty →
        P.Nonempty →
        (∀ a b : Fin m, ∀ c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (m + n) C →
        (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ x : Fin (m + n) → Bool, (C.wires (List.ofFn x)).getD (m + n + j) Bool.false = Bool.true ∧
            ¬∃ (a : Fin m) (b : Fin n), (a, b) ∈ E ∧ x (Fin.castAdd n a) = Bool.true ∧ x (Fin.natAdd m b) = Bool.true) →
        (∀ p ∈ P, ∀ x : Fin (m + n) → Bool,
          (C.wires (List.ofFn x)).getD p.1 Bool.false = Bool.true →
          (C.wires (List.ofFn x)).getD p.2 Bool.false = Bool.true →
          ∃ (a : Fin m) (b : Fin n), (a, b) ∈ E ∧ x (Fin.castAdd n a) = Bool.true ∧ x (Fin.natAdd m b) = Bool.true) →
        (∀ e ∈ F, e ∈ E ∧ ∃ p ∈ P,
          (C.wires (List.ofFn fun i : Fin (m + n) => Decidable.decide (i = Fin.castAdd n e.1 ∨ i = Fin.natAdd m e.2))).getD p.1 Bool.false = Bool.true ∧
          (C.wires (List.ofFn fun i : Fin (m + n) => Decidable.decide (i = Fin.castAdd n e.1 ∨ i = Fin.natAdd m e.2))).getD p.2 Bool.false = Bool.true) →
        M ⊆ F →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1.1 = e2.1 → e1 = e2) →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1.2 = e2.2 → e1 = e2) →
        F.card + M.card ≤ C.size + (2 : ℕ) * P.card) :
    ∀ (x1 x2 : ℕ) (x3 x4 x5 : Finset (Fin x1 × Fin x2)) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Finset (ℕ × ℕ)), (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 → ¬((x8, x10) ∈ x3 ∧ (x8, x11) ∈ x3 ∧ (x9, x10) ∈ x3 ∧ (x9, x11) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x6 → (∀ x10 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD (x1 + x2 + x10) Bool.false = Bool.true ∧ ¬∃ (x14 : Fin x1) (x15 : Fin x2), (x14, x15) ∈ x3 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x1 x15) = Bool.true) → (∀ x11 ∈ x7, ∀ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD x11.1 Bool.false = Bool.true → (x6.wires (List.ofFn x13)).getD x11.2 Bool.false = Bool.true → ∃ (x16 : Fin x1) (x17 : Fin x2), (x16, x17) ∈ x3 ∧ x13 (Fin.castAdd x2 x16) = Bool.true ∧ x13 (Fin.natAdd x1 x17) = Bool.true) → (∀ x12 ∈ x4, x12 ∈ x3 ∧ ∃ x14 ∈ x7, (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.1 Bool.false = Bool.true ∧ (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.2 Bool.false = Bool.true) → x5 ⊆ x4 → (∀ x14 ∈ x5, ∀ x16 ∈ x5, x14.1 = x16.1 → x14 = x16) → (∀ x15 ∈ x5, ∀ x17 ∈ x5, x15.2 = x17.2 → x15 = x17) → x4.card + x5.card ≤ x6.size + (2 : ℕ) * x7.card := by
  classical
  intro m n E F M C P hC4 hAO hAndJunk hSound hCov hSub hM1 hM2
  by_cases hFle : F.card ≤ P.card
  · have hMle : M.card ≤ F.card := Finset.card_le_card hSub
    omega
  have hPlt : P.card < F.card := by omega
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  have hPne : P.Nonempty := by
    obtain ⟨e, he⟩ := hFne
    obtain ⟨_, p, hp, _, _⟩ := hCov e he
    exact ⟨p, hp⟩
  by_cases hEx : ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact hHasAnd m n E F M C P hPlt hFne hPne hC4 hAO hEx hAndJunk hSound hCov hSub hM1 hM2
  · apply hPureOr m n E F M C P hPlt hFne hPne hC4 hAO _ hSound hCov hSub hM1 hM2
    intro j hj
    have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
      change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ C.gates
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    rcases hAO.1 _ hmem with hand | hor
    · exfalso
      exact hEx ⟨j, hj, hand⟩
    · exact hor
