import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8045_4
    (hSingleOutGate :
      ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)) (g0 : Fin x1.size),
        x1.WellFormed →
        x1.outVars = ∅ →
        x1.outGates = {g0} →
        (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → x1.eval {x6 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x7 : Fin (26 : ℕ)) => !Decidable.decide (x7 = Fin.castAdd (13 : ℕ) x3 ∨ x7 = Fin.natAdd (13 : ℕ) x4)) x6 = Bool.true} = Bool.false) →
        (∀ (x4 x5 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse (fun (x6 : Fin (13 : ℕ)) => {x6, x6 + (1 : Fin (13 : ℕ)), x6 + (3 : Fin (13 : ℕ)), x6 + (9 : Fin (13 : ℕ))}) x4 x5 → PEqualNP.GenericRejection.IsGeneric (fun (x7 : Fin (13 : ℕ)) => {x7, x7 + (1 : Fin (13 : ℕ)), x7 + (3 : Fin (13 : ℕ)), x7 + (9 : Fin (13 : ℕ))}) (3 : ℕ) x4 x5 → x1.eval {x8 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x9 : Fin (26 : ℕ)) => !Decidable.decide ((∃ x10 ∈ x4, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ x10 ∈ x5, x9 = Fin.natAdd (13 : ℕ) x10)) x8 = Bool.true} = Bool.true) →
        (51 : ℕ) ≤ x1.size)
    (hMultiOutGates :
      ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),
        x1.WellFormed →
        x1.outVars = ∅ →
        (2 : ℕ) ≤ x1.outGates.card →
        (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → x1.eval {x6 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x7 : Fin (26 : ℕ)) => !Decidable.decide (x7 = Fin.castAdd (13 : ℕ) x3 ∨ x7 = Fin.natAdd (13 : ℕ) x4)) x6 = Bool.true} = Bool.false) →
        (∀ (x4 x5 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse (fun (x6 : Fin (13 : ℕ)) => {x6, x6 + (1 : Fin (13 : ℕ)), x6 + (3 : Fin (13 : ℕ)), x6 + (9 : Fin (13 : ℕ))}) x4 x5 → PEqualNP.GenericRejection.IsGeneric (fun (x7 : Fin (13 : ℕ)) => {x7, x7 + (1 : Fin (13 : ℕ)), x7 + (3 : Fin (13 : ℕ)), x7 + (9 : Fin (13 : ℕ))}) (3 : ℕ) x4 x5 → x1.eval {x8 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x9 : Fin (26 : ℕ)) => !Decidable.decide ((∃ x10 ∈ x4, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ x10 ∈ x5, x9 = Fin.natAdd (13 : ℕ) x10)) x8 = Bool.true} = Bool.true) →
        (51 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)), x1.WellFormed → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → x1.eval {x6 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x7 : Fin (26 : ℕ)) => !Decidable.decide (x7 = Fin.castAdd (13 : ℕ) x3 ∨ x7 = Fin.natAdd (13 : ℕ) x4)) x6 = Bool.true} = Bool.false) → (∀ (x4 x5 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse (fun (x6 : Fin (13 : ℕ)) => {x6, x6 + (1 : Fin (13 : ℕ)), x6 + (3 : Fin (13 : ℕ)), x6 + (9 : Fin (13 : ℕ))}) x4 x5 → PEqualNP.GenericRejection.IsGeneric (fun (x7 : Fin (13 : ℕ)) => {x7, x7 + (1 : Fin (13 : ℕ)), x7 + (3 : Fin (13 : ℕ)), x7 + (9 : Fin (13 : ℕ))}) (3 : ℕ) x4 x5 → x1.eval {x8 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x9 : Fin (26 : ℕ)) => !Decidable.decide ((∃ x10 ∈ x4, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ x10 ∈ x5, x9 = Fin.natAdd (13 : ℕ) x10)) x8 = Bool.true} = Bool.true) → (51 : ℕ) ≤ x1.size := by
  intro C hWF hInc hGen
  have hAvoid : ∀ v : Fin 27,
      Fin.cases Bool.true (fun (x7 : Fin 26) => !Decidable.decide (x7 = Fin.castAdd 13 (0 : Fin 13) ∨ x7 = Fin.natAdd 13 (0 : Fin 13))) v = Bool.true ∨
      Fin.cases Bool.true (fun (x7 : Fin 26) => !Decidable.decide (x7 = Fin.castAdd 13 (1 : Fin 13) ∨ x7 = Fin.natAdd 13 (1 : Fin 13))) v = Bool.true := by
    decide
  have hOutVars : C.outVars = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    rcases hAvoid v with h0 | h1
    · have hF := hInc 0 0 (Or.inl rfl)
      have hEv : C.eval {x6 : Fin 27 | Fin.cases Bool.true (fun (x7 : Fin 26) => !Decidable.decide (x7 = Fin.castAdd 13 (0 : Fin 13) ∨ x7 = Fin.natAdd 13 (0 : Fin 13))) x6 = Bool.true} = Bool.true := by
        change decide ((∃ w ∈ C.outVars, w ∈ _) ∨ _) = true
        exact decide_eq_true (Or.inl ⟨v, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩)
      rw [hEv] at hF
      exact Bool.noConfusion hF
    · have hF := hInc 1 1 (Or.inl rfl)
      have hEv : C.eval {x6 : Fin 27 | Fin.cases Bool.true (fun (x7 : Fin 26) => !Decidable.decide (x7 = Fin.castAdd 13 (1 : Fin 13) ∨ x7 = Fin.natAdd 13 (1 : Fin 13))) x6 = Bool.true} = Bool.true := by
        change decide ((∃ w ∈ C.outVars, w ∈ _) ∨ _) = true
        exact decide_eq_true (Or.inl ⟨v, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩)
      rw [hEv] at hF
      exact Bool.noConfusion hF
  have hOutGatesNe : C.outGates.Nonempty := by
    let A0 : Finset (Fin 13) := {(0 : Fin 13), 1, 2, 5}
    let B0 : Finset (Fin 13) := {(3 : Fin 13), 7, 8}
    have hMF : PEqualNP.GenericRejection.IsMaximalFalse (fun (x6 : Fin 13) => {x6, x6 + (1 : Fin 13), x6 + (3 : Fin 13), x6 + (9 : Fin 13)}) A0 B0 := by decide
    have hG : PEqualNP.GenericRejection.IsGeneric (fun (x7 : Fin 13) => {x7, x7 + (1 : Fin 13), x7 + (3 : Fin 13), x7 + (9 : Fin 13)}) 3 A0 B0 := by decide
    have hT := hGen A0 B0 hMF hG
    change decide ((∃ v ∈ C.outVars, v ∈ _) ∨ ∃ j ∈ C.outGates, C.gateVal _ j = true) = true at hT
    rcases of_decide_eq_true hT with ⟨v, hv, _⟩ | ⟨j, hj, _⟩
    · rw [hOutVars] at hv
      exact False.elim (Finset.notMem_empty v hv)
    · exact ⟨j, hj⟩
  have hCardPos : 1 ≤ C.outGates.card := Finset.card_pos.mpr hOutGatesNe
  rcases Nat.eq_or_lt_of_le hCardPos with hCard1 | hCardGe2
  · obtain ⟨g0, hg0⟩ := Finset.card_eq_one.mp hCard1.symm
    exact hSingleOutGate C g0 hWF hOutVars hg0 hInc hGen
  · exact hMultiOutGates C hWF hOutVars hCardGe2 hInc hGen
