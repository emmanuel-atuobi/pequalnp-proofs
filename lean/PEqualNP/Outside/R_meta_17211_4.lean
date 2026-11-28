import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17211_4
    (hHasOr :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3);
      have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1);
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 x7 : ℕ),
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x4;
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 →
        (∀ x9 ∈ x4.gates, x9.inputs.Nodup) →
        x5 < x4.size ∧ x4.output = (26 : ℕ) + x5 ∧ (26 : ℕ) ≤ x6 ∧ x6 < (26 : ℕ) + x5 ∧ (26 : ℕ) ≤ x7 ∧ x7 < (26 : ℕ) + x5 ∧ x6 ≠ x7 →
        x4.gates[x5]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } →
        ((ga (x6 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ (ga (x7 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (∀ (x14 x15 : Fin (13 : ℕ)), x4.eval (x2 x14 x15) = Decidable.decide (x14 - x15 ∈ x1)) →
        (∀ (x15 : Finset (Fin (13 : ℕ))), x15.card = (4 : ℕ) → (∀ (x17 : Fin (13 : ℕ)), {x18 ∈ x15 | x18 - x17 ∈ x1}.card ≤ (2 : ℕ)) → x4.eval (x3 x15) = Bool.false) →
        (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x1 ∧ (x4.wires (x2 x16 x17)).getD x6 Bool.false = Bool.true ∧ (x4.wires (x2 x16 x17)).getD x7 Bool.false = Bool.false) →
        (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x1 ∧ (x4.wires (x2 x17 x18)).getD x7 Bool.false = Bool.true ∧ (x4.wires (x2 x17 x18)).getD x6 Bool.false = Bool.false) →
        (64 : ℕ) ≤ x4.size)
    (hBothAnd :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3);
      have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1);
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 x7 : ℕ),
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x4;
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 →
        (∀ x9 ∈ x4.gates, x9.inputs.Nodup) →
        x5 < x4.size ∧ x4.output = (26 : ℕ) + x5 ∧ (26 : ℕ) ≤ x6 ∧ x6 < (26 : ℕ) + x5 ∧ (26 : ℕ) ≤ x7 ∧ x7 < (26 : ℕ) + x5 ∧ x6 ≠ x7 →
        x4.gates[x5]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } →
        (ga (x6 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (ga (x7 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x14 x15 : Fin (13 : ℕ)), x4.eval (x2 x14 x15) = Decidable.decide (x14 - x15 ∈ x1)) →
        (∀ (x15 : Finset (Fin (13 : ℕ))), x15.card = (4 : ℕ) → (∀ (x17 : Fin (13 : ℕ)), {x18 ∈ x15 | x18 - x17 ∈ x1}.card ≤ (2 : ℕ)) → x4.eval (x3 x15) = Bool.false) →
        (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x1 ∧ (x4.wires (x2 x16 x17)).getD x6 Bool.false = Bool.true ∧ (x4.wires (x2 x16 x17)).getD x7 Bool.false = Bool.false) →
        (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x1 ∧ (x4.wires (x2 x17 x18)).getD x7 Bool.false = Bool.true ∧ (x4.wires (x2 x17 x18)).getD x6 Bool.false = Bool.false) →
        (64 : ℕ) ≤ x4.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 x7 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 → (∀ x9 ∈ x4.gates, x9.inputs.Nodup) → x4.output = (26 : ℕ) + x5 → x4.gates[x5]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } → (26 : ℕ) ≤ x6 → (26 : ℕ) ≤ x7 → (∀ (x14 x15 : Fin (13 : ℕ)), x4.eval (x2 x14 x15) = Decidable.decide (x14 - x15 ∈ x1)) → (∀ (x15 : Finset (Fin (13 : ℕ))), x15.card = (4 : ℕ) → (∀ (x17 : Fin (13 : ℕ)), {x18 ∈ x15 | x18 - x17 ∈ x1}.card ≤ (2 : ℕ)) → x4.eval (x3 x15) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x1 ∧ (x4.wires (x2 x16 x17)).getD x6 Bool.false = Bool.true ∧ (x4.wires (x2 x16 x17)).getD x7 Bool.false = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x1 ∧ (x4.wires (x2 x17 x18)).getD x7 Bool.false = Bool.true ∧ (x4.wires (x2 x17 x18)).getD x6 Bool.false = Bool.false) → (64 : ℕ) ≤ x4.size := by
  classical
  intro x1 x2 x3 C j a b hAO hNodup hOut hGate haGe hbGe hPairs hQuad hW1 hW2
  have hjLt : j < C.gates.length := by
    by_contra hge
    have hnone : C.gates[j]? = Option.none := List.getElem?_eq_none (Nat.le_of_not_lt hge)
    rw [hnone] at hGate
    cases hGate
  have hjSz : j < C.size := hjLt
  have hGateEq : C.gates[j]'hjLt = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } := by
    rw [List.getElem?_eq_getElem hjLt] at hGate
    exact Option.some.inj hGate
  have hgaJ : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j]'hjLt :=
    List.getD_eq_getElem _ _ hjLt
  have haLt : a < 26 + j := by
    have hmem : a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs := by rw [hgaJ, hGateEq]; simp
    exact hAO.2.1 j hjLt a hmem
  have hbLt : b < 26 + j := by
    have hmem : b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs := by rw [hgaJ, hGateEq]; simp
    exact hAO.2.1 j hjLt b hmem
  have habNe : a ≠ b := by
    have hnd := hNodup (C.gates[j]'hjLt) (List.getElem_mem hjLt)
    rw [hGateEq] at hnd
    simp only [List.nodup_cons, List.mem_singleton] at hnd
    exact hnd.1
  have hOp : ∀ k, k < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro k hk
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k]'hk := by
      change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
      exact List.getD_eq_getElem _ _ hk
    rw [hge]
    exact hAO.1 (C.gates[k]'hk) (List.getElem_mem hk)
  rcases hOp (a - 26) (by omega) with haAnd | haOr
  · rcases hOp (b - 26) (by omega) with hbAnd | hbOr
    · exact hBothAnd C j a b hAO hNodup ⟨hjSz, hOut, haGe, haLt, hbGe, hbLt, habNe⟩ hGate ⟨haAnd, hbAnd⟩ hPairs hQuad hW1 hW2
    · exact hHasOr C j a b hAO hNodup ⟨hjSz, hOut, haGe, haLt, hbGe, hbLt, habNe⟩ hGate (Or.inr hbOr) hPairs hQuad hW1 hW2
  · exact hHasOr C j a b hAO hNodup ⟨hjSz, hOut, haGe, haLt, hbGe, hbLt, habNe⟩ hGate (Or.inl haOr) hPairs hQuad hW1 hW2
