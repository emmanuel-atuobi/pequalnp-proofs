import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7911_1
    (hOutAnd :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        (26 : ℕ) ≤ x2.output ∧ x2.output < (26 : ℕ) + x2.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) →
        (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) →
        ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))), (∀ x12 ∈ x10, ∀ x14 ∈ x11, ¬x1 x12 x14) ∧ (∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x10 | x1 x13 x12}.card ≤ (2 : ℕ)) ∧ (∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x1 x12 x13}.card ≤ (2 : ℕ)) ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ x13 ∈ x10, x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true) → (∀ x14 ∈ x11, x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x12 = Bool.true)
    (hOutOr :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        (26 : ℕ) ≤ x2.output ∧ x2.output < (26 : ℕ) + x2.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) →
        (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) →
        ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))), (∀ x12 ∈ x10, ∀ x14 ∈ x11, ¬x1 x12 x14) ∧ (∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x10 | x1 x13 x12}.card ≤ (2 : ℕ)) ∧ (∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x1 x12 x13}.card ≤ (2 : ℕ)) ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ x13 ∈ x10, x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true) → (∀ x14 ∈ x11, x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x12 = Bool.true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) → (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) → ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))), (∀ x12 ∈ x10, ∀ x14 ∈ x11, ¬x1 x12 x14) ∧ (∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x10 | x1 x13 x12}.card ≤ (2 : ℕ)) ∧ (∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x1 x12 x13}.card ≤ (2 : ℕ)) ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ x13 ∈ x10, x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true) → (∀ x14 ∈ x11, x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x12 = Bool.true := by
  intro x1 C hM hSz hN1R hN1L h2R h2L hPos
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool),
      (gs.foldl step v).length = v.length + gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro v; simp
    | append_singleton gs g ih =>
      intro v
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, step, List.length_append, List.length_singleton]
      rw [ih v]
      omega
  have hPref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool) (i : ℕ),
      i < v.length → (gs.foldl step v).getD i false = v.getD i false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro v i _; rfl
    | append_singleton gs g ih =>
      intro v i hi
      have hl : (gs.foldl step v).length = v.length + gs.length := hLen gs v
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((gs.foldl step v) ++ [_]).getD i false = v.getD i false
      rw [List.getD_append _ _ _ _ (by omega)]
      exact ih v i hi
  have hOutLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    let f0 : Fin 26 → Bool := fun x12 => Decidable.decide (x12 = Fin.castAdd 13 (0 : Fin 13) ∨ x12 = Fin.natAdd 13 (0 : Fin 13))
    have hT : (C.gates.foldl step (List.ofFn f0)).getD C.output false = true := hPos 0 0 (Or.inl rfl)
    have hl : (C.gates.foldl step (List.ofFn f0)).length = 26 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hF : (C.gates.foldl step (List.ofFn f0)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hF] at hT
    exact Bool.noConfusion hT
  have hAvoid : ∀ w : Fin 26, ∃ a : Fin 13,
      w ≠ Fin.castAdd 13 a ∧ w ≠ Fin.natAdd 13 a := by
    decide
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    obtain ⟨a, ha1, ha2⟩ := hAvoid ⟨C.output, hlt⟩
    let fa : Fin 26 → Bool := fun x12 => Decidable.decide (x12 = Fin.castAdd 13 a ∨ x12 = Fin.natAdd 13 a)
    have hT : (C.gates.foldl step (List.ofFn fa)).getD C.output false = true := hPos a a (Or.inl rfl)
    rw [hPref C.gates (List.ofFn fa) C.output (by rw [List.length_ofFn]; exact hlt)] at hT
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hT
    simp only [hlt, ↓reduceDIte, Option.getD_some] at hT
    rcases of_decide_eq_true hT with h1 | h2
    · exact ha1 h1
    · exact ha2 h2
  have hk_lt : C.output - 26 < C.gates.length := by change C.output - 26 < C.size; omega
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26) = C.gates[C.output - 26]'hk_lt :=
    List.getD_eq_getElem _ _ hk_lt
  rcases (hM (C.gates[C.output - 26]'hk_lt) (List.getElem_mem hk_lt)).1 with hAnd | hOr
  · exact hOutAnd C hM hSz ⟨hOutGe, hOutLt⟩ (by rw [hga]; exact hAnd) hN1R hN1L h2R h2L hPos
  · exact hOutOr C hM hSz ⟨hOutGe, hOutLt⟩ (by rw [hga]; exact hOr) hN1R hN1L h2R h2L hPos
