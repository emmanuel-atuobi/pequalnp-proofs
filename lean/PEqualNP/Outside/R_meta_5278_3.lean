import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5278_3
    (hOutAnd :
      have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1);
      have x2 : Finset (Finset (Fin (13 : ℕ))) := PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ),
        have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x3;
        have x6 : List Bool → ℕ → Bool := PEqualNP.LowMerge.wireVal x3;
        (PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (38 : ℕ) ≤ x3.size ∧ x3.size < (64 : ℕ) ∧ (26 : ℕ) ≤ x3.output ∧ x3.output < (26 : ℕ) + x3.size ∧ (x5 (x3.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x3 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x3) →
        (∀ x11 ∈ x3.gates, x11.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x11.inputs.getD (1 : ℕ) (0 : ℕ)) →
        (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 →
        (∀ x13 < x3.size, (x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x16 ∈ (x5 x13).inputs, ∃ x18 ∈ x2, x6 (x1 x18) ((26 : ℕ) + x13) ≠ x6 (x1 x18) x16) →
        (∀ x14 ∈ x4, x14 < x3.size ∧ (x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x16 ∈ x2, x6 (x1 x16) ((26 : ℕ) + x14) = Bool.false) →
        (2 : ℕ) * x4.card ≤ x3.size + (1 : ℕ) →
        (∀ (x16 : List Bool), x16.length = (26 : ℕ) → (x3.eval x16 = Bool.true ↔ ∃ x18 ∈ x4, x6 x16 ((26 : ℕ) + x18) = Bool.true)) →
        (∀ (x17 x18 : Fin (13 : ℕ)), x17 ∈ PEqualNP.HeptadCover.singerLines3 x18 → ∃ x20 ∈ x4, x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x17 x18) ((26 : ℕ) + x20) = Bool.true) →
        False)
    (hOutOr :
      have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1);
      have x2 : Finset (Finset (Fin (13 : ℕ))) := PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ),
        have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x3;
        have x6 : List Bool → ℕ → Bool := PEqualNP.LowMerge.wireVal x3;
        (PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (38 : ℕ) ≤ x3.size ∧ x3.size < (64 : ℕ) ∧ (26 : ℕ) ≤ x3.output ∧ x3.output < (26 : ℕ) + x3.size ∧ (x5 (x3.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x3 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x3) →
        (∀ x11 ∈ x3.gates, x11.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x11.inputs.getD (1 : ℕ) (0 : ℕ)) →
        (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 →
        (∀ x13 < x3.size, (x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x16 ∈ (x5 x13).inputs, ∃ x18 ∈ x2, x6 (x1 x18) ((26 : ℕ) + x13) ≠ x6 (x1 x18) x16) →
        (∀ x14 ∈ x4, x14 < x3.size ∧ (x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x16 ∈ x2, x6 (x1 x16) ((26 : ℕ) + x14) = Bool.false) →
        (2 : ℕ) * x4.card ≤ x3.size + (1 : ℕ) →
        (∀ (x16 : List Bool), x16.length = (26 : ℕ) → (x3.eval x16 = Bool.true ↔ ∃ x18 ∈ x4, x6 x16 ((26 : ℕ) + x18) = Bool.true)) →
        (∀ (x17 x18 : Fin (13 : ℕ)), x17 ∈ PEqualNP.HeptadCover.singerLines3 x18 → ∃ x20 ∈ x4, x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x17 x18) ((26 : ℕ) + x20) = Bool.true) →
        False) :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : Finset (Finset (Fin (13 : ℕ))) := PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ),   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x3;   have x6 : List Bool → ℕ → Bool := PEqualNP.LowMerge.wireVal x3;   PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (38 : ℕ) ≤ x3.size → x3.size < (64 : ℕ) → (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x3 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x3 → (∀ x11 ∈ x3.gates, x11.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x11.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 → (∀ x13 < x3.size, (x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x16 ∈ (x5 x13).inputs, ∃ x18 ∈ x2, x6 (x1 x18) ((26 : ℕ) + x13) ≠ x6 (x1 x18) x16) → (∀ x14 ∈ x4, x14 < x3.size ∧ (x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x16 ∈ x2, x6 (x1 x16) ((26 : ℕ) + x14) = Bool.false) → (2 : ℕ) * x4.card ≤ x3.size + (1 : ℕ) → (∀ (x16 : List Bool), x16.length = (26 : ℕ) → (x3.eval x16 = Bool.true ↔ ∃ x18 ∈ x4, x6 x16 ((26 : ℕ) + x18) = Bool.true)) → (∀ (x17 x18 : Fin (13 : ℕ)), x17 ∈ PEqualNP.HeptadCover.singerLines3 x18 → ∃ x20 ∈ x4, x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x17 x18) ((26 : ℕ) + x20) = Bool.true) → False := by
  intro x1 x2 C K gate wire hAO hMin hMax hCounts hDist hPairs hAct hSil hBud hEval hAll
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
  have hPLlen : ∀ p l : Fin 13, (PEqualNP.LowMerge.pointLineInput 13 13 p l).length = 26 := by
    intro p l
    change (List.ofFn (fun q : Fin 13 => decide (q = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))).length = 26
    simp only [List.length_append, List.length_ofFn]
  have hIncEval : ∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l →
      C.eval (PEqualNP.LowMerge.pointLineInput 13 13 p l) = true := by
    intro p l hpl
    exact (hEval (PEqualNP.LowMerge.pointLineInput 13 13 p l) (hPLlen p l)).mpr (hAll p l hpl)
  have hDiag : ∀ a : Fin 13, a ∈ PEqualNP.HeptadCover.singerLines3 a := by
    intro a; revert a; decide
  have hNeNext : ∀ a : Fin 13, a + 1 ≠ a := by
    intro a; revert a; decide
  have hOutLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hev : (C.gates.foldl step (PEqualNP.LowMerge.pointLineInput 13 13 0 0)).getD C.output false = true :=
      hIncEval 0 0 (hDiag 0)
    have hl : (C.gates.foldl step (PEqualNP.LowMerge.pointLineInput 13 13 0 0)).length = 26 + C.size := by
      rw [hLen, hPLlen]
      rfl
    have hdf : (C.gates.foldl step (PEqualNP.LowMerge.pointLineInput 13 13 0 0)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    by_cases h13 : C.output < 13
    · let p0 : Fin 13 := ⟨C.output, h13⟩
      have hev : (C.gates.foldl step (PEqualNP.LowMerge.pointLineInput 13 13 (p0 + 1) (p0 + 1))).getD C.output false = true :=
        hIncEval (p0 + 1) (p0 + 1) (hDiag (p0 + 1))
      rw [hPref C.gates _ C.output (by rw [hPLlen]; exact hlt)] at hev
      change (List.ofFn (fun q : Fin 13 => decide (q = p0 + 1)) ++ List.ofFn (fun v : Fin 13 => decide (v = p0 + 1))).getD C.output false = true at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13), List.getElem?_ofFn] at hev
      simp only [h13, ↓reduceDIte, Option.getD_some, decide_eq_true_eq] at hev
      exact hNeNext p0 hev.symm
    · let l0 : Fin 13 := ⟨C.output - 13, by omega⟩
      have hev : (C.gates.foldl step (PEqualNP.LowMerge.pointLineInput 13 13 (l0 + 1) (l0 + 1))).getD C.output false = true :=
        hIncEval (l0 + 1) (l0 + 1) (hDiag (l0 + 1))
      rw [hPref C.gates _ C.output (by rw [hPLlen]; exact hlt)] at hev
      change (List.ofFn (fun q : Fin 13 => decide (q = l0 + 1)) ++ List.ofFn (fun v : Fin 13 => decide (v = l0 + 1))).getD C.output false = true at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at hev
      simp only [List.length_ofFn] at hev
      rw [List.getElem?_ofFn] at hev
      have hsub : C.output - 13 < 13 := by omega
      simp only [hsub, ↓reduceDIte, Option.getD_some, decide_eq_true_eq] at hev
      exact hNeNext l0 hev.symm
  have hj : C.output - 26 < C.gates.length := by
    change C.output - 26 < C.size
    omega
  have hge : gate (C.output - 26) = C.gates[C.output - 26]'hj := by
    change C.gates.getD (C.output - 26) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hj
  have hOp : (gate (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (gate (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    rw [hge]
    exact hAO.1 (C.gates[C.output - 26]'hj) (List.getElem_mem hj)
  rcases hOp with hAnd | hOr
  · exact hOutAnd C K ⟨hAO, hMin, hMax, hOutGe, hOutLt, hAnd, hCounts.1, hCounts.2⟩ hDist hPairs hAct hSil hBud hEval hAll
  · exact hOutOr C K ⟨hAO, hMin, hMax, hOutGe, hOutLt, hOr, hCounts.1, hCounts.2⟩ hDist hPairs hAct hSil hBud hEval hAll
