import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4147_4
    (hOutAnd :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x1 x3 ∧ ∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x4 → x3.eval (x2 x4) = Bool.false;
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6;
      have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ (x6 : ℕ), x4 x5 x6) ∧ ∀ (x6 : ℕ), x4 x5 x6 → (∃ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x8 ∧ (x5.wires (x2 x8)).getD ((26 : ℕ) + x6) Bool.false = Bool.true) ∧ (2 : ℕ) ≤ {x8 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x8.1} {x8.2}) = Bool.false}.card;
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),
        (x3 x6 ∧ x5 x6 ∧ (26 : ℕ) ≤ x6.output ∧ x6.output < (26 : ℕ) + x6.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 (x6.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (64 : ℕ) ≤ x6.size)
    (hOutOr :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x1 x3 ∧ ∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x4 → x3.eval (x2 x4) = Bool.false;
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6;
      have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ (x6 : ℕ), x4 x5 x6) ∧ ∀ (x6 : ℕ), x4 x5 x6 → (∃ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x8 ∧ (x5.wires (x2 x8)).getD ((26 : ℕ) + x6) Bool.false = Bool.true) ∧ (2 : ℕ) ≤ {x8 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x8.1} {x8.2}) = Bool.false}.card;
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),
        (x3 x6 ∧ x5 x6 ∧ (26 : ℕ) ≤ x6.output ∧ x6.output < (26 : ℕ) + x6.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 (x6.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (64 : ℕ) ≤ x6.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x1 x3 ∧ ∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x4 → x3.eval (x2 x4) = Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ (x6 : ℕ), x4 x5 x6) ∧ ∀ (x6 : ℕ), x4 x5 x6 → (∃ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x8 ∧ (x5.wires (x2 x8)).getD ((26 : ℕ) + x6) Bool.false = Bool.true) ∧ (2 : ℕ) ≤ {x8 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x8.1} {x8.2}) = Bool.false}.card; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x5 x6 → (64 : ℕ) ≤ x6.size := by
  intro x1 x2 x3 x4 x5 C h3 h5
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
  have hIIlen : ∀ X Y : Finset (Fin 13), (PEqualNP.GenericRejection.incidenceInput X Y).length = 26 := by
    intro X Y
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y))).length = 26
    simp only [List.length_append, List.length_ofFn]
  have hDiag : ∀ a : Fin 13, a ∈ x1 a := by
    intro a; revert a; decide
  have hNeNext : ∀ a : Fin 13, a + 1 ≠ a := by
    intro a; revert a; decide
  have hRight := h3.2.2.1
  have hOutLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    let inp := PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}
    have hev : (C.gates.foldl step inp).getD C.output false = true :=
      hRight 0 0 (hDiag 0)
    have hl : (C.gates.foldl step inp).length = 26 + C.size := by
      rw [hLen, hIIlen]
      rfl
    have hdf : (C.gates.foldl step inp).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    by_cases h13 : C.output < 13
    · let p0 : Fin 13 := ⟨C.output, h13⟩
      have hev : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p0 + 1} {p0 + 1})).getD C.output false = true :=
        hRight (p0 + 1) (p0 + 1) (hDiag (p0 + 1))
      rw [hPref C.gates _ C.output (by rw [hIIlen]; exact hlt)] at hev
      change (List.ofFn (fun p : Fin 13 => decide (p ∈ ({p0 + 1} : Finset (Fin 13)))) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ ({p0 + 1} : Finset (Fin 13))))).getD C.output false = true at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13), List.getElem?_ofFn] at hev
      simp only [h13, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hev
      exact hNeNext p0 hev.symm
    · let l0 : Fin 13 := ⟨C.output - 13, by omega⟩
      have hev : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {l0 + 1} {l0 + 1})).getD C.output false = true :=
        hRight (l0 + 1) (l0 + 1) (hDiag (l0 + 1))
      rw [hPref C.gates _ C.output (by rw [hIIlen]; exact hlt)] at hev
      change (List.ofFn (fun p : Fin 13 => decide (p ∈ ({l0 + 1} : Finset (Fin 13)))) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ ({l0 + 1} : Finset (Fin 13))))).getD C.output false = true at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at hev
      simp only [List.length_ofFn] at hev
      rw [List.getElem?_ofFn] at hev
      have hsub : C.output - 13 < 13 := by omega
      simp only [hsub, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hev
      exact hNeNext l0 hev.symm
  have hj : C.output - 26 < C.gates.length := by
    change C.output - 26 < C.size
    omega
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26) = C.gates[C.output - 26]'hj := by
    change C.gates.getD (C.output - 26) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hj
  have hOp : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    rw [hge]
    have hm := (h3.1 (C.gates[C.output - 26]'hj) (List.getElem_mem hj)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  rcases hOp with hAnd | hOr
  · exact hOutAnd C ⟨h3, h5, hOutGe, hOutLt, hAnd⟩
  · exact hOutOr C ⟨h3, h5, hOutGe, hOutLt, hOr⟩
