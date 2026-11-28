import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18627_3
    (hOutAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (7 : ℕ)),
        x1.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
        (14 : ℕ) ≤ x1.output ∧ x1.output < (14 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (14 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ x6 ∈ x1.gates, x6.inputs.Nodup) →
        PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x1 →
        x2 ∈ PEqualNP.CircuitLowerBounds.fanoLines x3 →
        (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2} →
        (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x3} →
        (∃ x11 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (2 : ℕ) ≤ List.count ((14 : ℕ) + x11) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)) →
        False)
    (hOutOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (7 : ℕ)),
        x1.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
        (14 : ℕ) ≤ x1.output ∧ x1.output < (14 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (14 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ x6 ∈ x1.gates, x6.inputs.Nodup) →
        PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x1 →
        x2 ∈ PEqualNP.CircuitLowerBounds.fanoLines x3 →
        (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2} →
        (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x3} →
        (∃ x11 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (2 : ℕ) ≤ List.count ((14 : ℕ) + x11) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (7 : ℕ)), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 ∈ x1.gates, x6.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x1 → x2 ∈ PEqualNP.CircuitLowerBounds.fanoLines x3 → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2} → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x3} → (∃ x11 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (2 : ℕ) ≤ List.count ((14 : ℕ) + x11) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)) → False := by
  intro C p l hSz hAO hNodup hComp hInc hDegP hDegL hSharedAnd
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
  have hLen14 : ∀ (A B : Finset (Fin 7)), (PEqualNP.GenericRejection.incidenceInput A B).length = 14 := by
    intro A B
    change (List.ofFn (fun i : Fin 7 => decide (i ∈ A)) ++ List.ofFn (fun j : Fin 7 => decide (j ∈ B))).length = 14
    simp only [List.length_append, List.length_ofFn]
  have houtLt : C.output < 14 + C.size := by
    by_contra hge
    have hge : 14 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hT := hComp {(0 : Fin 7)} {(0 : Fin 7)}
    have hFun : PEqualNP.GenericRejection.incidenceFun PEqualNP.CircuitLowerBounds.fanoLines ({(0 : Fin 7)} : Finset (Fin 7)) {(0 : Fin 7)} = true := by decide
    rw [hFun] at hT
    change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 7)} : Finset (Fin 7)) {(0 : Fin 7)})).getD C.output false = true at hT
    have hL : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 7)} : Finset (Fin 7)) {(0 : Fin 7)})).length = 14 + C.size := by
      rw [hLen, hLen14]
      rfl
    have hF : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 7)} : Finset (Fin 7)) {(0 : Fin 7)})).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hF] at hT
    exact Bool.noConfusion hT
  have houtGe : 14 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 14 := Nat.lt_of_not_ge hlt
    by_cases h7 : C.output < 7
    · let p0 : Fin 7 := ⟨C.output, h7⟩
      have hT := hComp {p0} ∅
      have hFun : ∀ q : Fin 7, PEqualNP.GenericRejection.incidenceFun PEqualNP.CircuitLowerBounds.fanoLines ({q} : Finset (Fin 7)) ∅ = false := by decide
      rw [hFun p0] at hT
      change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({p0} : Finset (Fin 7)) ∅)).getD C.output false = false at hT
      rw [hPref C.gates _ C.output (by rw [hLen14]; exact hlt)] at hT
      have hIn : ∀ q : Fin 7, (PEqualNP.GenericRejection.incidenceInput ({q} : Finset (Fin 7)) (∅ : Finset (Fin 7))).getD q.val false = true := by decide
      have h1 := hIn p0
      change (PEqualNP.GenericRejection.incidenceInput ({p0} : Finset (Fin 7)) (∅ : Finset (Fin 7))).getD C.output false = true at h1
      rw [h1] at hT
      exact Bool.noConfusion hT
    · let l0 : Fin 7 := ⟨C.output - 7, by omega⟩
      have hT := hComp ∅ {l0}
      have hFun : ∀ q : Fin 7, PEqualNP.GenericRejection.incidenceFun PEqualNP.CircuitLowerBounds.fanoLines ∅ ({q} : Finset (Fin 7)) = false := by decide
      rw [hFun l0] at hT
      change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 7)) ({l0} : Finset (Fin 7)))).getD C.output false = false at hT
      rw [hPref C.gates _ C.output (by rw [hLen14]; exact hlt)] at hT
      have hIn : ∀ q : Fin 7, (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 7)) ({q} : Finset (Fin 7))).getD (7 + q.val) false = true := by decide
      have h1 := hIn l0
      have hEq : 7 + l0.val = C.output := by show 7 + (C.output - 7) = C.output; omega
      rw [hEq] at h1
      rw [h1] at hT
      exact Bool.noConfusion hT
  have hk_lt : C.output - 14 < C.gates.length := by change C.output - 14 < C.size; omega
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 14) = C.gates[C.output - 14]'hk_lt :=
    List.getD_eq_getElem _ _ hk_lt
  rcases hAO.1 (C.gates[C.output - 14]'hk_lt) (List.getElem_mem hk_lt) with hAnd | hOr
  · exact hOutAnd C p l hSz hAO ⟨houtGe, houtLt⟩ (by rw [hge]; exact hAnd) hNodup hComp hInc hDegP hDegL hSharedAnd
  · exact hOutOr C p l hSz hAO ⟨houtGe, houtLt⟩ (by rw [hge]; exact hOr) hNodup hComp hInc hDegP hDegL hSharedAnd
