import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17363_2
    (hOutAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 : Fin (13 : ℕ)),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x5 x6 : Fin (13 : ℕ)), (if x2 = Bool.true then x5 ≠ x3 else x6 ≠ x3) → x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 → x1.eval (PEqualNP.GenericRejection.incidenceInput {x5} {x6}) = Bool.true) →
        (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (if x2 = Bool.true then x3 ∉ x6 else x3 ∉ x7) → x1.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true → PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x6 x7 = Bool.true) →
        (59 : ℕ) ≤ x1.size)
    (hOutOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 : Fin (13 : ℕ)),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x5 x6 : Fin (13 : ℕ)), (if x2 = Bool.true then x5 ≠ x3 else x6 ≠ x3) → x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 → x1.eval (PEqualNP.GenericRejection.incidenceInput {x5} {x6}) = Bool.true) →
        (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (if x2 = Bool.true then x3 ∉ x6 else x3 ∉ x7) → x1.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true → PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x6 x7 = Bool.true) →
        (59 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 : Fin (13 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x5 x6 : Fin (13 : ℕ)), (if x2 = Bool.true then x5 ≠ x3 else x6 ≠ x3) → x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 → x1.eval (PEqualNP.GenericRejection.incidenceInput {x5} {x6}) = Bool.true) → (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (if x2 = Bool.true then x3 ∉ x6 else x3 ∉ x7) → x1.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true → PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x6 x7 = Bool.true) → (59 : ℕ) ≤ x1.size := by
  intro C b v0 hM hPos hNeg
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
  have hLen26 : ∀ (A B : Finset (Fin 13)), (PEqualNP.GenericRejection.incidenceInput A B).length = 26 := by
    intro A B
    change (List.ofFn (fun i : Fin 13 => decide (i ∈ A)) ++ List.ofFn (fun j : Fin 13 => decide (j ∈ B))).length = 26
    simp only [List.length_append, List.length_ofFn]
  have hDiag : ∀ a : Fin 13, a ∈ PEqualNP.HeptadCover.singerLines3 a := by decide
  have hAvoid2 : ∀ (x : Fin 13) (w : Fin 26),
      ∃ a : Fin 13, a ≠ x ∧ (PEqualNP.GenericRejection.incidenceInput {a} {a}).getD w.val false = false := by
    decide
  have hDiagTrue : ∀ a : Fin 13, a ≠ v0 →
      C.eval (PEqualNP.GenericRejection.incidenceInput {a} {a}) = true := by
    intro a ha
    have hcond : (if b = Bool.true then a ≠ v0 else a ≠ v0) := by cases b <;> exact ha
    exact hPos a a hcond (hDiag a)
  have hOutLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    obtain ⟨a, ha, _⟩ := hAvoid2 v0 ⟨0, by omega⟩
    have hT := hDiagTrue a ha
    change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {a} {a})).getD C.output false = true at hT
    have hL : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {a} {a})).length = 26 + C.size := by
      rw [hLen, hLen26]
      rfl
    have hF : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {a} {a})).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hF] at hT
    exact Bool.noConfusion hT
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    obtain ⟨a, ha, hgetF⟩ := hAvoid2 v0 ⟨C.output, hlt⟩
    have hT := hDiagTrue a ha
    change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {a} {a})).getD C.output false = true at hT
    rw [hPref C.gates _ C.output (by rw [hLen26]; exact hlt)] at hT
    rw [hgetF] at hT
    exact Bool.noConfusion hT
  have hk_lt : C.output - 26 < C.gates.length := by change C.output - 26 < C.size; omega
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26) = C.gates[C.output - 26]'hk_lt :=
    List.getD_eq_getElem _ _ hk_lt
  rcases (hM (C.gates[C.output - 26]'hk_lt) (List.getElem_mem hk_lt)).1 with hAnd | hOr
  · exact hOutAnd C b v0 hM ⟨hOutGe, hOutLt⟩ (by rw [hge]; exact hAnd) hPos hNeg
  · exact hOutOr C b v0 hM ⟨hOutGe, hOutLt⟩ (by rw [hge]; exact hOr) hPos hNeg
