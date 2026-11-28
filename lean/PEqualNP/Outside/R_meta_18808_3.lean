import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18808_3
    (hOutAnd :
      have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true;
      have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2;
      have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        x4.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 →
        (14 : ℕ) ≤ x4.output ∧ x4.output < (14 : ℕ) + x4.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (14 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ x7 ∈ x4.gates, x7.inputs.Nodup) →
        (∀ (x8 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (7 : ℕ)) (x10 : Fin (7 : ℕ)), x9 ∈ PEqualNP.CircuitLowerBounds.fanoLines x10 ∧ x8 (Fin.castAdd (7 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (7 : ℕ) x10) = Bool.true) →
        (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} →
        (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} →
        ∃ (x11 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)), x2 x11 ∧ x11.leaves ≤ (28 : ℕ) ∧ (∀ (x12 : Fin (14 : ℕ) → Bool), x11.eval x12 = x4.eval (List.ofFn x12)) ∧ (2 : ℕ) ≤ x3 (0 : ℕ) x11 ∧ (2 : ℕ) ≤ x3 (7 : ℕ) x11)
    (hOutOr :
      have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true;
      have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2;
      have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        x4.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 →
        (14 : ℕ) ≤ x4.output ∧ x4.output < (14 : ℕ) + x4.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (14 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ x7 ∈ x4.gates, x7.inputs.Nodup) →
        (∀ (x8 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (7 : ℕ)) (x10 : Fin (7 : ℕ)), x9 ∈ PEqualNP.CircuitLowerBounds.fanoLines x10 ∧ x8 (Fin.castAdd (7 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (7 : ℕ) x10) = Bool.true) →
        (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} →
        (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} →
        ∃ (x11 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)), x2 x11 ∧ x11.leaves ≤ (28 : ℕ) ∧ (∀ (x12 : Fin (14 : ℕ) → Bool), x11.eval x12 = x4.eval (List.ofFn x12)) ∧ (2 : ℕ) ≤ x3 (0 : ℕ) x11 ∧ (2 : ℕ) ≤ x3 (7 : ℕ) x11) :
    have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true; have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2; have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 → (∀ x7 ∈ x4.gates, x7.inputs.Nodup) → (∀ (x8 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (7 : ℕ)) (x10 : Fin (7 : ℕ)), x9 ∈ PEqualNP.CircuitLowerBounds.fanoLines x10 ∧ x8 (Fin.castAdd (7 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (7 : ℕ) x10) = Bool.true) → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x11 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)), x2 x11 ∧ x11.leaves ≤ (28 : ℕ) ∧ (∀ (x12 : Fin (14 : ℕ) → Bool), x11.eval x12 = x4.eval (List.ofFn x12)) ∧ (2 : ℕ) ≤ x3 (0 : ℕ) x11 ∧ (2 : ℕ) ≤ x3 (7 : ℕ) x11 := by
  classical
  intro x1 x2 x3 C hSz hAO hNodup hSpec hDeg0 hDeg7
  have hFano0 : (0 : Fin 7) ∈ PEqualNP.CircuitLowerBounds.fanoLines 0 := by decide
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) init).length =
      init.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro init; simp
    | cons hd tl ih =>
      intro init
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [List.length_append, List.length_singleton]
      omega
  have hfold_pref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (j : ℕ),
      j < init.length →
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) init).getD j false =
      init.getD j false := by
    intro gs
    induction gs with
    | nil => intro init j _; rfl
    | cons hd tl ih =>
      intro init j hj
      simp only [List.foldl_cons]
      rw [ih _ j (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ hj
  have houtGe : 14 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 14 := Nat.lt_of_not_ge hlt
    let idx : Fin 14 := ⟨C.output, hlt⟩
    let f : Fin 14 → Bool := fun i => decide (i = idx)
    have ht : C.eval (List.ofFn f) = true := by
      have h1 := hfold_pref C.gates (List.ofFn f) C.output (by simp only [List.length_ofFn]; exact hlt)
      change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn f)).getD C.output false = true
      rw [h1, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      have heq : (⟨C.output, hlt⟩ : Fin 14) = idx := rfl
      simp only [f, heq, decide_true]
    obtain ⟨p, l, _, hp, hl⟩ := (hSpec f).mp ht
    simp only [f, decide_eq_true_eq] at hp hl
    have hv := congrArg Fin.val (hp.trans hl.symm)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have houtLt : C.output < 14 + C.size := by
    by_contra hge
    have hge : 14 + C.size ≤ C.output := Nat.le_of_not_lt hge
    let f : Fin 14 → Bool := fun _ => true
    have ht : C.eval (List.ofFn f) = true := (hSpec f).mpr ⟨0, 0, hFano0, rfl, rfl⟩
    change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn f)).getD C.output false = true at ht
    have hlen : (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn f)).length = 14 + C.size := by
      rw [hfold_len, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn f)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at ht
    exact Bool.noConfusion ht
  have hk_lt : C.output - 14 < C.gates.length := by change C.output - 14 < C.size; omega
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 14) = C.gates[C.output - 14]'hk_lt :=
    List.getD_eq_getElem _ _ hk_lt
  rcases hAO.1 (C.gates[C.output - 14]'hk_lt) (List.getElem_mem hk_lt) with hAnd | hOr
  · exact hOutAnd C hSz hAO ⟨houtGe, houtLt⟩ (by rw [hge]; exact hAnd) hNodup hSpec hDeg0 hDeg7
  · exact hOutOr C hSz hAO ⟨houtGe, houtLt⟩ (by rw [hge]; exact hOr) hNodup hSpec hDeg0 hDeg7
