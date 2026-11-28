import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17818_2
    (hOutAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →
        PEqualNP.TopForm.andPairs (27 : ℕ) x1 = (2 : ℕ) →
        (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (27 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
        have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];
        (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) →
        (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) →
        (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) →
        x1.eval (x9 {x2} {x3}) = Bool.false →
        (63 : ℕ) ≤ x1.size)
    (hOutOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →
        PEqualNP.TopForm.andPairs (27 : ℕ) x1 = (2 : ℕ) →
        (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (27 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
        have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];
        (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) →
        (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) →
        (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) →
        x1.eval (x9 {x2} {x3}) = Bool.false →
        (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →       PEqualNP.TopForm.andPairs (27 : ℕ) x1 = (2 : ℕ) →         have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];         (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) → (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) → x1.eval (x9 {x2} {x3}) = Bool.false → (63 : ℕ) ≤ x1.size := by
  classical
  intro C x2 x3 x4 hMono hRB hAP x8 x9 hInc hQuad hNon hMiss
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
  have hMem0 : (0 : Fin 13) ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide
  have hMem1 : (1 : Fin 13) ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide
  have hWitPt : ∀ (p0 a b : Fin 13), ∃ (p l : Fin 13), p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ (p ≠ a ∨ l ≠ b) ∧ p ≠ p0 := by
    intro p0 a b
    have hlb : b + 1 ≠ b := by revert b; decide
    have h12 : (b + 2 : Fin 13) - (b + 1) = 1 := by revert b; decide
    have hne12 : (b + 2 : Fin 13) ≠ b + 1 := by revert b; decide
    by_cases hlp : b + 1 = p0
    · refine ⟨b + 2, b + 1, ?_, Or.inr hlb, ?_⟩
      · rw [h12]; exact hMem1
      · rw [← hlp]; exact hne12
    · refine ⟨b + 1, b + 1, ?_, Or.inr hlb, hlp⟩
      rw [sub_self]; exact hMem0
  have hWitLn : ∀ (l0 a b : Fin 13), ∃ (p l : Fin 13), p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ (p ≠ a ∨ l ≠ b) ∧ l ≠ l0 := by
    intro l0 a b
    have hlb1 : b + 1 ≠ b := by revert b; decide
    have hlb2 : b + 2 ≠ b := by revert b; decide
    have hne12 : (b + 2 : Fin 13) ≠ b + 1 := by revert b; decide
    by_cases hl1 : b + 1 = l0
    · refine ⟨b + 2, b + 2, ?_, Or.inr hlb2, ?_⟩
      · rw [sub_self]; exact hMem0
      · rw [← hl1]; exact hne12
    · refine ⟨b + 1, b + 1, ?_, Or.inr hlb1, hl1⟩
      rw [sub_self]; exact hMem0
  have hWitAny : ∀ (a b : Fin 13), ∃ (p l : Fin 13), p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ (p ≠ a ∨ l ≠ b) := by
    intro a b
    have hlb : b + 1 ≠ b := by revert b; decide
    refine ⟨b + 1, b + 1, ?_, Or.inr hlb⟩
    rw [sub_self]; exact hMem0
  have hOutGe : 27 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 27 := Nat.lt_of_not_ge hlt
    by_cases h13 : C.output < 13
    · let p0 : Fin 13 := ⟨C.output, h13⟩
      obtain ⟨p, l, hpl, hne, hpne⟩ := hWitPt p0 x2 x3
      have hev := hInc p l hpl hne
      change (C.gates.foldl step (x9 {p} {l})).getD C.output false = true at hev
      have hvl : (x9 {p} {l}).length = 27 := by
        change (((List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ ({l} : Finset (Fin 13)))) ++ [x4]).length = 27
        simp only [List.length_append, List.length_ofFn, List.length_singleton]
      rw [hPref C.gates (x9 {p} {l}) C.output (by omega)] at hev
      change (((List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ ({l} : Finset (Fin 13)))) ++ [x4]).getD C.output false = true at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_append, List.length_ofFn]; omega), List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13), List.getElem?_ofFn] at hev
      simp only [h13, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hev
      exact hpne hev.symm
    · by_cases h26 : C.output < 26
      · let l0 : Fin 13 := ⟨C.output - 13, by omega⟩
        obtain ⟨p, l, hpl, hne, hlne⟩ := hWitLn l0 x2 x3
        have hev := hInc p l hpl hne
        change (C.gates.foldl step (x9 {p} {l})).getD C.output false = true at hev
        have hvl : (x9 {p} {l}).length = 27 := by
          change (((List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ ({l} : Finset (Fin 13)))) ++ [x4]).length = 27
          simp only [List.length_append, List.length_ofFn, List.length_singleton]
        rw [hPref C.gates (x9 {p} {l}) C.output (by omega)] at hev
        change (((List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ ({l} : Finset (Fin 13)))) ++ [x4]).getD C.output false = true at hev
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_append, List.length_ofFn]; exact h26), List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at hev
        simp only [List.length_ofFn] at hev
        rw [List.getElem?_ofFn] at hev
        have hsub : C.output - 13 < 13 := by omega
        simp only [hsub, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hev
        exact hlne hev.symm
      · have hEq26 : C.output = 26 := by omega
        have hAt26 : ∀ S T : Finset (Fin 13), C.eval (x9 S T) = x4 := by
          intro S T
          change (C.gates.foldl step (x9 S T)).getD C.output false = x4
          have hvl : (x9 S T).length = 27 := by
            change (((List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ S)) ++ List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ T)) ++ [x4]).length = 27
            simp only [List.length_append, List.length_ofFn, List.length_singleton]
          rw [hPref C.gates (x9 S T) C.output (by omega), hEq26]
          change (((List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ S)) ++ List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ T)) ++ [x4]).getD 26 false = x4
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_append, List.length_ofFn]; omega)]
          simp only [List.length_append, List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        obtain ⟨p, l, hpl, hne⟩ := hWitAny x2 x3
        have hT := hInc p l hpl hne
        rw [hAt26 {p} {l}] at hT
        rw [hAt26 {x2} {x3}] at hMiss
        rw [hT] at hMiss
        exact Bool.noConfusion hMiss
  have hOutLt : C.output < 27 + C.size := by
    by_contra hge
    have hge : 27 + C.size ≤ C.output := Nat.le_of_not_lt hge
    obtain ⟨p, l, hpl, hne⟩ := hWitAny x2 x3
    have hev := hInc p l hpl hne
    change (C.gates.foldl step (x9 {p} {l})).getD C.output false = true at hev
    have hvl : (x9 {p} {l}).length = 27 := by
      change (((List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn fun (a : Fin 13) => Decidable.decide (a ∈ ({l} : Finset (Fin 13)))) ++ [x4]).length = 27
      simp only [List.length_append, List.length_ofFn, List.length_singleton]
    have hl : (C.gates.foldl step (x9 {p} {l})).length = 27 + C.size := by
      rw [hLen, hvl]
      rfl
    have hdf : (C.gates.foldl step (x9 {p} {l})).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hj : C.output - 27 < C.gates.length := by
    change C.output - 27 < C.size
    omega
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 27) = C.gates[C.output - 27]'hj := by
    change C.gates.getD (C.output - 27) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hj
  have hOp : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 27)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 27)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    rw [hge]
    have hm := (hMono (C.gates[C.output - 27]'hj) (List.getElem_mem hj)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  rcases hOp with hAnd | hOr
  · exact hOutAnd C x2 x3 x4 hMono hRB hAP ⟨hOutGe, hOutLt⟩ hAnd hInc hQuad hNon hMiss
  · exact hOutOr C x2 x3 x4 hMono hRB hAP ⟨hOutGe, hOutLt⟩ hOr hInc hQuad hNon hMiss
