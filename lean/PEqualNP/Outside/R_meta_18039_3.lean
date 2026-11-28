import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18039_3
    (hOutAnd :
      have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true;
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (26 : ℕ)),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        (26 : ℕ) ≤ x2.output ∧ x2.output < (26 : ℕ) + x2.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (x3 = (1 : Fin (26 : ℕ)) ∨ x3 = (2 : Fin (26 : ℕ))) →
        (∀ (x6 : Fin (26 : ℕ) → Bool), x6 (0 : Fin (26 : ℕ)) = Bool.false → x6 (13 : Fin (26 : ℕ)) = Bool.false → x6 x3 = Bool.false → (x2.eval (List.ofFn x6) = Bool.true ↔ x1 x6)) →
        (if x3 = (1 : Fin (26 : ℕ)) then (52 : ℕ) else (51 : ℕ)) ≤ x2.size)
    (hOutOr :
      have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true;
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (26 : ℕ)),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        (26 : ℕ) ≤ x2.output ∧ x2.output < (26 : ℕ) + x2.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (x3 = (1 : Fin (26 : ℕ)) ∨ x3 = (2 : Fin (26 : ℕ))) →
        (∀ (x6 : Fin (26 : ℕ) → Bool), x6 (0 : Fin (26 : ℕ)) = Bool.false → x6 (13 : Fin (26 : ℕ)) = Bool.false → x6 x3 = Bool.false → (x2.eval (List.ofFn x6) = Bool.true ↔ x1 x6)) →
        (if x3 = (1 : Fin (26 : ℕ)) then (52 : ℕ) else (51 : ℕ)) ≤ x2.size) :
    have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x2 → x3 = (1 : Fin (26 : ℕ)) ∨ x3 = (2 : Fin (26 : ℕ)) → (∀ (x6 : Fin (26 : ℕ) → Bool), x6 (0 : Fin (26 : ℕ)) = Bool.false → x6 (13 : Fin (26 : ℕ)) = Bool.false → x6 x3 = Bool.false → (x2.eval (List.ofFn x6) = Bool.true ↔ x1 x6)) → (if x3 = (1 : Fin (26 : ℕ)) then (52 : ℕ) else (51 : ℕ)) ≤ x2.size := by
  intro x1 C v hM hv hSpec
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool),
      (gs.foldl step s).length = s.length + gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro s; simp
    | append_singleton gs g ih =>
      intro s
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, step, List.length_append, List.length_singleton]
      rw [ih s]
      omega
  have hPref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool) (i : ℕ),
      i < s.length → (gs.foldl step s).getD i false = s.getD i false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro s i _; rfl
    | append_singleton gs g ih =>
      intro s i hi
      have hl : (gs.foldl step s).length = s.length + gs.length := hLen gs s
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((gs.foldl step s) ++ [_]).getD i false = s.getD i false
      rw [List.getD_append _ _ _ _ (by omega)]
      exact ih s i hi
  let f3 : Fin 26 → Bool := fun i => decide (i = 3 ∨ i = 16)
  have hf3_0 : f3 0 = false := by decide
  have hf3_13 : f3 13 = false := by decide
  have hf3_v : f3 v = false := by
    rcases hv with rfl | rfl <;> decide
  have hf3_x1 : x1 f3 := ⟨3, 3, Or.inl rfl, by decide, by decide⟩
  have hCf3 : C.eval (List.ofFn f3) = true := (hSpec f3 hf3_0 hf3_13 hf3_v).mpr hf3_x1
  have hOutLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hev : (C.gates.foldl step (List.ofFn f3)).getD C.output false = true := hCf3
    have hl : (C.gates.foldl step (List.ofFn f3)).length = 26 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn f3)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    let w0 : Fin 26 := ⟨C.output, hlt⟩
    by_cases hBad : w0 = 0 ∨ w0 = 13 ∨ w0 = v
    · have hev : (C.gates.foldl step (List.ofFn f3)).getD C.output false = true := hCf3
      rw [hPref C.gates (List.ofFn f3) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
      simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
      change f3 w0 = true at hev
      rcases hBad with h0 | h13 | hv0
      · rw [h0, hf3_0] at hev; exact Bool.noConfusion hev
      · rw [h13, hf3_13] at hev; exact Bool.noConfusion hev
      · rw [hv0, hf3_v] at hev; exact Bool.noConfusion hev
    · let fS : Fin 26 → Bool := fun i => decide (i = w0)
      have hfS_0 : fS 0 = false := decide_eq_false (fun h => hBad (Or.inl h.symm))
      have hfS_13 : fS 13 = false := decide_eq_false (fun h => hBad (Or.inr (Or.inl h.symm)))
      have hfS_v : fS v = false := decide_eq_false (fun h => hBad (Or.inr (Or.inr h.symm)))
      have hfS_nx1 : ¬x1 fS := by
        rintro ⟨p, l, _, hp, hl⟩
        have hp' : Fin.castAdd 13 p = w0 := of_decide_eq_true hp
        have hl' : Fin.natAdd 13 l = w0 := of_decide_eq_true hl
        have hval := congrArg Fin.val (hp'.trans hl'.symm)
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      have hCfS : C.eval (List.ofFn fS) = false := by
        cases h : C.eval (List.ofFn fS)
        · rfl
        · exact False.elim (hfS_nx1 ((hSpec fS hfS_0 hfS_13 hfS_v).mp h))
      have hev : (C.gates.foldl step (List.ofFn fS)).getD C.output false = false := hCfS
      rw [hPref C.gates (List.ofFn fS) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
      simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
      change decide (w0 = w0) = false at hev
      rw [decide_eq_true rfl] at hev
      exact Bool.noConfusion hev
  have hk_lt : C.output - 26 < C.gates.length := by change C.output - 26 < C.size; omega
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26) = C.gates[C.output - 26]'hk_lt :=
    List.getD_eq_getElem _ _ hk_lt
  rcases (hM (C.gates[C.output - 26]'hk_lt) (List.getElem_mem hk_lt)).1 with hAnd | hOr
  · exact hOutAnd C v hM ⟨hOutGe, hOutLt⟩ (by rw [hga]; exact hAnd) hv hSpec
  · exact hOutOr C v hM ⟨hOutGe, hOutLt⟩ (by rw [hga]; exact hOr) hv hSpec
