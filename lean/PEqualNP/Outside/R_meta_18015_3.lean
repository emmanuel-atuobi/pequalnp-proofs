import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18015_3
    (hOutAnd :
      ∀ (x1 : Fin (11 : ℕ)) (x2 : Fin (10 : ℕ)) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit),
        ↑x1 < (4 : ℕ) →
        PEqualNP.TopForm.IsAO2 (9 : ℕ) x3 →
        PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x3.size) x4 →
        x3.size + x4.size ≤ (17 : ℕ) →
        (9 : ℕ) ≤ x3.output →
        x3.output < (9 : ℕ) + x3.size →
        (10 : ℕ) + x3.size ≤ x4.output ∧ x4.output < (10 : ℕ) + x3.size + x4.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - ((10 : ℕ) + x3.size))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        have x11 : (Fin (10 : ℕ) → Bool) → Bool := fun (x11 : Fin (10 : ℕ) → Bool) =>
          have x12 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x11;
          [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x13 : ℕ) => x12 (Fin.ofNat (11 : ℕ) (x13 / (11 : ℕ))) && x12 (Fin.ofNat (11 : ℕ) (x13 % (11 : ℕ)));
        (∀ (x12 : Fin (9 : ℕ) → Bool), x11 (x2.insertNth Bool.false x12) ≠ x11 (x2.insertNth Bool.true x12) → x3.eval (List.ofFn x12) = Bool.false) →
        ∃ (x13 : Fin (9 : ℕ) → Bool) (x14 : Bool), x4.eval (x3.wires (List.ofFn x13) ++ [x14 || x3.eval (List.ofFn x13)]) ≠ x11 (x2.insertNth x14 x13))
    (hOutOr :
      ∀ (x1 : Fin (11 : ℕ)) (x2 : Fin (10 : ℕ)) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit),
        ↑x1 < (4 : ℕ) →
        PEqualNP.TopForm.IsAO2 (9 : ℕ) x3 →
        PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x3.size) x4 →
        x3.size + x4.size ≤ (17 : ℕ) →
        (9 : ℕ) ≤ x3.output →
        x3.output < (9 : ℕ) + x3.size →
        (10 : ℕ) + x3.size ≤ x4.output ∧ x4.output < (10 : ℕ) + x3.size + x4.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - ((10 : ℕ) + x3.size))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        have x11 : (Fin (10 : ℕ) → Bool) → Bool := fun (x11 : Fin (10 : ℕ) → Bool) =>
          have x12 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x11;
          [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x13 : ℕ) => x12 (Fin.ofNat (11 : ℕ) (x13 / (11 : ℕ))) && x12 (Fin.ofNat (11 : ℕ) (x13 % (11 : ℕ)));
        (∀ (x12 : Fin (9 : ℕ) → Bool), x11 (x2.insertNth Bool.false x12) ≠ x11 (x2.insertNth Bool.true x12) → x3.eval (List.ofFn x12) = Bool.false) →
        ∃ (x13 : Fin (9 : ℕ) → Bool) (x14 : Bool), x4.eval (x3.wires (List.ofFn x13) ++ [x14 || x3.eval (List.ofFn x13)]) ≠ x11 (x2.insertNth x14 x13)) :
    ∀ (x1 : Fin (11 : ℕ)) (x2 : Fin (10 : ℕ)) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit),   ↑x1 < (4 : ℕ) →     PEqualNP.TopForm.IsAO2 (9 : ℕ) x3 →       PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x3.size) x4 →         x3.size + x4.size ≤ (17 : ℕ) →           (9 : ℕ) ≤ x3.output →             x3.output < (9 : ℕ) + x3.size →               have x11 : (Fin (10 : ℕ) → Bool) → Bool := fun (x11 : Fin (10 : ℕ) → Bool) =>                 have x12 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x11;                 [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x13 : ℕ) => x12 (Fin.ofNat (11 : ℕ) (x13 / (11 : ℕ))) && x12 (Fin.ofNat (11 : ℕ) (x13 % (11 : ℕ)));               (∀ (x12 : Fin (9 : ℕ) → Bool), x11 (x2.insertNth Bool.false x12) ≠ x11 (x2.insertNth Bool.true x12) → x3.eval (List.ofFn x12) = Bool.false) → ∃ (x13 : Fin (9 : ℕ) → Bool) (x14 : Bool), x4.eval (x3.wires (List.ofFn x13) ++ [x14 || x3.eval (List.ofFn x13)]) ≠ x11 (x2.insertNth x14 x13) := by
  intro a b C3 C4 ha hAO3 hAO4 hSz h3Ge h3Lt
  dsimp only
  intro hSens
  let f : Fin 11 → (Fin 10 → Bool) → Bool := fun v x =>
    let y : Fin 11 → Bool := v.insertNth false x
    [(9 : ℕ), 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97].any fun e =>
      y (Fin.ofNat 11 (e / 11)) && y (Fin.ofNat 11 (e % 11))
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
  have hW3Len : ∀ x : Fin 9 → Bool, (C3.wires (List.ofFn x)).length = 9 + C3.size := by
    intro x
    change (C3.gates.foldl step (List.ofFn x)).length = 9 + C3.gates.length
    rw [hLen, List.length_ofFn]
  have hAllTrue : ∀ v : Fin 11, v.val < 4 → ∀ w : Fin 10,
      f v (w.insertNth true (fun _ => true)) = true := by
    decide
  have hSingleTrue : ∀ v : Fin 11, v.val < 4 → ∀ w : Fin 10,
      f v (w.insertNth true (fun _ => false)) = false := by
    decide
  have hHasNbr : ∀ v : Fin 11, v.val < 4 → ∀ w : Fin 10, ∃ u : Fin 9,
      f v (w.insertNth false (fun i => decide (i = u))) ≠
      f v (w.insertNth true (fun i => decide (i = u))) := by
    decide
  by_cases hOutLt : C4.output < 10 + C3.size + C4.size
  · by_cases hOutGe : 10 + C3.size ≤ C4.output
    · have hk_lt : C4.output - (10 + C3.size) < C4.gates.length := by
        change C4.output - (10 + C3.size) < C4.size
        omega
      have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C4 (C4.output - (10 + C3.size)) = C4.gates[C4.output - (10 + C3.size)]'hk_lt :=
        List.getD_eq_getElem _ _ hk_lt
      rcases hAO4.1 (C4.gates[C4.output - (10 + C3.size)]'hk_lt) (List.getElem_mem hk_lt) with hAnd | hOr
      · exact hOutAnd a b C3 C4 ha hAO3 hAO4 hSz h3Ge h3Lt ⟨hOutGe, hOutLt⟩ (by rw [hge]; exact hAnd) hSens
      · exact hOutOr a b C3 C4 ha hAO3 hAO4 hSz h3Ge h3Lt ⟨hOutGe, hOutLt⟩ (by rw [hge]; exact hOr) hSens
    · have hOutSmall : C4.output < 10 + C3.size := Nat.lt_of_not_ge hOutGe
      by_cases hEq : C4.output = 9 + C3.size
      · refine ⟨fun _ => false, true, ?_⟩
        have hL : (C3.wires (List.ofFn (fun _ : Fin 9 => false)) ++ [true || C3.eval (List.ofFn (fun _ : Fin 9 => false))]).length = 10 + C3.size := by
          rw [List.length_append, hW3Len, List.length_singleton]
          omega
        have hEv : C4.eval (C3.wires (List.ofFn (fun _ : Fin 9 => false)) ++ [true || C3.eval (List.ofFn (fun _ : Fin 9 => false))]) = true := by
          change (C4.gates.foldl step _).getD C4.output false = true
          rw [hPref C4.gates _ C4.output (by rw [hL]; exact hOutSmall)]
          rw [List.getD_append_right _ _ _ _ (by rw [hW3Len]; omega)]
          have hsub : C4.output - (C3.wires (List.ofFn (fun _ : Fin 9 => false))).length = 0 := by
            rw [hW3Len]; omega
          rw [hsub, List.getD_cons_zero, Bool.true_or]
        rw [hEv]
        have hF := hSingleTrue a ha b
        change f a (b.insertNth true (fun _ => false)) = false at hF
        change true ≠ f a (b.insertNth true (fun _ => false))
        rw [hF]
        decide
      · have hLt9 : C4.output < 9 + C3.size := by omega
        obtain ⟨u, hDiff⟩ := hHasNbr a ha b
        let x0 : Fin 9 → Bool := fun i => decide (i = u)
        have hEvalIndep : ∀ bit : Bool,
            C4.eval (C3.wires (List.ofFn x0) ++ [bit || C3.eval (List.ofFn x0)]) =
            (C3.wires (List.ofFn x0)).getD C4.output false := by
          intro bit
          have hL : (C3.wires (List.ofFn x0) ++ [bit || C3.eval (List.ofFn x0)]).length = 10 + C3.size := by
            rw [List.length_append, hW3Len, List.length_singleton]
            omega
          change (C4.gates.foldl step _).getD C4.output false = _
          rw [hPref C4.gates _ C4.output (by rw [hL]; exact hOutSmall)]
          exact List.getD_append _ _ _ _ (by rw [hW3Len]; exact hLt9)
        by_cases hEqF : C4.eval (C3.wires (List.ofFn x0) ++ [false || C3.eval (List.ofFn x0)]) = f a (b.insertNth false x0)
        · refine ⟨x0, true, ?_⟩
          intro hEqT
          apply hDiff
          have h1 : (C3.wires (List.ofFn x0)).getD C4.output false = f a (b.insertNth false x0) := by
            rw [← hEvalIndep false]; exact hEqF
          have h2 : (C3.wires (List.ofFn x0)).getD C4.output false = f a (b.insertNth true x0) := by
            rw [← hEvalIndep true]; exact hEqT
          exact h1.symm.trans h2
        · exact ⟨x0, false, hEqF⟩
  · have hOutBig : 10 + C3.size + C4.size ≤ C4.output := Nat.le_of_not_lt hOutLt
    refine ⟨fun _ => true, true, ?_⟩
    have hL0 : (C3.wires (List.ofFn (fun _ : Fin 9 => true)) ++ [true || C3.eval (List.ofFn (fun _ : Fin 9 => true))]).length = 10 + C3.size := by
      rw [List.length_append, hW3Len, List.length_singleton]
      omega
    have hL : (C4.gates.foldl step (C3.wires (List.ofFn (fun _ : Fin 9 => true)) ++ [true || C3.eval (List.ofFn (fun _ : Fin 9 => true))])).length = 10 + C3.size + C4.size := by
      rw [hLen, hL0]
      rfl
    have hEv : C4.eval (C3.wires (List.ofFn (fun _ : Fin 9 => true)) ++ [true || C3.eval (List.ofFn (fun _ : Fin 9 => true))]) = false := by
      change (C4.gates.foldl step _).getD C4.output false = false
      exact List.getD_eq_default _ _ (by omega)
    rw [hEv]
    have hT := hAllTrue a ha b
    change false ≠ f a (b.insertNth true (fun _ => true))
    rw [hT]
    decide
