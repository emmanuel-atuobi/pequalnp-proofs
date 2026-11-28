import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17233_1
    (hTouchesZero :
      ∀ (x2 : Fin (14 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        (x2 = (1 : Fin (14 : ℕ)) ∨ x2 = (2 : Fin (14 : ℕ)) ∨ x2 = (8 : Fin (14 : ℕ)) ∨ x2 = (11 : Fin (14 : ℕ))) →
        (15 : ℕ) ≤ x3.output ∧ x3.output < (15 : ℕ) + x3.size →
        x3.size ≤ (26 : ℕ) →
        PEqualNP.TopForm.IsAO2 (15 : ℕ) x3 →
        (∀ x9 < x3.size, PEqualNP.TopForm.opnd x3 x9 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x3 x9 (1 : Fin (2 : ℕ))) →
        (∀ (x10 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 (0 : Fin (14 : ℕ)) || x10 x2]) = Bool.true ↔
          ∃ (x11 : Fin (7 : ℕ)) (x12 : Fin (7 : ℕ)),
            (x11 = x12 ∨ x11 = x12 + (1 : Fin (7 : ℕ)) ∨ x11 = x12 + (3 : Fin (7 : ℕ))) ∧
            x10 (Fin.castAdd (7 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (7 : ℕ) x12) = Bool.true) →
        ∃ (x11 : Bool),
          ((PEqualNP.ReadK.linearParts x3
            (fun (x12 : ℕ) => if x11 = Bool.true then x12 == (7 : ℕ) else x12 == (0 : ℕ) || x12 == (14 : ℕ))
            (List.map (fun (x12 : ℕ) => x12 == (0 : ℕ) || x12 == (7 : ℕ)) (List.range (14 : ℕ)) ++ [Bool.true])).getD x3.output (Bool.false, Bool.false)).2 = Bool.true)
    (hDisjointZeroSeven :
      ∀ (x1 x2 : Fin (14 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        ((x1 = (1 : Fin (14 : ℕ)) ∧ (x2 = (2 : Fin (14 : ℕ)) ∨ x2 = (3 : Fin (14 : ℕ)) ∨ x2 = (8 : Fin (14 : ℕ)) ∨ x2 = (9 : Fin (14 : ℕ)) ∨ x2 = (11 : Fin (14 : ℕ)))) ∨
         (x1 = (2 : Fin (14 : ℕ)) ∧ (x2 = (4 : Fin (14 : ℕ)) ∨ x2 = (6 : Fin (14 : ℕ)) ∨ x2 = (8 : Fin (14 : ℕ)) ∨ x2 = (10 : Fin (14 : ℕ))))) →
        (15 : ℕ) ≤ x3.output ∧ x3.output < (15 : ℕ) + x3.size →
        x3.size ≤ (26 : ℕ) →
        PEqualNP.TopForm.IsAO2 (15 : ℕ) x3 →
        (∀ x9 < x3.size, PEqualNP.TopForm.opnd x3 x9 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x3 x9 (1 : Fin (2 : ℕ))) →
        (∀ (x10 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 x1 || x10 x2]) = Bool.true ↔
          ∃ (x11 : Fin (7 : ℕ)) (x12 : Fin (7 : ℕ)),
            (x11 = x12 ∨ x11 = x12 + (1 : Fin (7 : ℕ)) ∨ x11 = x12 + (3 : Fin (7 : ℕ))) ∧
            x10 (Fin.castAdd (7 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (7 : ℕ) x12) = Bool.true) →
        ∃ (x11 : Bool),
          ((PEqualNP.ReadK.linearParts x3
            (fun (x12 : ℕ) => x12 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ))
            (List.map (fun (x12 : ℕ) => x12 == (0 : ℕ) || x12 == (7 : ℕ)) (List.range (14 : ℕ)) ++ [Bool.false])).getD x3.output (Bool.false, Bool.false)).2 = Bool.true) :
    ∀ (x1 x2 : Fin (14 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ x2 → Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * Min.min ↑x1 ↑x2 + Max.max ↑x1 ↑x2) = Bool.true → ¬(Min.min ↑x1 ↑x2 = (0 : ℕ) ∧ Max.max ↑x1 ↑x2 = (7 : ℕ)) → x3.size ≤ (26 : ℕ) → PEqualNP.TopForm.IsAO2 (15 : ℕ) x3 → (∀ x9 < x3.size, PEqualNP.TopForm.opnd x3 x9 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x3 x9 (1 : Fin (2 : ℕ))) → (∀ (x10 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 x1 || x10 x2]) = Bool.true ↔ ∃ (x11 : Fin (7 : ℕ)) (x12 : Fin (7 : ℕ)), (x11 = x12 ∨ x11 = x12 + (1 : Fin (7 : ℕ)) ∨ x11 = x12 + (3 : Fin (7 : ℕ))) ∧ x10 (Fin.castAdd (7 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (7 : ℕ) x12) = Bool.true) → ∃ (x11 : Bool), ((PEqualNP.ReadK.linearParts x3 (fun (x12 : ℕ) => (x12 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || x12 == (14 : ℕ) && ((↑x1 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || ↑x2 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.map (fun (x12 : ℕ) => x12 == (0 : ℕ) || x12 == (7 : ℕ)) (List.range (14 : ℕ)) ++ [↑x1 == (0 : ℕ) || ↑x1 == (7 : ℕ) || (↑x2 == (0 : ℕ) || ↑x2 == (7 : ℕ))])).getD x3.output (Bool.false, Bool.false)).2 = Bool.true := by
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
  have hDecode : ∀ a b : Fin 14, a < b →
      Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * a.val + b.val) = Bool.true →
      ¬(a.val = 0 ∧ b.val = 7) →
      (a = (0 : Fin 14) ∧ (b = (1 : Fin 14) ∨ b = (2 : Fin 14) ∨ b = (8 : Fin 14) ∨ b = (11 : Fin 14))) ∨
      ((a = (1 : Fin 14) ∧ (b = (2 : Fin 14) ∨ b = (3 : Fin 14) ∨ b = (8 : Fin 14) ∨ b = (9 : Fin 14) ∨ b = (11 : Fin 14))) ∨
       (a = (2 : Fin 14) ∧ (b = (4 : Fin 14) ∨ b = (6 : Fin 14) ∨ b = (8 : Fin 14) ∨ b = (10 : Fin 14)))) := by
    decide
  have hNe07 : ∀ a b : Fin 14,
      ((a = (1 : Fin 14) ∧ (b = (2 : Fin 14) ∨ b = (3 : Fin 14) ∨ b = (8 : Fin 14) ∨ b = (9 : Fin 14) ∨ b = (11 : Fin 14))) ∨
       (a = (2 : Fin 14) ∧ (b = (4 : Fin 14) ∨ b = (6 : Fin 14) ∨ b = (8 : Fin 14) ∨ b = (10 : Fin 14)))) →
      ((a.val == (0 : ℕ)) = Bool.false ∧ (a.val == (7 : ℕ)) = Bool.false ∧
       (b.val == (0 : ℕ)) = Bool.false ∧ (b.val == (7 : ℕ)) = Bool.false) := by
    decide
  have hOrdered : ∀ (a b : Fin 14) (C : PEqualNP.CircuitLowerBounds.Circuit),
      a < b →
      Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * ↑a + ↑b) = Bool.true →
      ¬(↑a = (0 : ℕ) ∧ ↑b = (7 : ℕ)) →
      C.size ≤ (26 : ℕ) →
      PEqualNP.TopForm.IsAO2 (15 : ℕ) C →
      (∀ x9 < C.size, PEqualNP.TopForm.opnd C x9 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd C x9 (1 : Fin (2 : ℕ))) →
      (∀ (x10 : Fin (14 : ℕ) → Bool), C.eval (List.ofFn x10 ++ [x10 a || x10 b]) = Bool.true ↔
        ∃ (x11 : Fin (7 : ℕ)) (x12 : Fin (7 : ℕ)),
          (x11 = x12 ∨ x11 = x12 + (1 : Fin (7 : ℕ)) ∨ x11 = x12 + (3 : Fin (7 : ℕ))) ∧
          x10 (Fin.castAdd (7 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (7 : ℕ) x12) = Bool.true) →
      ∃ (x11 : Bool),
        ((PEqualNP.ReadK.linearParts C
          (fun (x12 : ℕ) => (x12 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || x12 == (14 : ℕ) && ((↑a == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || ↑b == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)))
          (List.map (fun (x12 : ℕ) => x12 == (0 : ℕ) || x12 == (7 : ℕ)) (List.range (14 : ℕ)) ++ [↑a == (0 : ℕ) || ↑a == (7 : ℕ) || (↑b == (0 : ℕ) || ↑b == (7 : ℕ))])).getD C.output (Bool.false, Bool.false)).2 = Bool.true := by
    intro a b C hab hbit hnot07 hsz hAO hdist hEv
    have hOutLt : C.output < 15 + C.size := by
      by_contra hge
      have hge : 15 + C.size ≤ C.output := Nat.le_of_not_lt hge
      let f : Fin 14 → Bool := fun _ => true
      have hT : C.eval (List.ofFn f ++ [f a || f b]) = true :=
        (hEv f).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
      change (C.gates.foldl step (List.ofFn f ++ [f a || f b])).getD C.output false = true at hT
      have hL : (C.gates.foldl step (List.ofFn f ++ [f a || f b])).length = 15 + C.size := by
        rw [hLen, List.length_append, List.length_ofFn, List.length_singleton]
        rfl
      have hF : (C.gates.foldl step (List.ofFn f ++ [f a || f b])).getD C.output false = false :=
        List.getD_eq_default _ _ (by omega)
      rw [hF] at hT
      exact Bool.noConfusion hT
    have hOutGe : 15 ≤ C.output := by
      by_contra hlt
      have hlt : C.output < 15 := Nat.lt_of_not_ge hlt
      by_cases h14 : C.output < 14
      · let idx : Fin 14 := ⟨C.output, h14⟩
        let f : Fin 14 → Bool := fun i => decide (i = idx)
        have hT : C.eval (List.ofFn f ++ [f a || f b]) = true := by
          change (C.gates.foldl step (List.ofFn f ++ [f a || f b])).getD C.output false = true
          rw [hPref C.gates _ C.output (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)]
          rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact h14)]
          rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact h14), List.getElem_ofFn]
          have heq : (⟨C.output, h14⟩ : Fin 14) = idx := rfl
          simp only [f, heq, decide_true]
        obtain ⟨p, l, _, hp, hl⟩ := (hEv f).mp hT
        simp only [f, decide_eq_true_eq] at hp hl
        have hv := congrArg Fin.val (hp.trans hl.symm)
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      · have hEq14 : C.output = 14 := by omega
        let f : Fin 14 → Bool := fun i => decide (i = a)
        have hT : C.eval (List.ofFn f ++ [f a || f b]) = true := by
          change (C.gates.foldl step (List.ofFn f ++ [f a || f b])).getD C.output false = true
          rw [hPref C.gates _ C.output (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)]
          rw [hEq14, List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
          simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero, f, decide_true, Bool.true_or]
        obtain ⟨p, l, _, hp, hl⟩ := (hEv f).mp hT
        simp only [f, decide_eq_true_eq] at hp hl
        have hv := congrArg Fin.val (hp.trans hl.symm)
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
    rcases hDecode a b hab hbit hnot07 with ⟨ha0, hb⟩ | hdisj
    · subst ha0
      have hb7 : ((b : ℕ) == (7 : ℕ)) = Bool.false := by
        rcases hb with rfl | rfl | rfl | rfl <;> rfl
      obtain ⟨x11, hx11⟩ := hTouchesZero b C hb ⟨hOutGe, hOutLt⟩ hsz hAO hdist hEv
      refine ⟨x11, ?_⟩
      have hfn : (fun (x12 : ℕ) => (x12 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || x12 == (14 : ℕ) && (((0 : ℕ) == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || ↑b == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ))) =
          (fun (x12 : ℕ) => if x11 = Bool.true then x12 == (7 : ℕ) else x12 == (0 : ℕ) || x12 == (14 : ℕ)) := by
        funext x12
        cases x11
        · simp
        · simp [hb7]
      have htail : (((0 : ℕ) == (0 : ℕ) || (0 : ℕ) == (7 : ℕ) || (↑b == (0 : ℕ) || ↑b == (7 : ℕ)))) = Bool.true := rfl
      change ((PEqualNP.ReadK.linearParts C (fun (x12 : ℕ) => (x12 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || x12 == (14 : ℕ) && (((0 : ℕ) == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || ↑b == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.map (fun (x12 : ℕ) => x12 == (0 : ℕ) || x12 == (7 : ℕ)) (List.range (14 : ℕ)) ++ [(0 : ℕ) == (0 : ℕ) || (0 : ℕ) == (7 : ℕ) || (↑b == (0 : ℕ) || ↑b == (7 : ℕ))])).getD C.output (Bool.false, Bool.false)).2 = Bool.true
      rw [hfn, htail]
      exact hx11
    · obtain ⟨ha0, ha7, hb0, hb7⟩ := hNe07 a b hdisj
      obtain ⟨x11, hx11⟩ := hDisjointZeroSeven a b C hdisj ⟨hOutGe, hOutLt⟩ hsz hAO hdist hEv
      refine ⟨x11, ?_⟩
      have hfn : (fun (x12 : ℕ) => (x12 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || x12 == (14 : ℕ) && ((↑a == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || ↑b == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ))) =
          (fun (x12 : ℕ) => x12 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) := by
        funext x12
        cases x11 <;> simp [ha0, ha7, hb0, hb7]
      have htail : (↑a == (0 : ℕ) || ↑a == (7 : ℕ) || (↑b == (0 : ℕ) || ↑b == (7 : ℕ))) = Bool.false := by
        simp [ha0, ha7, hb0, hb7]
      rw [hfn, htail]
      exact hx11
  intro x1 x2 x3 hne hbit hnot07 hsz hAO hdist hEval
  rcases lt_or_gt_of_ne hne with h12 | h21
  · have hmn : Min.min (x1 : ℕ) (x2 : ℕ) = (x1 : ℕ) := Nat.min_eq_left (Nat.le_of_lt h12)
    have hmx : Max.max (x1 : ℕ) (x2 : ℕ) = (x2 : ℕ) := Nat.max_eq_right (Nat.le_of_lt h12)
    rw [hmn, hmx] at hbit hnot07
    exact hOrdered x1 x2 x3 h12 hbit hnot07 hsz hAO hdist hEval
  · have hmn : Min.min (x1 : ℕ) (x2 : ℕ) = (x2 : ℕ) := Nat.min_eq_right (Nat.le_of_lt h21)
    have hmx : Max.max (x1 : ℕ) (x2 : ℕ) = (x1 : ℕ) := Nat.max_eq_left (Nat.le_of_lt h21)
    rw [hmn, hmx] at hbit hnot07
    have hEval' : ∀ (x10 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 x2 || x10 x1]) = Bool.true ↔
        ∃ (x11 : Fin (7 : ℕ)) (x12 : Fin (7 : ℕ)),
          (x11 = x12 ∨ x11 = x12 + (1 : Fin (7 : ℕ)) ∨ x11 = x12 + (3 : Fin (7 : ℕ))) ∧
          x10 (Fin.castAdd (7 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (7 : ℕ) x12) = Bool.true := by
      intro x10
      have hx := hEval x10
      rw [Bool.or_comm (x10 x1) (x10 x2)] at hx
      exact hx
    obtain ⟨b, hb⟩ := hOrdered x2 x1 x3 h21 hbit hnot07 hsz hAO hdist hEval'
    refine ⟨b, ?_⟩
    rw [Bool.or_comm (↑x1 == if b = Bool.true then (7 : ℕ) else (0 : ℕ)) (↑x2 == if b = Bool.true then (7 : ℕ) else (0 : ℕ)),
        Bool.or_comm (↑x1 == (0 : ℕ) || ↑x1 == (7 : ℕ)) (↑x2 == (0 : ℕ) || ↑x2 == (7 : ℕ))]
    exact hb
