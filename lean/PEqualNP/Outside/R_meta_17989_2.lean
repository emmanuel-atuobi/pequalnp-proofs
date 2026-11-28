import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17989_2
    (hPt1 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (1 : ℕ) ≤ x1.size →
        x1.size ≤ (27 : ℕ) →
        (14 : ℕ) ≤ x1.output →
        x1.output < (14 : ℕ) + x1.size →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
        (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →
        (have x7 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (0 : Fin (2 : ℕ));
         have x8 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (1 : Fin (2 : ℕ));
         Min.min x7 x8 = (1 : ℕ) ∧ (Max.max x7 x8 = (9 : ℕ) ∨ Max.max x7 x8 = (11 : ℕ))) →
        ∃ (x8 : Bool), PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x9 : ℕ) => x9 == if x8 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.true)
    (hEvenShift :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (1 : ℕ) ≤ x1.size →
        x1.size ≤ (27 : ℕ) →
        (14 : ℕ) ≤ x1.output →
        x1.output < (14 : ℕ) + x1.size →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
        (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →
        (have x7 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (0 : Fin (2 : ℕ));
         have x8 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (1 : Fin (2 : ℕ));
         (Min.min x7 x8 = (0 : ℕ) ∧ Max.max x7 x8 = (8 : ℕ)) ∨ (Min.min x7 x8 = (2 : ℕ) ∧ Max.max x7 x8 = (10 : ℕ))) →
        ∃ (x8 : Bool), PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x9 : ℕ) => x9 == if x8 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (have x7 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (0 : Fin (2 : ℕ));               have x8 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (1 : Fin (2 : ℕ));               Nat.testBit (274919850240 : ℕ) ((14 : ℕ) * Min.min x7 x8 + Max.max x7 x8) = Bool.true) →               ∃ (x8 : Bool), PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x9 : ℕ) => x9 == if x8 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.true := by
  classical
  intro C hSz hAO hNe hG0Or hSpec hMask
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
  have hSzPos : 1 ≤ C.size := by
    by_contra h0
    have h0' : C.gates = [] := List.eq_nil_of_length_eq_zero (by change C.gates.length = 0; change ¬1 ≤ C.gates.length at h0; omega)
    have ha0 : PEqualNP.TopForm.opnd C 0 (0 : Fin 2) = 0 := by
      change (C.gates.getD 0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.getD 0 0 = 0
      rw [h0']
      rfl
    have hb0 : PEqualNP.TopForm.opnd C 0 (1 : Fin 2) = 0 := by
      change (C.gates.getD 0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.getD 1 0 = 0
      rw [h0']
      rfl
    dsimp only at hMask
    rw [ha0, hb0] at hMask
    have hfalse : Nat.testBit (274919850240 : ℕ) ((14 : ℕ) * Min.min (0 : ℕ) (0 : ℕ) + Max.max (0 : ℕ) (0 : ℕ)) = Bool.false := by decide
    rw [hfalse] at hMask
    exact Bool.noConfusion hMask
  have hOutGe : 14 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 14 := Nat.lt_of_not_ge hlt
    let idx : Fin 14 := ⟨C.output, hlt⟩
    let f : Fin 14 → Bool := fun i => decide (i = idx)
    have hEvTrue : C.eval (List.ofFn f) = true := by
      change (C.gates.foldl step (List.ofFn f)).getD C.output false = true
      rw [hPref C.gates (List.ofFn f) C.output (by simp only [List.length_ofFn]; exact hlt)]
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      have heq : (⟨C.output, hlt⟩ : Fin 14) = idx := rfl
      simp only [f, heq, decide_true]
    obtain ⟨p, l, _, hp, hl⟩ := (hSpec f).mp hEvTrue
    simp only [f, decide_eq_true_eq] at hp hl
    have heq := hp.trans hl.symm
    have hv := congrArg Fin.val heq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hOutLt : C.output < 14 + C.size := by
    by_contra hge
    have hge : 14 + C.size ≤ C.output := Nat.le_of_not_lt hge
    let f : Fin 14 → Bool := fun _ => true
    have hEvTrue : C.eval (List.ofFn f) = true :=
      (hSpec f).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
    change (C.gates.foldl step (List.ofFn f)).getD C.output false = true at hEvTrue
    have hlen : (C.gates.foldl step (List.ofFn f)).length = 14 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn f)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hEvTrue
    exact Bool.noConfusion hEvTrue
  have h0lt : 0 < C.gates.length := by change 0 < C.size; omega
  have hga0 : PEqualNP.MetaComplexity.NestedCover.gateAt C 0 = C.gates[0]'h0lt := by
    change C.gates.getD 0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[0]'h0lt
    rw [List.getD_eq_getElem _ _ h0lt]
  have hlen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).inputs.length = 2 := by
    rw [hga0]
    exact hAO.2.2 (C.gates[0]'h0lt) (List.getElem_mem h0lt)
  have ha_lt : PEqualNP.TopForm.opnd C 0 (0 : Fin 2) < 14 := by
    have hmem : PEqualNP.TopForm.opnd C 0 (0 : Fin 2) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).inputs := by
      change (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).inputs.getD 0 0 ∈ _
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem (by omega)
    have h1 := hAO.2.1 0 h0lt _ hmem
    omega
  have hb_lt : PEqualNP.TopForm.opnd C 0 (1 : Fin 2) < 14 := by
    have hmem : PEqualNP.TopForm.opnd C 0 (1 : Fin 2) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).inputs := by
      change (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).inputs.getD 1 0 ∈ _
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem (by omega)
    have h1 := hAO.2.1 0 h0lt _ hmem
    omega
  have hDecode : ∀ a b : Fin 14,
      Nat.testBit (274919850240 : ℕ) ((14 : ℕ) * Min.min a.val b.val + Max.max a.val b.val) = Bool.true →
      (Min.min a.val b.val = 1 ∧ (Max.max a.val b.val = 9 ∨ Max.max a.val b.val = 11)) ∨
      ((Min.min a.val b.val = 0 ∧ Max.max a.val b.val = 8) ∨ (Min.min a.val b.val = 2 ∧ Max.max a.val b.val = 10)) := by
    decide
  rcases hDecode ⟨PEqualNP.TopForm.opnd C 0 (0 : Fin 2), ha_lt⟩ ⟨PEqualNP.TopForm.opnd C 0 (1 : Fin 2), hb_lt⟩ hMask with h0 | h1
  · exact hPt1 C hSzPos hSz hOutGe hOutLt hAO hNe hG0Or hSpec h0
  · exact hEvenShift C hSzPos hSz hOutGe hOutLt hAO hNe hG0Or hSpec h1
