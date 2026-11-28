import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_9111_1
    (hSameSide :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ x1.size →
        x1.size ≤ (27 : ℕ) →
        (14 : ℕ) ≤ x1.output →
        x1.output < (14 : ℕ) + x1.size →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
        (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →
        (have x7 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (0 : Fin (2 : ℕ));
         have x8 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (1 : Fin (2 : ℕ));
         (Min.min x7 x8 = (0 : ℕ) ∧ (Max.max x7 x8 = (1 : ℕ) ∨ Max.max x7 x8 = (2 : ℕ))) ∨
         (Min.min x7 x8 = (1 : ℕ) ∧ (Max.max x7 x8 = (2 : ℕ) ∨ Max.max x7 x8 = (3 : ℕ))) ∨
         (Min.min x7 x8 = (2 : ℕ) ∧ (Max.max x7 x8 = (4 : ℕ) ∨ Max.max x7 x8 = (6 : ℕ)))) →
        ∃ (x9 : Bool), PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x10 : ℕ) => x10 == if x9 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.true)
    (hCrossSide :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ x1.size →
        x1.size ≤ (27 : ℕ) →
        (14 : ℕ) ≤ x1.output →
        x1.output < (14 : ℕ) + x1.size →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
        (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →
        (have x7 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (0 : Fin (2 : ℕ));
         have x8 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (1 : Fin (2 : ℕ));
         (Min.min x7 x8 = (0 : ℕ) ∧ (Max.max x7 x8 = (7 : ℕ) ∨ Max.max x7 x8 = (8 : ℕ) ∨ Max.max x7 x8 = (11 : ℕ))) ∨
         (Min.min x7 x8 = (1 : ℕ) ∧ (Max.max x7 x8 = (8 : ℕ) ∨ Max.max x7 x8 = (9 : ℕ) ∨ Max.max x7 x8 = (11 : ℕ))) ∨
         (Min.min x7 x8 = (2 : ℕ) ∧ (Max.max x7 x8 = (8 : ℕ) ∨ Max.max x7 x8 = (10 : ℕ)))) →
        ∃ (x9 : Bool), PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x10 : ℕ) => x10 == if x9 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (have x7 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (0 : Fin (2 : ℕ));               have x8 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (1 : Fin (2 : ℕ));               Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * Min.min x7 x8 + Max.max x7 x8) = Bool.true) →               (∃ (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x8) → ∃ (x9 : Bool), PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x10 : ℕ) => x10 == if x9 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.true := by
  classical
  intro C hSz hAO hNe hG0Or hSpec hMask hG1
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
  have hSzGe2 : 2 ≤ C.size := by
    obtain ⟨g1, hg1⟩ := hG1
    have hlt : 1 < C.gates.length := by
      by_contra hge
      have hnone : C.gates[1]? = Option.none := List.getElem?_eq_none (Nat.le_of_not_lt hge)
      rw [hnone] at hg1
      cases hg1
    change 2 ≤ C.gates.length
    omega
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
  have habNe : PEqualNP.TopForm.opnd C 0 (0 : Fin 2) ≠ PEqualNP.TopForm.opnd C 0 (1 : Fin 2) :=
    hNe 0 (by omega)
  have hDecode : ∀ a b : Fin 14,
      a.val ≠ b.val →
      Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * Min.min a.val b.val + Max.max a.val b.val) = Bool.true →
      ((Min.min a.val b.val = 0 ∧ (Max.max a.val b.val = 1 ∨ Max.max a.val b.val = 2)) ∨
       (Min.min a.val b.val = 1 ∧ (Max.max a.val b.val = 2 ∨ Max.max a.val b.val = 3)) ∨
       (Min.min a.val b.val = 2 ∧ (Max.max a.val b.val = 4 ∨ Max.max a.val b.val = 6))) ∨
      ((Min.min a.val b.val = 0 ∧ (Max.max a.val b.val = 7 ∨ Max.max a.val b.val = 8 ∨ Max.max a.val b.val = 11)) ∨
       (Min.min a.val b.val = 1 ∧ (Max.max a.val b.val = 8 ∨ Max.max a.val b.val = 9 ∨ Max.max a.val b.val = 11)) ∨
       (Min.min a.val b.val = 2 ∧ (Max.max a.val b.val = 8 ∨ Max.max a.val b.val = 10))) := by
    decide
  rcases hDecode ⟨PEqualNP.TopForm.opnd C 0 (0 : Fin 2), ha_lt⟩ ⟨PEqualNP.TopForm.opnd C 0 (1 : Fin 2), hb_lt⟩ habNe hMask with hS | hC
  · exact hSameSide C hSzGe2 hSz hOutGe hOutLt hAO hNe hG0Or hSpec hS
  · exact hCrossSide C hSzGe2 hSz hOutGe hOutLt hAO hNe hG0Or hSpec hC
