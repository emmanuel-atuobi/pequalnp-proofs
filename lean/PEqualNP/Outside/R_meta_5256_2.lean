import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5256_2
    (hOutAnd :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1);
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        (PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ (26 : ℕ) ≤ x3.output ∧ x3.output < (26 : ℕ) + x3.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (2 : ℕ) ≤ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))) →
        (∀ (x6 : Bool) (x7 : List Bool), x2 x6 x7 → x3.eval x7 = x6) →
        (∀ x8 < x3.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x2 x12 x13 ∧ (x3.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x3.wires x13).getD x10 Bool.false) = !x12) →
        (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x9 x10) →
        (64 : ℕ) ≤ x3.size)
    (hOutOr :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1);
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        (PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ (26 : ℕ) ≤ x3.output ∧ x3.output < (26 : ℕ) + x3.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (2 : ℕ) ≤ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))) →
        (∀ (x6 : Bool) (x7 : List Bool), x2 x6 x7 → x3.eval x7 = x6) →
        (∀ x8 < x3.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x2 x12 x13 ∧ (x3.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x3.wires x13).getD x10 Bool.false) = !x12) →
        (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x9 x10) →
        (64 : ℕ) ≤ x3.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → (∀ (x6 : Bool) (x7 : List Bool), x2 x6 x7 → x3.eval x7 = x6) → (2 : ℕ) ≤ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (∀ x8 < x3.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x2 x12 x13 ∧ (x3.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x3.wires x13).getD x10 Bool.false) = !x12) → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x9 x10) → (64 : ℕ) ≤ x3.size := by
  intro x1 x2 C hMono hRB hTests hDeg hSep hNest
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
  have hMem0 : (0 : Fin 13) ∈ x1 := by decide
  have hNeNext : ∀ a : Fin 13, a + 1 ≠ a := by
    intro a; revert a; decide
  have hDiagTest : ∀ a : Fin 13,
      C.eval ((List.ofFn fun (q : Fin 13) => Decidable.decide (q = a)) ++
        List.ofFn fun (q : Fin 13) => Decidable.decide (q = a)) = Bool.true := by
    intro a
    apply hTests Bool.true
    change ∃ p l : Fin 13, p - l ∈ x1 ∧ _
    refine ⟨a, a, ?_, rfl⟩
    rw [sub_self]
    exact hMem0
  have hOutLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    let inp := (List.ofFn fun (q : Fin 13) => Decidable.decide (q = (0 : Fin 13))) ++
      List.ofFn fun (q : Fin 13) => Decidable.decide (q = (0 : Fin 13))
    have hev : (C.gates.foldl step inp).getD C.output false = true := hDiagTest 0
    have hvl : inp.length = 26 := by
      simp only [inp, List.length_append, List.length_ofFn]
    have hl : (C.gates.foldl step inp).length = 26 + C.size := by
      rw [hLen, hvl]
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
      let inp := (List.ofFn fun (q : Fin 13) => Decidable.decide (q = p0 + 1)) ++
        List.ofFn fun (q : Fin 13) => Decidable.decide (q = p0 + 1)
      have hev : (C.gates.foldl step inp).getD C.output false = true := hDiagTest (p0 + 1)
      have hvl : inp.length = 26 := by
        simp only [inp, List.length_append, List.length_ofFn]
      rw [hPref C.gates inp C.output (by omega)] at hev
      simp only [inp] at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13), List.getElem?_ofFn] at hev
      simp only [h13, ↓reduceDIte, Option.getD_some, decide_eq_true_eq] at hev
      exact hNeNext p0 hev.symm
    · let l0 : Fin 13 := ⟨C.output - 13, by omega⟩
      let inp := (List.ofFn fun (q : Fin 13) => Decidable.decide (q = l0 + 1)) ++
        List.ofFn fun (q : Fin 13) => Decidable.decide (q = l0 + 1)
      have hev : (C.gates.foldl step inp).getD C.output false = true := hDiagTest (l0 + 1)
      have hvl : inp.length = 26 := by
        simp only [inp, List.length_append, List.length_ofFn]
      rw [hPref C.gates inp C.output (by omega)] at hev
      simp only [inp] at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at hev
      simp only [List.length_ofFn] at hev
      rw [List.getElem?_ofFn] at hev
      have hsub : C.output - 13 < 13 := by omega
      simp only [hsub, ↓reduceDIte, Option.getD_some, decide_eq_true_eq] at hev
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
    have hm := (hMono (C.gates[C.output - 26]'hj) (List.getElem_mem hj)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  rcases hOp with hAnd | hOr
  · exact hOutAnd C ⟨hMono, hRB, hOutGe, hOutLt, hAnd, hDeg⟩ hTests hSep hNest
  · exact hOutOr C ⟨hMono, hRB, hOutGe, hOutLt, hOr, hDeg⟩ hTests hSep hNest
