import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17950_1
    (hOutAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool),
        (∀ (x3 : Fin (26 : ℕ)), (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x3 ∈ x4.inputs)) x1.gates).length ≤ (4 : ℕ)) →
        (x1.size = (61 : ℕ) ∧ (26 : ℕ) ≤ x1.output ∧ x1.output < (87 : ℕ) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) →
        (∀ (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ), x2 x6 x7 = (x1.wires (List.ofFn x6)).getD x7 Bool.false) →
        (∀ (x7 : Fin (26 : ℕ) → Bool), x2 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        ∃ (x8 : Fin (26 : ℕ)) (x9 : Finset ℕ), (5 : ℕ) ≤ x9.card ∧ ∀ x10 ∈ x9, x10 < x1.size ∧ ∃ (x12 : Bool) (x13 : Bool), ∃ x14 < (26 : ℕ) + x10, ∀ (x15 : Fin (26 : ℕ) → Bool), x15 x8 = Bool.false → x2 x15 ((26 : ℕ) + x10) = (x12 && x2 x15 x14 || x13))
    (hOutOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool),
        (∀ (x3 : Fin (26 : ℕ)), (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x3 ∈ x4.inputs)) x1.gates).length ≤ (4 : ℕ)) →
        (x1.size = (61 : ℕ) ∧ (26 : ℕ) ≤ x1.output ∧ x1.output < (87 : ℕ) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) →
        (∀ (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ), x2 x6 x7 = (x1.wires (List.ofFn x6)).getD x7 Bool.false) →
        (∀ (x7 : Fin (26 : ℕ) → Bool), x2 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        ∃ (x8 : Fin (26 : ℕ)) (x9 : Finset ℕ), (5 : ℕ) ≤ x9.card ∧ ∀ x10 ∈ x9, x10 < x1.size ∧ ∃ (x12 : Bool) (x13 : Bool), ∃ x14 < (26 : ℕ) + x10, ∀ (x15 : Fin (26 : ℕ) → Bool), x15 x8 = Bool.false → x2 x15 ((26 : ℕ) + x10) = (x12 && x2 x15 x14 || x13)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool), (∀ (x3 : Fin (26 : ℕ)), (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x3 ∈ x4.inputs)) x1.gates).length ≤ (4 : ℕ)) → x1.size = (61 : ℕ) → (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) → (∀ (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ), x2 x6 x7 = (x1.wires (List.ofFn x6)).getD x7 Bool.false) → (∀ (x7 : Fin (26 : ℕ) → Bool), x2 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) → ∃ (x8 : Fin (26 : ℕ)) (x9 : Finset ℕ), (5 : ℕ) ≤ x9.card ∧ ∀ x10 ∈ x9, x10 < x1.size ∧ ∃ (x12 : Bool) (x13 : Bool), ∃ x14 < (26 : ℕ) + x10, ∀ (x15 : Fin (26 : ℕ) → Bool), x15 x8 = Bool.false → x2 x15 ((26 : ℕ) + x10) = (x12 && x2 x15 x14 || x13) := by
  intro C wire hFan hSz hGates hWires hEval
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
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    let f : Fin 26 → Bool := fun i => decide (i.val = C.output)
    have hWT : wire f C.output = true := by
      rw [hWires f C.output]
      change (C.gates.foldl step (List.ofFn f)).getD C.output false = true
      rw [hPref C.gates (List.ofFn f) C.output (by rw [List.length_ofFn]; exact hlt)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hlt, ↓reduceDIte, Option.getD_some, f, decide_eq_true_eq]
    obtain ⟨p, l, _, hpT, hlT⟩ := (hEval f).mp hWT
    simp only [f, Fin.val_castAdd, Fin.val_natAdd, decide_eq_true_eq] at hpT hlT
    omega
  have hOutLt : C.output < 87 := by
    by_contra hge
    have hge : 87 ≤ C.output := Nat.le_of_not_lt hge
    let f : Fin 26 → Bool := fun _ => true
    have hWT : wire f C.output = true := (hEval f).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
    rw [hWires f C.output] at hWT
    change (C.gates.foldl step (List.ofFn f)).getD C.output false = true at hWT
    have hl : (C.gates.foldl step (List.ofFn f)).length = 87 := by
      rw [hLen, List.length_ofFn]
      change 26 + C.size = 87
      omega
    have hdf : (C.gates.foldl step (List.ofFn f)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hWT
    exact Bool.noConfusion hWT
  have hj : C.output - 26 < C.gates.length := by
    change C.output - 26 < C.size
    omega
  have hsome : C.gates[C.output - 26]? = Option.some (C.gates[C.output - 26]'hj) :=
    List.getElem?_eq_getElem hj
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26) = C.gates[C.output - 26]'hj := by
    change C.gates.getD (C.output - 26) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hj
  have hOp := (hGates (C.output - 26) (C.gates[C.output - 26]'hj) hsome).1
  rw [← hge] at hOp
  rcases hOp with hAnd | hOr
  · exact hOutAnd C wire hFan ⟨hSz, hOutGe, hOutLt, hAnd⟩ hGates hWires hEval
  · exact hOutOr C wire hFan ⟨hSz, hOutGe, hOutLt, hOr⟩ hGates hWires hEval
