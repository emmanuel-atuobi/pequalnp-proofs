import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18890_3
    (hOutAnd :
      have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (13 : ℕ)), x3.succ ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true;
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x3 : Fin x2.gates.length), ∃ x4 ∈ [(1 : ℕ), (2 : ℕ), (14 : ℕ), (16 : ℕ), (313 : ℕ), (316 : ℕ), (339 : ℕ)], (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (25 : ℕ) + ↑x3 ≠ x2.output ∧ (x2.wires (List.ofFn fun (x5 : Fin (25 : ℕ)) => Decidable.decide (↑x5 = x4 / (25 : ℕ) ∨ ↑x5 = x4 % (25 : ℕ)))).getD ((25 : ℕ) + ↑x3) Bool.false = Bool.true;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x3 →
        (2 : ℕ) ≤ x3.size →
        (25 : ℕ) ≤ x3.output ∧ x3.output < (25 : ℕ) + x3.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.output - (25 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        x1 x3 →
        x2 x3 →
        (59 : ℕ) ≤ x3.size)
    (hOutOr :
      have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (13 : ℕ)), x3.succ ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true;
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x3 : Fin x2.gates.length), ∃ x4 ∈ [(1 : ℕ), (2 : ℕ), (14 : ℕ), (16 : ℕ), (313 : ℕ), (316 : ℕ), (339 : ℕ)], (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (25 : ℕ) + ↑x3 ≠ x2.output ∧ (x2.wires (List.ofFn fun (x5 : Fin (25 : ℕ)) => Decidable.decide (↑x5 = x4 / (25 : ℕ) ∨ ↑x5 = x4 % (25 : ℕ)))).getD ((25 : ℕ) + ↑x3) Bool.false = Bool.true;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x3 →
        (2 : ℕ) ≤ x3.size →
        (25 : ℕ) ≤ x3.output ∧ x3.output < (25 : ℕ) + x3.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.output - (25 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        x1 x3 →
        x2 x3 →
        (59 : ℕ) ≤ x3.size) :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (13 : ℕ)), x3.succ ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x3 : Fin x2.gates.length), ∃ x4 ∈ [(1 : ℕ), (2 : ℕ), (14 : ℕ), (16 : ℕ), (313 : ℕ), (316 : ℕ), (339 : ℕ)], (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (25 : ℕ) + ↑x3 ≠ x2.output ∧ (x2.wires (List.ofFn fun (x5 : Fin (25 : ℕ)) => Decidable.decide (↑x5 = x4 / (25 : ℕ) ∨ ↑x5 = x4 % (25 : ℕ)))).getD ((25 : ℕ) + ↑x3) Bool.false = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x1 x3 → x2 x3 → (59 : ℕ) ≤ x3.size := by
  intro x1 x2 C hMono hSem hWit
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
  have hOutGe : 25 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 25 := Nat.lt_of_not_ge hlt
    let f : Fin 25 → Bool := fun i => decide (i.val = C.output)
    have hev : C.eval (List.ofFn f) = Bool.true := by
      change (C.gates.foldl step (List.ofFn f)).getD C.output false = true
      rw [hPref C.gates (List.ofFn f) C.output (by simp only [List.length_ofFn]; exact hlt)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hlt, ↓reduceDIte, Option.getD_some, f, decide_eq_true_eq]
    obtain ⟨p, l, _, hpT, hlT⟩ := (hSem f).mp hev
    have hpEq : p.val = C.output := by
      simp only [f, Fin.val_castAdd, decide_eq_true_eq] at hpT
      exact hpT
    have hlEq : 12 + l.val = C.output := by
      simp only [f, Fin.val_natAdd, decide_eq_true_eq] at hlT
      exact hlT
    omega
  have hAnyInc : ∃ (p : Fin 12) (l : Fin 13), p.succ ∈ PEqualNP.HeptadCover.singerLines3 l := by
    refine ⟨(0 : Fin 12), (0 : Fin 13), ?_⟩
    decide
  have hOutLt : C.output < 25 + C.size := by
    by_contra hge
    have hge : 25 + C.size ≤ C.output := Nat.le_of_not_lt hge
    obtain ⟨p, l, hpl⟩ := hAnyInc
    let f : Fin 25 → Bool := fun _ => Bool.true
    have hev : C.eval (List.ofFn f) = Bool.true :=
      (hSem f).mpr ⟨p, l, hpl, rfl, rfl⟩
    change (C.gates.foldl step (List.ofFn f)).getD C.output false = true at hev
    have hl : (C.gates.foldl step (List.ofFn f)).length = 25 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn f)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hSz2 : 2 ≤ C.size := by
    obtain ⟨g, _, _, _, hne, _⟩ := hWit
    have hgLt : g.val < C.size := g.isLt
    have hoLt : C.output - 25 < C.size := by omega
    have hneq : g.val ≠ C.output - 25 := by omega
    omega
  have hj : C.output - 25 < C.gates.length := by
    change C.output - 25 < C.size
    omega
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 25) = C.gates[C.output - 25]'hj := by
    change C.gates.getD (C.output - 25) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hj
  have hOp : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 25)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 25)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    rw [hge]
    have hm := (hMono (C.gates[C.output - 25]'hj) (List.getElem_mem hj)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  rcases hOp with hAnd | hOr
  · exact hOutAnd C hMono hSz2 ⟨hOutGe, hOutLt⟩ hAnd hSem hWit
  · exact hOutOr C hMono hSz2 ⟨hOutGe, hOutLt⟩ hOr hSem hWit
