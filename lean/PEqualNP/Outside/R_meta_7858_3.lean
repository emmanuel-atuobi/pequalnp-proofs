import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7858_3
    (hHasOr :
      let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit;
      have x2 : ℕ := (26 : ℕ);
      have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | PEqualNP.CircuitLowerBounds.Circuit.eval x3 (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true};
      have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty;
      have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };
      have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (x7 x8 : x1),
        x7.gates = x8.gates →
        PEqualNP.MetaComplexity.Monotone2 x7 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 →
        x7.size < (63 : ℕ) →
        x2 ≤ x7.output ∧ x7.output < x2 + x7.size →
        x2 ≤ x8.output ∧ x8.output < x2 + x7.size →
        x7.output ≠ x8.output →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x7.output - x2)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∃ (x13 : ℕ) (x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) →
        x4 x7 →
        x4 x8 →
        Disjoint (x3 x7) (x3 x8) →
        (∀ x17 < x7.size, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) →
        False)
    (hBothAnd :
      let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit;
      have x2 : ℕ := (26 : ℕ);
      have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | PEqualNP.CircuitLowerBounds.Circuit.eval x3 (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true};
      have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty;
      have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };
      have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (x7 x8 : x1),
        x7.gates = x8.gates →
        PEqualNP.MetaComplexity.Monotone2 x7 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 →
        x7.size < (63 : ℕ) →
        x2 ≤ x7.output ∧ x7.output < x8.output ∧ x8.output < x2 + x7.size →
        x6 x7 (x7.output - x2) →
        x6 x7 (x8.output - x2) →
        (∃ (x13 : ℕ) (x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) →
        x4 x7 →
        x4 x8 →
        Disjoint (x3 x7) (x3 x8) →
        (∀ x17 < x7.size, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) →
        False) :
    let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit; have x2 : ℕ := (26 : ℕ); have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | PEqualNP.CircuitLowerBounds.Circuit.eval x3 (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true}; have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty; have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }; have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and; ∀ (x7 x8 : x1), x7.gates = x8.gates → PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 → PEqualNP.CircuitLowerBounds.Circuit.size x7 < (63 : ℕ) → (∃ (x13 : ℕ) (x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) → x4 x7 → x4 x8 → Disjoint (x3 x7) (x3 x8) → (∀ x17 < PEqualNP.CircuitLowerBounds.Circuit.size x7, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) → False := by
  intro x1 x2 x3 x4 x5 x6 C1 C2 hEqG hMono hRB hSz hNested hValid1 hValid2 hDisj hMin
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
  have hAvoidPt : ∀ p0 : Fin 13, ∃ (l : Fin 13) (p : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ p ≠ p0 := by
    decide
  have hAvoidLn : ∀ l0 : Fin 13, ∃ (l : Fin 13) (p : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ l ≠ l0 := by
    decide
  have hAnyInc : ∃ (l : Fin 13) (p : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l := by
    decide
  have hBounds : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 C →
      26 ≤ C.output ∧ C.output < 26 + C.size := by
    intro C hR
    constructor
    · by_contra hlt
      have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
      by_cases h13 : C.output < 13
      · let p0 : Fin 13 := ⟨C.output, h13⟩
        obtain ⟨l, p, hpl, hpne⟩ := hAvoidPt p0
        have hev := hR l p hpl
        change (C.gates.foldl step (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))))).getD C.output false = true at hev
        rw [hPref C.gates _ C.output (by simp only [List.length_append, List.length_ofFn]; exact hlt)] at hev
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13), List.getElem?_ofFn] at hev
        simp only [h13, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hev
        exact hpne hev.symm
      · let l0 : Fin 13 := ⟨C.output - 13, by omega⟩
        obtain ⟨l, p, hpl, hlne⟩ := hAvoidLn l0
        have hev := hR l p hpl
        change (C.gates.foldl step (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))))).getD C.output false = true at hev
        rw [hPref C.gates _ C.output (by simp only [List.length_append, List.length_ofFn]; exact hlt)] at hev
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at hev
        simp only [List.length_ofFn] at hev
        rw [List.getElem?_ofFn] at hev
        have hsub : C.output - 13 < 13 := by omega
        simp only [hsub, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hev
        exact hlne hev.symm
    · by_contra hge
      have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
      obtain ⟨l, p, hpl⟩ := hAnyInc
      have hev := hR l p hpl
      change (C.gates.foldl step (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))))).getD C.output false = true at hev
      have hl : (C.gates.foldl step (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))))).length = 26 + C.size := by
        rw [hLen]
        simp only [List.length_append, List.length_ofFn]
        rfl
      have hdf : (C.gates.foldl step (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))))).getD C.output false = false :=
        List.getD_eq_default _ _ (by omega)
      rw [hdf] at hev
      exact Bool.noConfusion hev
  have hB1 : 26 ≤ C1.output ∧ C1.output < 26 + C1.size := hBounds C1 hValid1.1
  have hSzEq : C2.size = C1.size := by
    change C2.gates.length = C1.gates.length
    rw [hEqG]
  have hB2 : 26 ≤ C2.output ∧ C2.output < 26 + C1.size := by
    have h := hBounds C2 hValid2.1
    rw [hSzEq] at h
    exact h
  have hOutNe : C1.output ≠ C2.output := by
    intro heq
    have hCEq : C1 = C2 := by
      cases C1
      cases C2
      dsimp only at hEqG heq
      subst hEqG
      subst heq
      rfl
    obtain ⟨Q, hQ⟩ := hValid1.2
    have hQ2 : Q ∈ x3 C2 := by rw [← hCEq]; exact hQ
    exact Finset.disjoint_left.mp hDisj hQ hQ2
  have hOp : ∀ j, j < C1.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C1 j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C1 j).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro j hj
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C1 j = C1.gates[j]'hj := by
      change C1.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
      exact List.getD_eq_getElem _ _ hj
    rw [hge]
    have hm := (hMono (C1.gates[j]'hj) (List.getElem_mem hj)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  have hMono2 : PEqualNP.MetaComplexity.Monotone2 C2 := by
    intro g hg
    rw [← hEqG] at hg
    exact hMono g hg
  have hRB2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 C2 := by
    intro j hj w hw
    have hj1 : j < C1.gates.length := by rw [hEqG]; exact hj
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C2 j = PEqualNP.MetaComplexity.NestedCover.gateAt C1 j := by
      change C2.gates.getD j _ = C1.gates.getD j _
      rw [← hEqG]
    rw [hge] at hw
    exact hRB j hj1 w hw
  have hNested2 : ∃ (a b : ℕ), x6 C2 a ∧ x6 C2 b ∧ PEqualNP.EdgeOwnership.InCone x2 C2 a b := by
    obtain ⟨a, b, ha, hb, hab⟩ := hNested
    have hga : ∀ k, PEqualNP.MetaComplexity.NestedCover.gateAt C2 k = PEqualNP.MetaComplexity.NestedCover.gateAt C1 k := by
      intro k
      change C2.gates.getD k _ = C1.gates.getD k _
      rw [← hEqG]
    have hConeEq : PEqualNP.EdgeOwnership.InCone x2 C2 a b = PEqualNP.EdgeOwnership.InCone x2 C1 a b := by
      change (a ∈ (PEqualNP.EdgeOwnership.cones x2 C2).getD b []) = (a ∈ (PEqualNP.EdgeOwnership.cones x2 C1).getD b [])
      have hCones : PEqualNP.EdgeOwnership.cones x2 C2 = PEqualNP.EdgeOwnership.cones x2 C1 := by
        cases C1
        cases C2
        dsimp only at hEqG
        subst hEqG
        rfl
      rw [hCones]
    refine ⟨a, b, ?_, ?_, ?_⟩
    · change (PEqualNP.MetaComplexity.NestedCover.gateAt C2 a).op = _; rw [hga]; exact ha
    · change (PEqualNP.MetaComplexity.NestedCover.gateAt C2 b).op = _; rw [hga]; exact hb
    · rw [hConeEq]; exact hab
  have hMin2 : ∀ j < C2.size, ¬(x4 (x5 C2 j) ∧ x4 (x5 C1 j)) ∧ (x6 C2 j → ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C2 j).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 C2 j w)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 C1 j w))) := by
    intro j hj
    have hj1 : j < C1.size := by rw [← hSzEq]; exact hj
    obtain ⟨h1, h2⟩ := hMin j hj1
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C2 j = PEqualNP.MetaComplexity.NestedCover.gateAt C1 j := by
      change C2.gates.getD j _ = C1.gates.getD j _
      rw [← hEqG]
    refine ⟨fun h => h1 ⟨h.2, h.1⟩, ?_⟩
    intro hand w hw
    rw [hga] at hw
    have hand1 : x6 C1 j := by
      change (PEqualNP.MetaComplexity.NestedCover.gateAt C1 j).op = _
      rw [← hga]
      exact hand
    intro hd
    exact h2 hand1 w hw hd.symm
  have hga2 : ∀ k, PEqualNP.MetaComplexity.NestedCover.gateAt C2 k = PEqualNP.MetaComplexity.NestedCover.gateAt C1 k := by
    intro k
    change C2.gates.getD k _ = C1.gates.getD k _
    rw [← hEqG]
  rcases hOp (C1.output - 26) (by omega) with h1And | h1Or
  · rcases hOp (C2.output - 26) (by omega) with h2And | h2Or
    · rcases Nat.lt_or_gt_of_ne hOutNe with hlt | hgt
      · exact hBothAnd C1 C2 hEqG hMono hRB hSz ⟨hB1.1, hlt, hB2.2⟩ h1And h2And hNested hValid1 hValid2 hDisj hMin
      · have hSz2 : C2.size < 63 := by rw [hSzEq]; exact hSz
        have hB2' : 26 ≤ C2.output ∧ C2.output < C1.output ∧ C1.output < 26 + C2.size := by
          rw [hSzEq]; exact ⟨hB2.1, hgt, hB1.2⟩
        have h2And' : x6 C2 (C2.output - x2) := by
          change (PEqualNP.MetaComplexity.NestedCover.gateAt C2 (C2.output - 26)).op = _
          rw [hga2]; exact h2And
        have h1And' : x6 C2 (C1.output - x2) := by
          change (PEqualNP.MetaComplexity.NestedCover.gateAt C2 (C1.output - 26)).op = _
          rw [hga2]; exact h1And
        exact hBothAnd C2 C1 hEqG.symm hMono2 hRB2 hSz2 hB2' h2And' h1And' hNested2 hValid2 hValid1 hDisj.symm hMin2
    · have hSz2 : C2.size < 63 := by rw [hSzEq]; exact hSz
      have hB2' : 26 ≤ C2.output ∧ C2.output < 26 + C2.size := by rw [hSzEq]; exact hB2
      have hB1' : 26 ≤ C1.output ∧ C1.output < 26 + C2.size := by rw [hSzEq]; exact hB1
      have h2Or' : (PEqualNP.MetaComplexity.NestedCover.gateAt C2 (C2.output - x2)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        change (PEqualNP.MetaComplexity.NestedCover.gateAt C2 (C2.output - 26)).op = _
        rw [hga2]; exact h2Or
      exact hHasOr C2 C1 hEqG.symm hMono2 hRB2 hSz2 hB2' hB1' hOutNe.symm h2Or' hNested2 hValid2 hValid1 hDisj.symm hMin2
  · exact hHasOr C1 C2 hEqG hMono hRB hSz hB1 hB2 hOutNe h1Or hNested hValid1 hValid2 hDisj hMin
