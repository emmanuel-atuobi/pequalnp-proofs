import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17661_3
    (hHasAndOut :
      let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit;
      have x2 : ℕ := (26 : ℕ);
      have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | x3.eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true};
      have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty;
      have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : x1 };
      have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (x7 x8 : x1),
        x7.gates = x8.gates ∧ PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 ∧ x7.size < (63 : ℕ) →
        x2 ≤ x7.output ∧ x7.output < x2 + x7.size ∧ x2 ≤ x8.output ∧ x8.output < x2 + x7.size ∧ x7.output ≠ x8.output ∧ x6 x7 (x7.output - x2) →
        (∃ (x13 x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) →
        x4 x7 ∧ x4 x8 ∧ Disjoint (x3 x7) (x3 x8) →
        (∀ x17 < x7.size, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) →
        (∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x18]? = Option.some x19 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        False)
    (hBothOrOut :
      let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit;
      have x2 : ℕ := (26 : ℕ);
      have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | x3.eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true};
      have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty;
      have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : x1 };
      have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (x7 x8 : x1),
        x7.gates = x8.gates ∧ PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 ∧ x7.size < (63 : ℕ) →
        x2 ≤ x7.output ∧ x7.output < x8.output ∧ x8.output < x2 + x7.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x7.output - x2)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x8.output - x2)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∃ (x13 x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) →
        x4 x7 ∧ x4 x8 ∧ Disjoint (x3 x7) (x3 x8) →
        (∀ x17 < x7.size, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) →
        False) :
    let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit; have x2 : ℕ := (26 : ℕ); have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | PEqualNP.CircuitLowerBounds.Circuit.eval x3 (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true}; have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty; have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }; have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and; ∀ (x7 x8 : x1), x7.gates = x8.gates → PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 → PEqualNP.CircuitLowerBounds.Circuit.size x7 < (63 : ℕ) → (∃ (x13 : ℕ) (x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) → x4 x7 → x4 x8 → Disjoint (x3 x7) (x3 x8) → (∀ x17 < PEqualNP.CircuitLowerBounds.Circuit.size x7, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) → (∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x18]? = Option.some x19 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C1 C2 hG hM1 hRB1 hSz1 hCone h41 h42 hDisj hMin hHasOr
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
  have hLen26 : ∀ (A B : Finset (Fin 13)), (PEqualNP.GenericRejection.incidenceInput A B).length = 26 := by
    intro A B
    change (List.ofFn (fun i : Fin 13 => decide (i ∈ A)) ++ List.ofFn (fun j : Fin 13 => decide (j ∈ B))).length = 26
    simp only [List.length_append, List.length_ofFn]
  have h00 : (0 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have h10 : (1 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have h11 : (1 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 1 := by decide
  have hOutBounds : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 C →
      26 ≤ C.output ∧ C.output < 26 + C.size := by
    intro C hR
    have hLt : C.output < 26 + C.size := by
      by_contra hge
      have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
      have hT := hR 0 0 h00
      change (C.gates.foldl step _).getD C.output false = true at hT
      have hL : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)})).length = 26 + C.size := by
        rw [hLen, hLen26]
        rfl
      have hF : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)})).getD C.output false = false :=
        List.getD_eq_default _ _ (by omega)
      rw [hF] at hT
      exact Bool.noConfusion hT
    have hGe : 26 ≤ C.output := by
      by_contra hlt
      have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
      by_cases h13 : C.output < 13
      · by_cases h0 : C.output = 0
        · have hT := hR 0 1 h10
          change (C.gates.foldl step _).getD C.output false = true at hT
          rw [hPref C.gates _ C.output (by rw [hLen26]; exact hlt), h0] at hT
          have hF : (PEqualNP.GenericRejection.incidenceInput ({(1 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD 0 false = false := by decide
          rw [hF] at hT
          exact Bool.noConfusion hT
        · have hT := hR 0 0 h00
          change (C.gates.foldl step _).getD C.output false = true at hT
          rw [hPref C.gates _ C.output (by rw [hLen26]; exact hlt)] at hT
          have hF : ∀ i : Fin 13, i.val ≠ 0 →
              (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD i.val false = false := by decide
          rw [hF ⟨C.output, h13⟩ h0] at hT
          exact Bool.noConfusion hT
      · by_cases h13eq : C.output = 13
        · have hT := hR 1 1 h11
          change (C.gates.foldl step _).getD C.output false = true at hT
          rw [hPref C.gates _ C.output (by rw [hLen26]; exact hlt), h13eq] at hT
          have hF : (PEqualNP.GenericRejection.incidenceInput ({(1 : Fin 13)} : Finset (Fin 13)) {(1 : Fin 13)}).getD 13 false = false := by decide
          rw [hF] at hT
          exact Bool.noConfusion hT
        · have hT := hR 0 0 h00
          change (C.gates.foldl step _).getD C.output false = true at hT
          rw [hPref C.gates _ C.output (by rw [hLen26]; exact hlt)] at hT
          have hF : ∀ i : Fin 26, 13 < i.val →
              (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD i.val false = false := by decide
          rw [hF ⟨C.output, hlt⟩ (by show 13 < C.output; omega)] at hT
          exact Bool.noConfusion hT
    exact ⟨hGe, hLt⟩
  have hSzEq : C2.size = C1.size := by change C2.gates.length = C1.gates.length; rw [hG]
  obtain ⟨h1Ge, h1Lt⟩ := hOutBounds C1 h41.1
  obtain ⟨h2Ge, h2Lt'⟩ := hOutBounds C2 h42.1
  have h2Lt : C2.output < 26 + C1.size := by omega
  have hNeOut : C1.output ≠ C2.output := by
    intro hEqOut
    have hEqC : C1 = C2 := by cases C1; cases C2; cases hG; cases hEqOut; rfl
    rw [hEqC] at h41 hDisj
    obtain ⟨Q, hQ⟩ := h41.2
    exact Finset.not_disjoint_iff.mpr ⟨Q, hQ, hQ⟩ hDisj
  have hk1 : C1.output - 26 < C1.gates.length := by change C1.output - 26 < C1.size; omega
  have hk2 : C2.output - 26 < C1.gates.length := by change C2.output - 26 < C1.size; omega
  have hga1 : PEqualNP.MetaComplexity.NestedCover.gateAt C1 (C1.output - 26) = C1.gates[C1.output - 26]'hk1 :=
    List.getD_eq_getElem _ _ hk1
  have hga2 : PEqualNP.MetaComplexity.NestedCover.gateAt C1 (C2.output - 26) = C1.gates[C2.output - 26]'hk2 :=
    List.getD_eq_getElem _ _ hk2
  have hM2 : PEqualNP.MetaComplexity.Monotone2 C2 := fun g hg => hM1 g (by rw [hG]; exact hg)
  have hgaEq : ∀ j : ℕ, PEqualNP.MetaComplexity.NestedCover.gateAt C2 j = PEqualNP.MetaComplexity.NestedCover.gateAt C1 j := by
    intro j; change C2.gates.getD j _ = C1.gates.getD j _; rw [hG]
  have hRB2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C2 := fun j hj i hi =>
    hRB1 j (by change j < C1.gates.length; rw [hG]; exact hj) i (by rw [← hgaEq j]; exact hi)
  have hSwapInCone : ∀ a b : ℕ, PEqualNP.EdgeOwnership.InCone 26 C1 a b → PEqualNP.EdgeOwnership.InCone 26 C2 a b := by
    intro a b hic
    change a ∈ (C2.gates.foldl (PEqualNP.EdgeOwnership.coneStep 26) []).getD b []
    rw [← hG]
    exact hic
  have hCone2 : ∃ x13 x14 : ℕ,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C2 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C2 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      PEqualNP.EdgeOwnership.InCone 26 C2 x13 x14 := by
    obtain ⟨a, b, ha, hb, hic⟩ := hCone
    exact ⟨a, b, by rw [hgaEq]; exact ha, by rw [hgaEq]; exact hb, hSwapInCone a b hic⟩
  have hMin2 : ∀ x17 < C2.size,
      ¬((PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := C2.gates.set x17 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }, output := C2.output } ∧
         ({x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | ({ gates := C2.gates.set x17 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }, output := C2.output } : PEqualNP.CircuitLowerBounds.Circuit).eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true}).Nonempty) ∧
        (PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := C1.gates.set x17 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }, output := C1.output } ∧
         ({x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | ({ gates := C1.gates.set x17 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }, output := C1.output } : PEqualNP.CircuitLowerBounds.Circuit).eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true}).Nonempty)) ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C2 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and →
       ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C2 x17).inputs,
         ¬Disjoint ({x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | (PEqualNP.CircuitMoves.eraseGate 26 C2 x17 x20).eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true})
                   ({x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | (PEqualNP.CircuitMoves.eraseGate 26 C1 x17 x20).eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true})) := by
    intro j hj
    have hj1 : j < C1.size := by rw [← hSzEq]; exact hj
    obtain ⟨hSet, hEr⟩ := hMin j hj1
    refine ⟨fun h => hSet ⟨h.2, h.1⟩, fun hAnd u hu => ?_⟩
    rw [hgaEq j] at hAnd hu
    exact fun hd => hEr hAnd u hu hd.symm
  rcases (hM1 (C1.gates[C1.output - 26]'hk1) (List.getElem_mem hk1)).1 with h1And | h1Or
  · exact hHasAndOut C1 C2 ⟨hG, hM1, hRB1, hSz1⟩ ⟨h1Ge, h1Lt, h2Ge, h2Lt, hNeOut, by dsimp only; rw [hga1]; exact h1And⟩
      hCone ⟨h41, h42, hDisj⟩ hMin hHasOr
  · rcases (hM1 (C1.gates[C2.output - 26]'hk2) (List.getElem_mem hk2)).1 with h2And | h2Or
    · have hHasOr2 : ∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), C2.gates[x18]? = Option.some x19 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        rw [← hG]; exact hHasOr
      exact hHasAndOut C2 C1 ⟨hG.symm, hM2, hRB2, by rw [hSzEq]; exact hSz1⟩
        ⟨h2Ge, h2Lt', h1Ge, by rw [hSzEq]; exact h1Lt, hNeOut.symm, by dsimp only; rw [hgaEq, hga2]; exact h2And⟩
        hCone2 ⟨h42, h41, hDisj.symm⟩ hMin2 hHasOr2
    · rcases Nat.lt_or_gt_of_ne hNeOut with h12 | h21
      · exact hBothOrOut C1 C2 ⟨hG, hM1, hRB1, hSz1⟩ ⟨h1Ge, h12, h2Lt⟩
          ⟨by rw [hga1]; exact h1Or, by rw [hga2]; exact h2Or⟩
          hCone ⟨h41, h42, hDisj⟩ hMin
      · exact hBothOrOut C2 C1 ⟨hG.symm, hM2, hRB2, by rw [hSzEq]; exact hSz1⟩
          ⟨h2Ge, h21, by rw [hSzEq]; exact h1Lt⟩
          ⟨by rw [hgaEq, hga2]; exact h2Or, by rw [hgaEq, hga1]; exact h1Or⟩
          hCone2 ⟨h42, h41, hDisj.symm⟩ hMin2
