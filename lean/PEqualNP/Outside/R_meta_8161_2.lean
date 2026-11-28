import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8161_2
    (hOutAnd :
      have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];
      have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => ∀ x6 ∈ x1, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x5 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false;
      have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ);
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 x21 : ℕ),
        PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 →
        x6.size ≤ (21 : ℕ) →
        ((11 : ℕ) ≤ x6.output ∧ PEqualNP.ReadTwo.isAnd x6 (x6.output - (11 : ℕ)) ∧ x6.output - (11 : ℕ) ≠ x7 ∧ x6.output - (11 : ℕ) ≠ x8) →
        (7 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x6 →
        PEqualNP.ReadTwo.nOr x6 ≤ (14 : ℕ) →
        x7 < x8 →
        x8 < x6.size →
        x3 x6 x7 →
        x3 x6 x8 →
        (∀ x17 < x6.size, x3 x6 x17 → (x4 x6 x17 ↔ x17 ≠ x7 ∧ x17 ≠ x8)) →
        (∀ x18 < x6.size, x3 x6 x18 → x4 x6 x18 → ∀ x22 < x6.size, x3 x6 x22 → ¬x5 x6 x18 x22) →
        ¬x5 x6 x7 x8 →
        ¬x5 x6 x8 x7 →
        (x21 < x6.size ∧ x3 x6 x21 ∧ x4 x6 x21 ∧ x5 x6 x7 x21 ∧ x5 x6 x8 x21) →
        (∀ x22 ∈ x2, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x24 : Fin (11 : ℕ)) => x22.testBit ↑x24) = Bool.true) →
        (∀ x23 ∈ x1, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x25 : Fin (11 : ℕ)) => x23.testBit ↑x25) = Bool.false) →
        False)
    (hOutOr :
      have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];
      have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => ∀ x6 ∈ x1, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x5 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false;
      have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ);
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 x21 : ℕ),
        PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 →
        x6.size ≤ (21 : ℕ) →
        ((11 : ℕ) ≤ x6.output ∧ PEqualNP.ReadTwo.isOr x6 (x6.output - (11 : ℕ))) →
        (7 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x6 →
        PEqualNP.ReadTwo.nOr x6 ≤ (14 : ℕ) →
        x7 < x8 →
        x8 < x6.size →
        x3 x6 x7 →
        x3 x6 x8 →
        (∀ x17 < x6.size, x3 x6 x17 → (x4 x6 x17 ↔ x17 ≠ x7 ∧ x17 ≠ x8)) →
        (∀ x18 < x6.size, x3 x6 x18 → x4 x6 x18 → ∀ x22 < x6.size, x3 x6 x22 → ¬x5 x6 x18 x22) →
        ¬x5 x6 x7 x8 →
        ¬x5 x6 x8 x7 →
        (x21 < x6.size ∧ x3 x6 x21 ∧ x4 x6 x21 ∧ x5 x6 x7 x21 ∧ x5 x6 x8 x21) →
        (∀ x22 ∈ x2, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x24 : Fin (11 : ℕ)) => x22.testBit ↑x24) = Bool.true) →
        (∀ x23 ∈ x1, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x25 : Fin (11 : ℕ)) => x23.testBit ↑x25) = Bool.false) →
        False) :
    have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => ∀ x6 ∈ x1, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x5 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false; have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 → x6.size ≤ (21 : ℕ) → (7 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x6 → PEqualNP.ReadTwo.nOr x6 ≤ (14 : ℕ) → x7 < x8 → x8 < x6.size → x3 x6 x7 → x3 x6 x8 → (∀ x17 < x6.size, x3 x6 x17 → (x4 x6 x17 ↔ x17 ≠ x7 ∧ x17 ≠ x8)) → (∀ x18 < x6.size, x3 x6 x18 → x4 x6 x18 → ∀ x22 < x6.size, x3 x6 x22 → ¬x5 x6 x18 x22) → ¬x5 x6 x7 x8 → ¬x5 x6 x8 x7 → (∃ x21 < x6.size, x3 x6 x21 ∧ x4 x6 x21 ∧ x5 x6 x7 x21 ∧ x5 x6 x8 x21) → (∀ x22 ∈ x2, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x24 : Fin (11 : ℕ)) => x22.testBit ↑x24) = Bool.true) → (∀ x23 ∈ x1, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x25 : Fin (11 : ℕ)) => x23.testBit ↑x25) = Bool.false) → False := by
  intro x1 x2 x3 x4 x5 C g7 g8 hAO hSz hAnd7 hOr14 h78 h8Sz hA7 hA8 hClean hTop hNC1 hNC2 hMeet hPos hNeg
  obtain ⟨g21, hg21Lt, hg21And, hg21Cl, hg21C7, hg21C8⟩ := hMeet
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
  have hOutLt : C.output < 11 + C.size := by
    by_contra hge
    have hge : 11 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hT : (C.gates.foldl step (List.ofFn fun (x24 : Fin 11) => (513 : ℕ).testBit ↑x24)).getD C.output false = true :=
      hPos 513 (by decide)
    have hl : (C.gates.foldl step (List.ofFn fun (x24 : Fin 11) => (513 : ℕ).testBit ↑x24)).length = 11 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hF : (C.gates.foldl step (List.ofFn fun (x24 : Fin 11) => (513 : ℕ).testBit ↑x24)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hF] at hT
    exact Bool.noConfusion hT
  have hBitCov : ∀ k : Fin 11, ∃ m ∈ x1, m.testBit ↑k = true := by
    decide
  have hOutGe : 11 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 11 := Nat.lt_of_not_ge hlt
    obtain ⟨m, hmMem, hmBit⟩ := hBitCov ⟨C.output, hlt⟩
    have hF : (C.gates.foldl step (List.ofFn fun (x25 : Fin 11) => m.testBit ↑x25)).getD C.output false = false :=
      hNeg m hmMem
    rw [hPref C.gates _ C.output (by rw [List.length_ofFn]; exact hlt)] at hF
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hF
    simp only [hlt, ↓reduceDIte, Option.getD_some] at hF
    rw [hmBit] at hF
    exact Bool.noConfusion hF
  have hkLt : C.output - 11 < C.gates.length := by change C.output - 11 < C.size; omega
  have hgaOut : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 11) = C.gates[C.output - 11]'hkLt :=
    List.getD_eq_getElem _ _ hkLt
  rcases hAO.1 (C.gates[C.output - 11]'hkLt) (List.getElem_mem hkLt) with hAnd | hOr
  · have hOutAndOp : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 11)).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
      rw [hgaOut]
      exact hAnd
    have hOutClean : x4 C (C.output - 11) := by
      intro m hmMem
      have hOutEq : 11 + (C.output - 11) = C.output := by omega
      change (C.wires (List.ofFn fun (x25 : Fin 11) => m.testBit ↑x25)).getD (11 + (C.output - 11)) false = false
      rw [hOutEq]
      exact hNeg m hmMem
    have hNe78 : C.output - 11 ≠ g7 ∧ C.output - 11 ≠ g8 :=
      (hClean (C.output - 11) hkLt hOutAndOp).mp hOutClean
    exact hOutAnd C g7 g8 g21 hAO hSz ⟨hOutGe, ⟨hkLt, hOutAndOp⟩, hNe78.1, hNe78.2⟩ hAnd7 hOr14 h78 h8Sz hA7 hA8 hClean hTop hNC1 hNC2 ⟨hg21Lt, hg21And, hg21Cl, hg21C7, hg21C8⟩ hPos hNeg
  · have hOutOrOp : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 11)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      rw [hgaOut]
      exact hOr
    exact hOutOr C g7 g8 g21 hAO hSz ⟨hOutGe, ⟨hkLt, hOutOrOp⟩⟩ hAnd7 hOr14 h78 h8Sz hA7 hA8 hClean hTop hNC1 hNC2 ⟨hg21Lt, hg21And, hg21Cl, hg21C7, hg21C8⟩ hPos hNeg
