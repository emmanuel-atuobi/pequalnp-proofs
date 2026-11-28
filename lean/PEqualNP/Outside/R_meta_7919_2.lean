import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7919_2
    (hWitnessAnd :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (v0 : Fin x1) (g0 : PEqualNP.CircuitLowerBounds.Gate),
        (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
        (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
        (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
        (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
        (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
        PEqualNP.MetaComplexity.FanInTwo x5 →
        x1 ≤ x5.output ∧ x5.output < x1 + x5.size →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →
        (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →
        (∀ x14 ∉ x3, (2 : ℕ) ≤ (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates).length) →
        have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑v0) x5.gates;
        (v0 ∉ x3 ∧ x16.length = (2 : ℕ) ∧ g0 ∈ x16 ∧ g0.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17)
    (hWitnessNot :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (v0 : Fin x1) (g0 : PEqualNP.CircuitLowerBounds.Gate),
        (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
        (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
        (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
        (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
        (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
        PEqualNP.MetaComplexity.FanInTwo x5 →
        x1 ≤ x5.output ∧ x5.output < x1 + x5.size →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →
        (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →
        (∀ x14 ∉ x3, (2 : ℕ) ≤ (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates).length) →
        have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑v0) x5.gates;
        (v0 ∉ x3 ∧ x16.length = (2 : ℕ) ∧ g0 ∈ x16 ∧ g0.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3, (2 : ℕ) ≤ (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates).length) →                     (∃ x15 ∉ x3,                         have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates;                         x16.length = (2 : ℕ) ∧ ∃ x17 ∈ x16, x17.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) →                       ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  intro n G A f C hDeg hGirth hNoA hEdge hSpec hFan hFun hMin hGe2 hEx2
  obtain ⟨u, v, huv⟩ := hEdge
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
  let xuv : Fin n → Bool := fun i => decide (i = u ∨ i = v)
  have hfuv : f xuv = true :=
    (hSpec xuv).mpr (Or.inr ⟨u, v, huv, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩)
  have hCuv : C.eval (List.ofFn xuv) = true := (congrFun hFun xuv).trans hfuv
  have hOutLt : C.output < n + C.size := by
    by_contra hge
    have hge : n + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hev : (C.gates.foldl step (List.ofFn xuv)).getD C.output false = true := hCuv
    have hl : (C.gates.foldl step (List.ofFn xuv)).length = n + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn xuv)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hOutGe : n ≤ C.output := by
    by_contra hlt
    have hlt : C.output < n := Nat.lt_of_not_ge hlt
    let w0 : Fin n := ⟨C.output, hlt⟩
    by_cases hwA : w0 ∈ A
    · have huNotA : u ∉ A := hNoA u v huv
      have hvNotA : v ∉ A := hNoA v u huv.symm
      have hwNeU : w0 ≠ u := fun h => huNotA (h ▸ hwA)
      have hwNeV : w0 ≠ v := fun h => hvNotA (h ▸ hwA)
      have hev : (C.gates.foldl step (List.ofFn xuv)).getD C.output false = true := hCuv
      rw [hPref C.gates (List.ofFn xuv) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
      simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
      change decide (w0 = u ∨ w0 = v) = true at hev
      rcases of_decide_eq_true hev with h1 | h2
      · exact hwNeU h1
      · exact hwNeV h2
    · let xS : Fin n → Bool := fun i => decide (i = w0)
      have hfS : f xS = false := by
        cases h : f xS
        · rfl
        · rcases (hSpec xS).mp h with ⟨a, haA, hxa⟩ | ⟨p, q, hpq, hxp, hxq⟩
          · have haw : a = w0 := of_decide_eq_true hxa
            exact False.elim (hwA (haw ▸ haA))
          · have hpw : p = w0 := of_decide_eq_true hxp
            have hqw : q = w0 := of_decide_eq_true hxq
            rw [hpw, hqw] at hpq
            exact False.elim (G.ne_of_adj hpq rfl)
      have hCS : C.eval (List.ofFn xS) = false := (congrFun hFun xS).trans hfS
      have hev : (C.gates.foldl step (List.ofFn xS)).getD C.output false = false := hCS
      rw [hPref C.gates (List.ofFn xS) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
      simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
      change decide (w0 = w0) = false at hev
      rw [decide_eq_true rfl] at hev
      exact Bool.noConfusion hev
  obtain ⟨v0, hv0NotA, hLen2, g0, hg0Mem, hg0NeOr⟩ := hEx2
  have hg0Gates : g0 ∈ C.gates := (List.mem_filter.mp hg0Mem).1
  rcases (hFan g0 hg0Gates).1 with hAnd | hOr | hNot
  · exact hWitnessAnd n G A f C v0 g0 hDeg hGirth hNoA ⟨u, v, huv⟩ hSpec hFan ⟨hOutGe, hOutLt⟩ hFun hMin hGe2 ⟨hv0NotA, hLen2, hg0Mem, hAnd⟩
  · exact False.elim (hg0NeOr hOr)
  · exact hWitnessNot n G A f C v0 g0 hDeg hGirth hNoA ⟨u, v, huv⟩ hSpec hFan ⟨hOutGe, hOutLt⟩ hFun hMin hGe2 ⟨hv0NotA, hLen2, hg0Mem, hNot⟩
