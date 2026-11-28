import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8285_1
    (hMono :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        x2.Colorable (2 : ℕ) →
        (∀ x7 ∉ x3, (x2.neighborSet x7).ncard = (3 : ℕ)) →
        (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
        (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x3) →
        (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) →
        (∀ (x11 : Fin x1 → Bool), x4 x11 = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →
        (∀ (x12 : Finset (Fin x1)), (∀ (x13 x14 : Fin x1), x2.Adj x13 x14 → x13 ∈ x12 ∨ x14 ∈ x12) → x5 ≤ x12.card) →
        PEqualNP.MetaComplexity.Monotone2 C →
        x1 ≤ C.output ∧ C.output < x1 + C.size →
        PEqualNP.MetaComplexity.circuitFun x1 C = x4 →
        x3.card + x2.edgeSet.ncard + x5 ≤ C.size + (1 : ℕ))
    (hHasNot :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        x2.Colorable (2 : ℕ) →
        (∀ x7 ∉ x3, (x2.neighborSet x7).ncard = (3 : ℕ)) →
        (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
        (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x3) →
        (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) →
        (∀ (x11 : Fin x1 → Bool), x4 x11 = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →
        (∀ (x12 : Finset (Fin x1)), (∀ (x13 x14 : Fin x1), x2.Adj x13 x14 → x13 ∈ x12 ∨ x14 ∈ x12) → x5 ≤ x12.card) →
        PEqualNP.MetaComplexity.FanInTwo C →
        (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        x1 ≤ C.output ∧ C.output < x1 + C.size →
        PEqualNP.MetaComplexity.circuitFun x1 C = x4 →
        x3.card + x2.edgeSet.ncard + x5 ≤ C.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : ℕ), x2.Colorable (2 : ℕ) → (∀ x7 ∉ x3, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x3) → (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) → (∀ (x11 : Fin x1 → Bool), x4 x11 = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → (∀ (x12 : Finset (Fin x1)), (∀ (x13 x14 : Fin x1), x2.Adj x13 x14 → x13 ∈ x12 ∨ x14 ∈ x12) → x5 ≤ x12.card) → ∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x3.card + x2.edgeSet.ncard + x5 ≤ x13 + (1 : ℕ) := by
  intro n G A f tau hCol hDeg hGirth hNoA hExEdge hSpec hCovTau s hHCS
  obtain ⟨C, hF2, hSzLe, hEval⟩ := hHCS
  have hFun : PEqualNP.MetaComplexity.circuitFun n C = f := funext hEval
  obtain ⟨u0, v1, huv⟩ := hExEdge
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
  let xuv : Fin n → Bool := fun i => decide (i = u0 ∨ i = v1)
  have hfuv : f xuv = true :=
    (hSpec xuv).mpr (Or.inr ⟨u0, v1, huv, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩)
  have hCuv : C.eval (List.ofFn xuv) = true := (hEval xuv).trans hfuv
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
    · have huNotA : u0 ∉ A := hNoA u0 v1 huv
      have hvNotA : v1 ∉ A := hNoA v1 u0 huv.symm
      have hwNeU : w0 ≠ u0 := fun h => huNotA (h ▸ hwA)
      have hwNeV : w0 ≠ v1 := fun h => hvNotA (h ▸ hwA)
      have hev : (C.gates.foldl step (List.ofFn xuv)).getD C.output false = true := hCuv
      rw [hPref C.gates (List.ofFn xuv) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
      simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
      change decide (w0 = u0 ∨ w0 = v1) = true at hev
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
      have hCS : C.eval (List.ofFn xS) = false := (hEval xS).trans hfS
      have hev : (C.gates.foldl step (List.ofFn xS)).getD C.output false = false := hCS
      rw [hPref C.gates (List.ofFn xS) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
      simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
      change decide (w0 = w0) = false at hev
      rw [decide_eq_true rfl] at hev
      exact Bool.noConfusion hev
  rcases Classical.em (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) with hNot | hNoNot
  · have hBnd := hHasNot n G A f tau C hCol hDeg hGirth hNoA ⟨u0, v1, huv⟩ hSpec hCovTau hF2 hNot ⟨hOutGe, hOutLt⟩ hFun
    omega
  · have hM2 : PEqualNP.MetaComplexity.Monotone2 C := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hF2 g hg
      refine ⟨?_, hlen⟩
      rcases hop with hAnd | hOr | hN
      · exact Or.inl hAnd
      · exact Or.inr hOr
      · exact False.elim (hNoNot ⟨g, hg, hN⟩)
    have hBnd := hMono n G A f tau C hCol hDeg hGirth hNoA ⟨u0, v1, huv⟩ hSpec hCovTau hM2 ⟨hOutGe, hOutLt⟩ hFun
    omega
