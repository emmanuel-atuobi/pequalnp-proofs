import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6192_2
    (hMono :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Fin x1) (x4 : Set (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (30 : ℕ) ≤ x1 →
        Even x1 →
        x2.Colorable (2 : ℕ) →
        (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        (x2.neighborSet x3).ncard = (0 : ℕ) →
        x4.ncard = (3 : ℕ) →
        x3 ∉ x4 →
        (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13 ≠ x15 → ∀ (x18 : x2.Walk x13 x15), x18.IsPath → (5 : ℕ) ≤ x18.length) →
        (∀ x14 ∈ x4, (x2.neighborSet x14).ncard = (2 : ℕ)) →
        (∀ (x15 : Fin x1), x15 ≠ x3 → x15 ∉ x4 → (x2.neighborSet x15).ncard = (3 : ℕ)) →
        (∀ (x16 : Fin x1 → Bool), x5 x16 = Bool.true ↔ ∃ (x17 : Fin x1) (x18 : Fin x1), x2.Adj x17 x18 ∧ x16 x17 = Bool.true ∧ x16 x18 = Bool.true) →
        PEqualNP.MetaComplexity.Monotone2 C →
        x1 ≤ C.output ∧ C.output < x1 + C.size →
        PEqualNP.MetaComplexity.circuitFun x1 C = x5 →
        C.size + (5 : ℕ) < (2 : ℕ) * x1 →
        ∃ (x20 : Fin x1), x20 ≠ x3 ∧ x20 ∉ x4 ∧ ∃ (x21 : ℕ), x21 + (4 : ℕ) ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x22 : Fin x1 → Bool) => x5 (Function.update x22 x20 Bool.false)) x21)
    (hHasNot :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Fin x1) (x4 : Set (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (30 : ℕ) ≤ x1 →
        Even x1 →
        x2.Colorable (2 : ℕ) →
        (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        (x2.neighborSet x3).ncard = (0 : ℕ) →
        x4.ncard = (3 : ℕ) →
        x3 ∉ x4 →
        (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13 ≠ x15 → ∀ (x18 : x2.Walk x13 x15), x18.IsPath → (5 : ℕ) ≤ x18.length) →
        (∀ x14 ∈ x4, (x2.neighborSet x14).ncard = (2 : ℕ)) →
        (∀ (x15 : Fin x1), x15 ≠ x3 → x15 ∉ x4 → (x2.neighborSet x15).ncard = (3 : ℕ)) →
        (∀ (x16 : Fin x1 → Bool), x5 x16 = Bool.true ↔ ∃ (x17 : Fin x1) (x18 : Fin x1), x2.Adj x17 x18 ∧ x16 x17 = Bool.true ∧ x16 x18 = Bool.true) →
        PEqualNP.MetaComplexity.FanInTwo C →
        (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        x1 ≤ C.output ∧ C.output < x1 + C.size →
        PEqualNP.MetaComplexity.circuitFun x1 C = x5 →
        C.size + (5 : ℕ) < (2 : ℕ) * x1 →
        ∃ (x20 : Fin x1), x20 ≠ x3 ∧ x20 ∉ x4 ∧ ∃ (x21 : ℕ), x21 + (4 : ℕ) ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x22 : Fin x1 → Bool) => x5 (Function.update x22 x20 Bool.false)) x21) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Fin x1) (x4 : Set (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (30 : ℕ) ≤ x1 → Even x1 → x2.Colorable (2 : ℕ) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (x2.neighborSet x3).ncard = (0 : ℕ) → x4.ncard = (3 : ℕ) → x3 ∉ x4 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13 ≠ x15 → ∀ (x18 : x2.Walk x13 x15), x18.IsPath → (5 : ℕ) ≤ x18.length) → (∀ x14 ∈ x4, (x2.neighborSet x14).ncard = (2 : ℕ)) → (∀ (x15 : Fin x1), x15 ≠ x3 → x15 ∉ x4 → (x2.neighborSet x15).ncard = (3 : ℕ)) → (∀ (x16 : Fin x1 → Bool), x5 x16 = Bool.true ↔ ∃ (x17 : Fin x1) (x18 : Fin x1), x2.Adj x17 x18 ∧ x16 x17 = Bool.true ∧ x16 x18 = Bool.true) → ∀ (x17 : ℕ), x17 + (5 : ℕ) < (2 : ℕ) * x1 → PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x17 → ∃ (x20 : Fin x1), x20 ≠ x3 ∧ x20 ∉ x4 ∧ ∃ (x21 : ℕ), x21 + (4 : ℕ) ≤ x17 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x22 : Fin x1 → Bool) => x5 (Function.update x22 x20 Bool.false)) x21 := by
  intro n G v3 S4 f h30 hEv hCol hGirth hD3 hC4 h34 hDist hD4 hDall hSpec s hsLt hHCS
  obtain ⟨C, hF2, hSzLe, hEval⟩ := hHCS
  have hFun : PEqualNP.MetaComplexity.circuitFun n C = f := funext hEval
  have hS4ne : S4.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨w1, hw1⟩ := hS4ne
  have hNne : (G.neighborSet w1).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hD4 w1 hw1]; decide)
  obtain ⟨w2, hw12⟩ := hNne
  have hadj : G.Adj w1 w2 := hw12
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
  let x12 : Fin n → Bool := fun i => decide (i = w1 ∨ i = w2)
  have hf12 : f x12 = true :=
    (hSpec x12).mpr ⟨w1, w2, hadj, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
  have hC12 : C.eval (List.ofFn x12) = true := by
    have h := congrFun hFun x12
    rw [hf12] at h
    exact h
  have hOutLt : C.output < n + C.size := by
    by_contra hge
    have hge : n + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hev : (C.gates.foldl step (List.ofFn x12)).getD C.output false = true := hC12
    have hl : (C.gates.foldl step (List.ofFn x12)).length = n + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn x12)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hOutGe : n ≤ C.output := by
    by_contra hlt
    have hlt : C.output < n := Nat.lt_of_not_ge hlt
    let w0 : Fin n := ⟨C.output, hlt⟩
    let xS : Fin n → Bool := fun i => decide (i = w0)
    have hfS : f xS = false := by
      cases h : f xS
      · rfl
      · obtain ⟨p, q, hpq, hxp, hxq⟩ := (hSpec xS).mp h
        have hpw : p = w0 := of_decide_eq_true hxp
        have hqw : q = w0 := of_decide_eq_true hxq
        rw [hpw, hqw] at hpq
        exact False.elim (G.ne_of_adj hpq rfl)
    have hCS : C.eval (List.ofFn xS) = false := by
      have h := congrFun hFun xS
      rw [hfS] at h
      exact h
    have hev : (C.gates.foldl step (List.ofFn xS)).getD C.output false = false := hCS
    rw [hPref C.gates (List.ofFn xS) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
    simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
    change decide (w0 = w0) = false at hev
    rw [decide_eq_true rfl] at hev
    exact Bool.noConfusion hev
  have hCszLt : C.size + 5 < 2 * n := by omega
  have hLift : ∀ (res : ∃ (x20 : Fin n), x20 ≠ v3 ∧ x20 ∉ S4 ∧ ∃ (x21 : ℕ), x21 + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun (x22 : Fin n → Bool) => f (Function.update x22 x20 Bool.false)) x21),
      ∃ (x20 : Fin n), x20 ≠ v3 ∧ x20 ∉ S4 ∧ ∃ (x21 : ℕ), x21 + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun (x22 : Fin n → Bool) => f (Function.update x22 x20 Bool.false)) x21 := by
    rintro ⟨v, hv3, hv4, t, ht, hH⟩
    exact ⟨v, hv3, hv4, t, le_trans ht hSzLe, hH⟩
  rcases Classical.em (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) with hNot | hNoNot
  · exact hLift (hHasNot n G v3 S4 f C h30 hEv hCol hGirth hD3 hC4 h34 hDist hD4 hDall hSpec hF2 hNot ⟨hOutGe, hOutLt⟩ hFun hCszLt)
  · have hM2 : PEqualNP.MetaComplexity.Monotone2 C := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hF2 g hg
      refine ⟨?_, hlen⟩
      rcases hop with hAnd | hOr | hN
      · exact Or.inl hAnd
      · exact Or.inr hOr
      · exact False.elim (hNoNot ⟨g, hg, hN⟩)
    exact hLift (hMono n G v3 S4 f C h30 hEv hCol hGirth hD3 hC4 h34 hDist hD4 hDall hSpec hM2 ⟨hOutGe, hOutLt⟩ hFun hCszLt)
