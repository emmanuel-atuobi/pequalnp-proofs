import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18539_3
    (hMonotone :
      ∀ (x1 : ℕ) (x2 x3 : SimpleGraph (Fin x1)) [x4 : DecidableRel x2.Adj] [x5 : DecidableRel x3.Adj] (x11 : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x6 x7 x8 : Fin x1), x2.Adj x6 x7 → ¬x3.Adj x6 x8) →
        (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) →
        (∃ (x8 : Fin x1) (x9 : Fin x1), x3.Adj x8 x9) →
        (∀ (x9 : Fin x1), ((x2 ⊔ x3).neighborSet x9).ncard = (0 : ℕ) ∨ ((x2 ⊔ x3).neighborSet x9).ncard = (3 : ℕ)) →
        (∀ (x10 : Fin x1) (x11 : (x2 ⊔ x3).Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) →
        PEqualNP.MetaComplexity.Monotone2 C →
        C.size ≤ x11 →
        x1 ≤ C.output ∧ C.output < x1 + C.size →
        (∀ (f : Fin x1 → Bool), C.eval (List.ofFn f) = Bool.true ↔ ∃ (u v : Fin x1), (x2 ⊔ x3).Adj u v ∧ f u = Bool.true ∧ f v = Bool.true) →
        ∃ (x13 : ℕ) (x14 : ℕ), x13 + x14 + (1 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x13 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅) x14)
    (hHasNot :
      ∀ (x1 : ℕ) (x2 x3 : SimpleGraph (Fin x1)) [x4 : DecidableRel x2.Adj] [x5 : DecidableRel x3.Adj] (x11 : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x6 x7 x8 : Fin x1), x2.Adj x6 x7 → ¬x3.Adj x6 x8) →
        (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) →
        (∃ (x8 : Fin x1) (x9 : Fin x1), x3.Adj x8 x9) →
        (∀ (x9 : Fin x1), ((x2 ⊔ x3).neighborSet x9).ncard = (0 : ℕ) ∨ ((x2 ⊔ x3).neighborSet x9).ncard = (3 : ℕ)) →
        (∀ (x10 : Fin x1) (x11 : (x2 ⊔ x3).Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) →
        PEqualNP.MetaComplexity.FanInTwo C →
        (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        C.size ≤ x11 →
        x1 ≤ C.output ∧ C.output < x1 + C.size →
        (∀ (f : Fin x1 → Bool), C.eval (List.ofFn f) = Bool.true ↔ ∃ (u v : Fin x1), (x2 ⊔ x3).Adj u v ∧ f u = Bool.true ∧ f v = Bool.true) →
        ∃ (x13 : ℕ) (x14 : ℕ), x13 + x14 + (1 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x13 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅) x14) :
    ∀ (x1 : ℕ) (x2 x3 : SimpleGraph (Fin x1)) [x4 : DecidableRel x2.Adj] [x5 : DecidableRel x3.Adj], (∀ (x6 x7 x8 : Fin x1), x2.Adj x6 x7 → ¬x3.Adj x6 x8) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∃ (x8 : Fin x1) (x9 : Fin x1), x3.Adj x8 x9) → (∀ (x9 : Fin x1), ((x2 ⊔ x3).neighborSet x9).ncard = (0 : ℕ) ∨ ((x2 ⊔ x3).neighborSet x9).ncard = (3 : ℕ)) → (∀ (x10 : Fin x1) (x11 : (x2 ⊔ x3).Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun (x2 ⊔ x3) ∅) x11 → ∃ (x13 : ℕ) (x14 : ℕ), x13 + x14 + (1 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x13 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅) x14 := by
  classical
  intro n G1 G2 _ _ hDisj hNE1 hNE2 hDeg hGirth s hHas
  obtain ⟨C, hF2, hCs, hCeval⟩ := hHas
  have hCspec : ∀ (f : Fin n → Bool),
      C.eval (List.ofFn f) = Bool.true ↔ ∃ (u v : Fin n), (G1 ⊔ G2).Adj u v ∧ f u = Bool.true ∧ f v = Bool.true := by
    intro f
    rw [hCeval f]
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), f a = Bool.true) || decide (∃ u v, (G1 ⊔ G2).Adj u v ∧ f u = Bool.true ∧ f v = Bool.true)) = Bool.true ↔ _
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
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
  have houtGe : n ≤ C.output := by
    by_contra hlt
    have hlt : C.output < n := Nat.lt_of_not_ge hlt
    let v0 : Fin n := ⟨C.output, hlt⟩
    let x : Fin n → Bool := fun i => decide (i = v0)
    have ht : C.eval (List.ofFn x) = true := by
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = true
      rw [hPref C.gates (List.ofFn x) C.output (by simp only [List.length_ofFn]; exact hlt)]
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      have heq : (⟨C.output, hlt⟩ : Fin n) = v0 := rfl
      simp only [x, heq, decide_true]
    obtain ⟨a, b, hab, ha, hb⟩ := (hCspec x).mp ht
    simp only [x, decide_eq_true_eq] at ha hb
    rw [ha, hb] at hab
    exact (G1 ⊔ G2).ne_of_adj hab rfl
  have houtLt : C.output < n + C.size := by
    by_contra hge
    have hge : n + C.size ≤ C.output := Nat.le_of_not_lt hge
    obtain ⟨a, b, hab⟩ := hNE1
    let x : Fin n → Bool := fun i => decide (i = a ∨ i = b)
    have ht : C.eval (List.ofFn x) = true :=
      (hCspec x).mpr ⟨a, b, Or.inl hab, by simp [x], by simp [x]⟩
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = true at ht
    have hlen : (C.gates.foldl step (List.ofFn x)).length = n + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn x)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at ht
    exact Bool.noConfusion ht
  by_cases hnot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact @hHasNot n G1 G2 _ _ s C hDisj hNE1 hNE2 hDeg hGirth hF2 hnot hCs ⟨houtGe, houtLt⟩ hCspec
  · have hMono : PEqualNP.MetaComplexity.Monotone2 C := by
      intro g hg
      have hf := hF2 g hg
      refine ⟨?_, hf.2⟩
      have hmem := hf.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
      rcases hmem with hA | hO | hN
      · exact Or.inl hA
      · exact Or.inr hO
      · exact False.elim (hnot ⟨g, hg, hN⟩)
    exact @hMonotone n G1 G2 _ _ s C hDisj hNE1 hNE2 hDeg hGirth hMono hCs ⟨houtGe, houtLt⟩ hCspec
