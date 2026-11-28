import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17255_3
    (hNoExtraOr :
      ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (j1 j2 : ℕ),
        x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
        PEqualNP.TopForm.IsLeastAO x1 x3 →
        PEqualNP.TopForm.TopForm x1 x3 →
        x3.size < (22 : ℕ) →
        (11 : ℕ) ≤ x3.output ∧ x3.output < (11 : ℕ) + x3.size →
        PEqualNP.TopForm.junk x1 x3 = {j1, j2} →
        PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 j1 j2 →
        PEqualNP.TopForm.orN x1 x3 ⊆ PEqualNP.TopForm.lam x1 x3 →
        have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
        (4 : ℕ) ≤ x9.card →
        ∀ (x11 : Finset (Fin (11 : ℕ))),
          (∀ (x12 x13 : Fin (11 : ℕ)), (x1.deleteEdges ↑x9).Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) →
          x11.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card < (5 : ℕ) + x9.card →
          False)
    (hHasExtraOr :
      ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (j1 j2 : ℕ),
        x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
        PEqualNP.TopForm.IsLeastAO x1 x3 →
        PEqualNP.TopForm.TopForm x1 x3 →
        x3.size < (22 : ℕ) →
        (11 : ℕ) ≤ x3.output ∧ x3.output < (11 : ℕ) + x3.size →
        PEqualNP.TopForm.junk x1 x3 = {j1, j2} →
        PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 j1 j2 →
        (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).Nonempty →
        have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
        (4 : ℕ) ≤ x9.card →
        ∀ (x11 : Finset (Fin (11 : ℕ))),
          (∀ (x12 x13 : Fin (11 : ℕ)), (x1.deleteEdges ↑x9).Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) →
          x11.card + ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) < (5 : ℕ) + x9.card →
          False) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             (4 : ℕ) ≤ x9.card → ∀ (x11 : Finset (Fin (11 : ℕ))), (∀ (x12 x13 : Fin (11 : ℕ)), (x1.deleteEdges ↑x9).Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x11.card + ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) < (5 : ℕ) + x9.card → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (11 : ℕ) x14 ∧ PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x14 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ ∧ x14.size < x3.size := by
  intro G _ C hEq hLeast hTF hSz hJunk U hU4 T hCov hCard
  obtain ⟨j1, j2, hJeq, hCone⟩ := hJunk
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
  have hAdj89 : G.Adj 8 9 := by rw [hEq]; decide
  have hOutLt : C.output < 11 + C.size := by
    by_contra hge
    have hge : 11 + C.size ≤ C.output := Nat.le_of_not_lt hge
    let x89 : Fin 11 → Bool := fun v => decide (v = 8 ∨ v = 9)
    have hG89 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x89 = true := by
      change (decide (∃ a ∈ (∅ : Finset (Fin 11)), x89 a = true) ||
        decide (∃ u v, G.Adj u v ∧ x89 u = true ∧ x89 v = true)) = true
      have hR : decide (∃ u v, G.Adj u v ∧ x89 u = true ∧ x89 v = true) = true :=
        decide_eq_true ⟨8, 9, hAdj89, by decide, by decide⟩
      rw [hR, Bool.or_true]
    have hEv := congrFun hLeast.2.1 x89
    rw [hG89] at hEv
    change (C.gates.foldl step (List.ofFn x89)).getD C.output false = true at hEv
    have hl : (C.gates.foldl step (List.ofFn x89)).length = 11 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn x89)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hEv
    exact Bool.noConfusion hEv
  have hOutGe : 11 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 11 := Nat.lt_of_not_ge hlt
    let w0 : Fin 11 := ⟨C.output, hlt⟩
    let xS : Fin 11 → Bool := fun v => decide (v = w0)
    have hGS : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ xS = false := by
      change (decide (∃ a ∈ (∅ : Finset (Fin 11)), xS a = true) ||
        decide (∃ u v, G.Adj u v ∧ xS u = true ∧ xS v = true)) = false
      have hL : decide (∃ a ∈ (∅ : Finset (Fin 11)), xS a = true) = false :=
        decide_eq_false (by rintro ⟨a, ha, _⟩; exact Finset.notMem_empty a ha)
      have hR : decide (∃ u v, G.Adj u v ∧ xS u = true ∧ xS v = true) = false :=
        decide_eq_false (by
          rintro ⟨u, v, hadj, hu, hv⟩
          have hu' : u = w0 := of_decide_eq_true hu
          have hv' : v = w0 := of_decide_eq_true hv
          rw [hu', hv'] at hadj
          exact G.ne_of_adj hadj rfl)
      rw [hL, hR]
      rfl
    have hEv := congrFun hLeast.2.1 xS
    rw [hGS] at hEv
    change (C.gates.foldl step (List.ofFn xS)).getD C.output false = false at hEv
    rw [hPref C.gates (List.ofFn xS) C.output (by rw [List.length_ofFn]; exact hlt)] at hEv
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hEv
    simp only [hlt, ↓reduceDIte, Option.getD_some] at hEv
    change decide (w0 = w0) = false at hEv
    rw [decide_eq_true rfl] at hEv
    exact Bool.noConfusion hEv
  by_cases hemp : PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C = ∅
  · have hsub : PEqualNP.TopForm.orN G C ⊆ PEqualNP.TopForm.lam G C :=
      Finset.sdiff_eq_empty_iff_subset.mp hemp
    have h0 : (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card = 0 := by
      rw [hemp]
      exact Finset.card_empty
    rw [h0, Nat.add_zero] at hCard
    exact False.elim (@hNoExtraOr G _ C j1 j2 hEq hLeast hTF hSz ⟨hOutGe, hOutLt⟩ hJeq hCone hsub hU4 T hCov hCard)
  · have hne : (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hemp
    exact False.elim (@hHasExtraOr G _ C j1 j2 hEq hLeast hTF hSz ⟨hOutGe, hOutLt⟩ hJeq hCone hne hU4 T hCov hCard)
