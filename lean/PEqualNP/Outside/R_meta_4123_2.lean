import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4123_2
    (hMonotone :
      ∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) →
        (x3.neighborSet x5).ncard = (3 : ℕ) →
        (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        x4 = x3.deleteEdges (x3.incidenceSet x5) →
        (∃ (a b : Fin x1), x4.Adj a b) →
        PEqualNP.MetaComplexity.Monotone2 C →
        C.size ≤ x2 →
        x1 ≤ C.output ∧ C.output < x1 + C.size →
        (∀ (x11 : Fin x1 → Bool), C.eval (List.ofFn x11) = Bool.true ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →
        ∃ (x13 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x14 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x15 : Fin (x2 + (1 : ℕ)) → Fin x1), ∀ (x16 x17 x18 x19 : Fin x1), x4.Adj x16 x17 → x18 = x19 ∨ x4.Adj x18 x19 → (∃! x22 : Fin (x2 + (1 : ℕ)), x13 x22 x16 x17 ∧ x14 x22 x18 x19) ∧ ∀ (x22 : Fin (x2 + (1 : ℕ))), x13 x22 x16 x17 → x14 x22 x18 x19 → (x15 x22 = x16 ∨ x15 x22 = x17) ∧ ¬((x4.Adj x18 (x15 x22) ∨ x4.Adj x19 (x15 x22)) ∧ x15 x22 ≠ x18 ∧ x15 x22 ≠ x19))
    (hHasNot :
      ∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) →
        (x3.neighborSet x5).ncard = (3 : ℕ) →
        (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        x4 = x3.deleteEdges (x3.incidenceSet x5) →
        (∃ (a b : Fin x1), x4.Adj a b) →
        PEqualNP.MetaComplexity.FanInTwo C →
        (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        C.size ≤ x2 →
        x1 ≤ C.output ∧ C.output < x1 + C.size →
        (∀ (x11 : Fin x1 → Bool), C.eval (List.ofFn x11) = Bool.true ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →
        ∃ (x13 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x14 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x15 : Fin (x2 + (1 : ℕ)) → Fin x1), ∀ (x16 x17 x18 x19 : Fin x1), x4.Adj x16 x17 → x18 = x19 ∨ x4.Adj x18 x19 → (∃! x22 : Fin (x2 + (1 : ℕ)), x13 x22 x16 x17 ∧ x14 x22 x18 x19) ∧ ∀ (x22 : Fin (x2 + (1 : ℕ))), x13 x22 x16 x17 → x14 x22 x18 x19 → (x15 x22 = x16 ∨ x15 x22 = x17) ∧ ¬((x4.Adj x18 (x15 x22) ∨ x4.Adj x19 (x15 x22)) ∧ x15 x22 ≠ x18 ∧ x15 x22 ≠ x19)) :
    ∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (x6 : (Fin x1 → Bool) → Bool), (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) → (x3.neighborSet x5).ncard = (3 : ℕ) → (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → x4 = x3.deleteEdges (x3.incidenceSet x5) → (∀ (x11 : Fin x1 → Bool), x6 x11 = Bool.true ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x2 → ∃ (x13 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x14 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x15 : Fin (x2 + (1 : ℕ)) → Fin x1), ∀ (x16 x17 x18 x19 : Fin x1), x4.Adj x16 x17 → x18 = x19 ∨ x4.Adj x18 x19 → (∃! x22 : Fin (x2 + (1 : ℕ)), x13 x22 x16 x17 ∧ x14 x22 x18 x19) ∧ ∀ (x22 : Fin (x2 + (1 : ℕ))), x13 x22 x16 x17 → x14 x22 x18 x19 → (x15 x22 = x16 ∨ x15 x22 = x17) ∧ ¬((x4.Adj x18 (x15 x22) ∨ x4.Adj x19 (x15 x22)) ∧ x15 x22 ≠ x18 ∧ x15 x22 ≠ x19) := by
  classical
  intro n s G H z f hDeg hDegZ hGirth hH hSpec hHas
  obtain ⟨C, hF2, hCs, hCeval⟩ := hHas
  have hCspec : ∀ (x : Fin n → Bool),
      C.eval (List.ofFn x) = Bool.true ↔ ∃ (a b : Fin n), H.Adj a b ∧ x a = Bool.true ∧ x b = Bool.true := by
    intro x
    rw [hCeval x]
    exact hSpec x
  have hHEdge : ∃ (a b : Fin n), H.Adj a b := by
    have hNzNE : (G.neighborSet z).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨u, hu⟩ := hNzNE
    have hzu : G.Adj z u := hu
    have huz_ne : u ≠ z := (G.ne_of_adj hzu).symm
    have hNuNE : (G.neighborSet u).Nonempty := ⟨z, G.adj_comm u z |>.mpr hzu⟩
    have hNuPos : 0 < (G.neighborSet u).ncard := (Set.ncard_pos (Set.toFinite _)).mpr hNuNE
    have hDegU : (G.neighborSet u).ncard = 3 := by
      rcases hDeg u with h0 | h3
      · omega
      · exact h3
    have hNotSub : ¬G.neighborSet u ⊆ {z} := by
      intro hsub
      have hle := Set.ncard_le_ncard hsub (Set.toFinite {z})
      rw [Set.ncard_singleton, hDegU] at hle
      omega
    obtain ⟨v, hv, hvne⟩ := Set.not_subset.mp hNotSub
    have hvz_ne : v ≠ z := by
      intro heq
      exact hvne (Set.mem_singleton_iff.mpr heq)
    refine ⟨u, v, ?_⟩
    rw [hH, SimpleGraph.deleteEdges_adj]
    refine ⟨hv, ?_⟩
    intro hinc
    rcases Sym2.mem_iff.mp hinc.2 with h1 | h2
    · exact huz_ne h1.symm
    · exact hvz_ne h2.symm
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) init).length =
      init.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro init; simp
    | cons hd tl ih =>
      intro init
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [List.length_append, List.length_singleton]
      omega
  have hfold_pref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (j : ℕ),
      j < init.length →
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) init).getD j false =
      init.getD j false := by
    intro gs
    induction gs with
    | nil => intro init j _; rfl
    | cons hd tl ih =>
      intro init j hj
      simp only [List.foldl_cons]
      rw [ih _ j (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ hj
  have houtGe : n ≤ C.output := by
    by_contra hlt
    have hlt : C.output < n := Nat.lt_of_not_ge hlt
    let v0 : Fin n := ⟨C.output, hlt⟩
    let x : Fin n → Bool := fun i => decide (i = v0)
    have ht : C.eval (List.ofFn x) = true := by
      have h1 := hfold_pref C.gates (List.ofFn x) C.output (by simp only [List.length_ofFn]; exact hlt)
      change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false = true
      rw [h1, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      have heq : (⟨C.output, hlt⟩ : Fin n) = v0 := rfl
      simp only [x, heq, decide_true]
    obtain ⟨a, b, hab, ha, hb⟩ := (hCspec x).mp ht
    simp only [x, decide_eq_true_eq] at ha hb
    rw [ha, hb] at hab
    exact H.ne_of_adj hab rfl
  have houtLt : C.output < n + C.size := by
    by_contra hge
    have hge : n + C.size ≤ C.output := Nat.le_of_not_lt hge
    obtain ⟨a, b, hab⟩ := hHEdge
    let x : Fin n → Bool := fun i => decide (i = a ∨ i = b)
    have ht : C.eval (List.ofFn x) = true :=
      (hCspec x).mpr ⟨a, b, hab, by simp [x], by simp [x]⟩
    change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false = true at ht
    have hlen : (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x)).length = n + C.size := by
      rw [hfold_len, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at ht
    exact Bool.noConfusion ht
  by_cases hnot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact hHasNot n s G H z C hDeg hDegZ hGirth hH hHEdge hF2 hnot hCs ⟨houtGe, houtLt⟩ hCspec
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
    exact hMonotone n s G H z C hDeg hDegZ hGirth hH hHEdge hMono hCs ⟨houtGe, houtLt⟩ hCspec
