import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18841_3
    (hOneJunk :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (j0 : ℕ),
        (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) →
        PEqualNP.TopForm.IsLeastAO x1 x3 →
        (26 : ℕ) ≤ x3.output ∧ x3.output < (26 : ℕ) + x3.size →
        PEqualNP.TopForm.junk x1 x3 = {j0} →
        j0 < x3.size ∧ (26 : ℕ) + j0 ≠ x3.output →
        (2 : ℕ) ≤ x3.size →
        (65 : ℕ) ≤ x3.size)
    (hTwoJunk :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (j1 j2 : ℕ),
        (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) →
        PEqualNP.TopForm.IsLeastAO x1 x3 →
        (26 : ℕ) ≤ x3.output ∧ x3.output < (26 : ℕ) + x3.size →
        j1 < j2 ∧ j1 ∈ PEqualNP.TopForm.junk x1 x3 ∧ j2 ∈ PEqualNP.TopForm.junk x1 x3 →
        (26 : ℕ) + j1 ≠ x3.output ∧ (26 : ℕ) + j2 ≠ x3.output →
        (3 : ℕ) ≤ x3.size →
        (65 : ℕ) ≤ x3.size) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 ≠ ∅ → (65 : ℕ) ≤ x3.size := by
  intro G _ C hG hLeast hJunk
  have hFun : PEqualNP.MetaComplexity.circuitFun 26 C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := hLeast.2.1
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
  have hAdj0 : G.Adj (Fin.castAdd 13 (0 : Fin 13)) (Fin.natAdd 13 (0 : Fin 13)) :=
    (hG _ _).mpr ⟨0, 0, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
  let e0 : Fin 26 → Bool := fun k => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13))
  have hGe0 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ e0 = true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin 26)), e0 a = true) ||
      decide (∃ p q, G.Adj p q ∧ e0 p = true ∧ e0 q = true)) = true
    have hR : decide (∃ p q, G.Adj p q ∧ e0 p = true ∧ e0 q = true) = true :=
      decide_eq_true ⟨Fin.castAdd 13 (0 : Fin 13), Fin.natAdd 13 (0 : Fin 13), hAdj0, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
    rw [hR, Bool.or_true]
  have hCe0 : C.eval (List.ofFn e0) = true := (congrFun hFun e0).trans hGe0
  have hOutLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hev : (C.gates.foldl step (List.ofFn e0)).getD C.output false = true := hCe0
    have hl : (C.gates.foldl step (List.ofFn e0)).length = 26 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn e0)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    let w0 : Fin 26 := ⟨C.output, hlt⟩
    let fS : Fin 26 → Bool := fun k => decide (k = w0)
    have hGfS : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ fS = false := by
      change (decide (∃ a ∈ (∅ : Finset (Fin 26)), fS a = true) ||
        decide (∃ p q, G.Adj p q ∧ fS p = true ∧ fS q = true)) = false
      have hL : decide (∃ a ∈ (∅ : Finset (Fin 26)), fS a = true) = false :=
        decide_eq_false (by rintro ⟨_, ha, _⟩; exact Finset.notMem_empty _ ha)
      have hR : decide (∃ p q, G.Adj p q ∧ fS p = true ∧ fS q = true) = false :=
        decide_eq_false (by
          rintro ⟨p, q, hpq, hp, hq⟩
          have hpw : p = w0 := of_decide_eq_true hp
          have hqw : q = w0 := of_decide_eq_true hq
          rw [hpw, hqw] at hpq
          exact G.ne_of_adj hpq rfl)
      rw [hL, hR]
      rfl
    have hCfS : C.eval (List.ofFn fS) = false := (congrFun hFun fS).trans hGfS
    have hev : (C.gates.foldl step (List.ofFn fS)).getD C.output false = false := hCfS
    rw [hPref C.gates (List.ofFn fS) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
    simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
    change decide (w0 = w0) = false at hev
    rw [decide_eq_true rfl] at hev
    exact Bool.noConfusion hev
  have hJunkProp : ∀ j ∈ PEqualNP.TopForm.junk G C, j < C.size ∧ 26 + j ≠ C.output := by
    intro j hj
    have hmem := Finset.mem_filter.mp hj
    have hjLt : j < C.size := Finset.mem_range.mp hmem.1
    refine ⟨hjLt, ?_⟩
    intro hEq
    obtain ⟨_, _, x, hgxT, hFxF⟩ := hmem.2
    have hCxF : (C.wires (List.ofFn x)).getD C.output false = false :=
      (congrFun hFun x).trans hFxF
    have hgxT' : (C.wires (List.ofFn x)).getD (26 + j) false = true := hgxT
    rw [hEq] at hgxT'
    rw [hCxF] at hgxT'
    exact Bool.noConfusion hgxT'
  have hJne : (PEqualNP.TopForm.junk G C).Nonempty := Finset.nonempty_iff_ne_empty.mpr hJunk
  have hCardPos : 1 ≤ (PEqualNP.TopForm.junk G C).card := Finset.card_pos.mpr hJne
  rcases Nat.eq_or_lt_of_le hCardPos with hEq1 | hGt1
  · obtain ⟨j0, hj0Eq⟩ := Finset.card_eq_one.mp hEq1.symm
    have hj0Mem : j0 ∈ PEqualNP.TopForm.junk G C := by
      rw [hj0Eq]
      exact Finset.mem_singleton_self j0
    obtain ⟨hj0Lt, hj0Ne⟩ := hJunkProp j0 hj0Mem
    have hSz2 : 2 ≤ C.size := by omega
    exact @hOneJunk G _ C j0 hG hLeast ⟨hOutGe, hOutLt⟩ hj0Eq ⟨hj0Lt, hj0Ne⟩ hSz2
  · obtain ⟨a, haMem, b, hbMem, hab⟩ := Finset.one_lt_card.mp hGt1
    obtain ⟨haLt, haNe⟩ := hJunkProp a haMem
    obtain ⟨hbLt, hbNe⟩ := hJunkProp b hbMem
    have hSz3 : 3 ≤ C.size := by omega
    rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
    · exact @hTwoJunk G _ C a b hG hLeast ⟨hOutGe, hOutLt⟩ ⟨hlt, haMem, hbMem⟩ ⟨haNe, hbNe⟩ hSz3
    · exact @hTwoJunk G _ C b a hG hLeast ⟨hOutGe, hOutLt⟩ ⟨hgt, hbMem, haMem⟩ ⟨hbNe, haNe⟩ hSz3
