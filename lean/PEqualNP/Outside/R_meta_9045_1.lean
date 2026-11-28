import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_9045_1
    (hAndWire :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ),
        (200 : ℕ) ≤ q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, (L l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        N + N + g < C.output →
        C.output < N + N + C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B →
          (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD (N + N + g) Bool.false = Bool.false) →
        N * (q + (1 : ℕ)) ≤ (2 : ℕ) *
          ∑ l : Fin N, {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD (N + N + g) Bool.false = Bool.true}.card →
        N * q ≤ (100 : ℕ) * C.size)
    (hOrWire :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ),
        (200 : ℕ) ≤ q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, (L l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        N + N + g < C.output →
        C.output < N + N + C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B →
          (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD (N + N + g) Bool.false = Bool.false) →
        N * (q + (1 : ℕ)) ≤ (2 : ℕ) *
          ∑ l : Fin N, {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD (N + N + g) Bool.false = Bool.true}.card →
        N * q ≤ (100 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x5 < x4.output → x4.output < x2 + x2 + x4.size → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → (x4.wires (PEqualNP.GenericRejection.incidenceInput x13 x14)).getD x5 Bool.false = Bool.false) → x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ x14 : Fin x2, {x15 ∈ x3 x14 | (x4.wires (PEqualNP.GenericRejection.incidenceInput {x15} {x14})).getD x5 Bool.false = Bool.true}.card → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N L C w hq hN hLcard hProj hAO hwlt houtLt hFalse hHalf
  have hfold_pref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (j : ℕ),
      j < init.length →
      (gs.foldl (fun ws h => ws ++ [h.op.eval (h.inputs.map fun i => ws.getD i false)]) init).getD j false =
      init.getD j false := by
    intro gs
    induction gs with
    | nil => intro init j _; rfl
    | cons hd tl ih =>
      intro init j hj
      simp only [List.foldl_cons]
      rw [ih _ j (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ hj
  have hWireLt : ∀ (A B : Finset (Fin N)) (j : ℕ), j < N + N →
      (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD j Bool.false =
      (PEqualNP.GenericRejection.incidenceInput A B).getD j Bool.false := by
    intro A B j hj
    have hlen : (PEqualNP.GenericRejection.incidenceInput A B).length = N + N := by
      change (List.ofFn (fun p : Fin N => decide (p ∈ A)) ++ List.ofFn (fun l : Fin N => decide (l ∈ B))).length = N + N
      simp only [List.length_append, List.length_ofFn]
    exact hfold_pref C.gates (PEqualNP.GenericRejection.incidenceInput A B) j (by omega)
  have hw_ge : N + N ≤ w := by
    by_contra hlt
    push Not at hlt
    by_cases hwN : w < N
    · let p0 : Fin N := ⟨w, hwN⟩
      have hcard_le1 : ∀ l : Fin N,
          ({p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD w Bool.false = Bool.true}).card ≤ 1 := by
        intro l
        have hsub : {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD w Bool.false = Bool.true} ⊆ {p0} := by
          intro p hp
          have hwt := (Finset.mem_filter.mp hp).2
          rw [hWireLt {p} {l} w hlt] at hwt
          change (List.ofFn (fun i : Fin N => decide (i ∈ ({p} : Finset (Fin N)))) ++
            List.ofFn (fun j : Fin N => decide (j ∈ ({l} : Finset (Fin N))))).getD w false = true at hwt
          rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hwN)] at hwt
          rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hwN)] at hwt
          simp only [List.getElem_ofFn, Finset.mem_singleton, decide_eq_true_eq] at hwt
          exact Finset.mem_singleton.mpr hwt.symm
        exact le_trans (Finset.card_le_card hsub) (by simp only [Finset.card_singleton]; rfl)
      have hsum_le : ∑ l : Fin N, {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD w Bool.false = Bool.true}.card ≤ N := by
        calc ∑ l : Fin N, {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD w Bool.false = Bool.true}.card
            ≤ ∑ _l : Fin N, (1 : ℕ) := Finset.sum_le_sum fun l _ => hcard_le1 l
          _ = N := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      have hNpos : 0 < N := by
        rw [hN]
        omega
      have h3 : 3 * N ≤ (q + 1) * N := Nat.mul_le_mul_right N (by omega)
      have hcomm : (q + 1) * N = N * (q + 1) := Nat.mul_comm (q + 1) N
      omega
    · let l0 : Fin N := ⟨w - N, by omega⟩
      have hf := hFalse ∅ {l0} (by simp only [Finset.card_singleton]; omega)
        (fun l _ => Finset.disjoint_empty_right (L l))
      rw [hWireLt ∅ {l0} w hlt] at hf
      change (List.ofFn (fun i : Fin N => decide (i ∈ (∅ : Finset (Fin N)))) ++
        List.ofFn (fun j : Fin N => decide (j ∈ ({l0} : Finset (Fin N))))).getD w false = false at hf
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)] at hf
      have hidx : w - (List.ofFn (fun i : Fin N => decide (i ∈ (∅ : Finset (Fin N))))).length <
          (List.ofFn (fun j : Fin N => decide (j ∈ ({l0} : Finset (Fin N))))).length := by
        simp only [List.length_ofFn]
        omega
      rw [List.getD_eq_getElem _ _ hidx] at hf
      simp only [List.getElem_ofFn, List.length_ofFn, Finset.mem_singleton, decide_eq_true_eq] at hf
      have heq : (⟨w - N, by omega⟩ : Fin N) = l0 := rfl
      rw [heq] at hf
      simp at hf
  let g : ℕ := w - (N + N)
  have hg_eq : N + N + g = w := by omega
  have hg_lt : g < C.gates.length := by
    change g < C.size
    omega
  have hg_mem : PEqualNP.MetaComplexity.NestedCover.gateAt C g ∈ C.gates := by
    change C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hg_lt]
    exact List.getElem_mem hg_lt
  rcases hAO.1 _ hg_mem with hAnd | hOr
  · exact hAndWire q N L C g hq hN hLcard hProj hAO (by omega) houtLt hAnd (by rwa [hg_eq]) (by rwa [hg_eq])
  · exact hOrWire q N L C g hq hN hLcard hProj hAO (by omega) houtLt hOr (by rwa [hg_eq]) (by rwa [hg_eq])
