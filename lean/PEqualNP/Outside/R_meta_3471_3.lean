import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3471_3
    (hHalfAnd :
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
    (hHalfOr :
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
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q N L C hq hN hLcard hProj hAO houtGe houtLt hOutOr hRight hFalse
  obtain ⟨g0, hg0Some, hg0op⟩ := hOutOr
  let k : ℕ := C.output - (N + N)
  have hk_lt : k < C.gates.length := by
    change C.output - (N + N) < C.size
    omega
  have hg0_eq : C.gates[k]'hk_lt = g0 := by
    rw [List.getElem?_eq_getElem hk_lt] at hg0Some
    exact Option.some.inj hg0Some
  have hg0_mem : g0 ∈ C.gates := by
    rw [← hg0_eq]
    exact List.getElem_mem hk_lt
  have hlen2 : g0.inputs.length = 2 := hAO.2.2 g0 hg0_mem
  cases hinp : g0.inputs with
  | nil => rw [hinp] at hlen2; simp at hlen2
  | cons a rest =>
    cases rest with
    | nil => rw [hinp] at hlen2; simp at hlen2
    | cons b tail =>
      cases tail with
      | cons _ _ => rw [hinp] at hlen2; simp at hlen2
      | nil =>
        have hga0 : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g0 := by
          change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g0
          rw [List.getD_eq_getElem _ _ hk_lt, hg0_eq]
        have ha_lt : a < C.output := by
          have h1 := hAO.2.1 k hk_lt a (by rw [hga0, hinp]; simp)
          omega
        have hb_lt : b < C.output := by
          have h1 := hAO.2.1 k hk_lt b (by rw [hga0, hinp]; simp)
          omega
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
        have hEvalOr : ∀ x : List Bool, x.length = N + N →
            C.eval x = ((C.wires x).getD a Bool.false || (C.wires x).getD b Bool.false) := by
          intro x hxlen
          have hsplit : C.gates = C.gates.take k ++ g0 :: C.gates.drop (k + 1) := by
            have h1 := (List.take_append_drop k C.gates).symm
            have h2 : C.gates.drop k = g0 :: C.gates.drop (k + 1) := by
              rw [← hg0_eq]
              exact List.drop_eq_getElem_cons hk_lt
            rw [h2] at h1
            exact h1
          let w0 := (C.gates.take k).foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) x
          have hw0_len : w0.length = C.output := by
            have h1 := hfold_len (C.gates.take k) x
            rw [hxlen, List.length_take, Nat.min_eq_left (le_of_lt hk_lt)] at h1
            change w0.length = N + N + k at h1
            omega
          let bval := g0.op.eval (g0.inputs.map fun i => w0.getD i false)
          have hbval : bval = (w0.getD a false || w0.getD b false) := by
            dsimp only [bval]
            rw [hg0op, hinp, List.map_cons, List.map_cons, List.map_nil]
            cases w0.getD a false <;> cases w0.getD b false <;> rfl
          have hw_eq : C.wires x = (C.gates.drop (k + 1)).foldl
              (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (w0 ++ [bval]) := by
            change C.gates.foldl _ x = _
            conv_lhs => rw [hsplit]
            rw [List.foldl_append, List.foldl_cons]
          have hw_out : (C.wires x).getD C.output false = bval := by
            rw [hw_eq, hfold_pref _ _ C.output (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
            rw [List.getD_append_right _ _ _ _ (by omega)]
            simp only [hw0_len, Nat.sub_self, List.getD_cons_zero]
          have hw_a : (C.wires x).getD a false = w0.getD a false := by
            rw [hw_eq, hfold_pref _ _ a (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
            exact List.getD_append _ _ _ _ (by omega)
          have hw_b : (C.wires x).getD b false = w0.getD b false := by
            rw [hw_eq, hfold_pref _ _ b (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
            exact List.getD_append _ _ _ _ (by omega)
          change (C.wires x).getD C.output false = _
          rw [hw_out, hbval, hw_a, hw_b]
        have hLenInc : ∀ A B : Finset (Fin N), (PEqualNP.GenericRejection.incidenceInput A B).length = N + N := by
          intro A B
          change (List.ofFn (fun i : Fin N => decide (i ∈ A)) ++ List.ofFn (fun j : Fin N => decide (j ∈ B))).length = N + N
          simp only [List.length_append, List.length_ofFn]
        have hFalseAB : ∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B →
            (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD a Bool.false = Bool.false ∧
            (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD b Bool.false = Bool.false := by
          intro A B hB hF
          have h1 := hFalse A B hB hF
          rw [hEvalOr _ (hLenInc A B), Bool.or_eq_false_iff] at h1
          exact h1
        have hCoverSum : ∀ l : Fin N,
            (L l).card ≤
              {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a Bool.false = Bool.true}.card +
              {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b Bool.false = Bool.true}.card := by
          intro l
          have hsub : L l ⊆
              {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a Bool.false = Bool.true} ∪
              {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b Bool.false = Bool.true} := by
            intro p hp
            have h1 := hRight l p hp
            rw [hEvalOr _ (hLenInc {p} {l}), Bool.or_eq_true] at h1
            rw [Finset.mem_union]
            rcases h1 with ha1 | hb1
            · exact Or.inl (Finset.mem_filter.mpr ⟨hp, ha1⟩)
            · exact Or.inr (Finset.mem_filter.mpr ⟨hp, hb1⟩)
          exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
        have hTot : N * (q + 1) ≤
            (∑ l : Fin N, {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a Bool.false = Bool.true}.card) +
            (∑ l : Fin N, {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b Bool.false = Bool.true}.card) := by
          calc N * (q + 1)
              = ∑ l : Fin N, (L l).card := by
                  simp only [hLcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
            _ ≤ ∑ l : Fin N, ({p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a Bool.false = Bool.true}.card +
                  {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b Bool.false = Bool.true}.card) :=
                Finset.sum_le_sum fun l _ => hCoverSum l
            _ = _ := Finset.sum_add_distrib
        have hFinish : ∀ w : ℕ, w < C.output →
            (∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B →
              (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD w Bool.false = Bool.false) →
            N * (q + (1 : ℕ)) ≤ (2 : ℕ) *
              ∑ l : Fin N, {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD w Bool.false = Bool.true}.card →
            N * q ≤ (100 : ℕ) * C.size := by
          intro w hwlt hFw hHalf
          have hWireLt : ∀ (A B : Finset (Fin N)) (j : ℕ), j < N + N →
              (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD j Bool.false =
              (PEqualNP.GenericRejection.incidenceInput A B).getD j Bool.false := by
            intro A B j hj
            exact hfold_pref C.gates (PEqualNP.GenericRejection.incidenceInput A B) j (by rw [hLenInc A B]; exact hj)
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
              have hNpos : 0 < N := by rw [hN]; omega
              have h3 : 3 * N ≤ (q + 1) * N := Nat.mul_le_mul_right N (by omega)
              have hcomm : (q + 1) * N = N * (q + 1) := Nat.mul_comm (q + 1) N
              omega
            · let l0 : Fin N := ⟨w - N, by omega⟩
              have hf := hFw ∅ {l0} (by simp only [Finset.card_singleton]; omega)
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
          · exact hHalfAnd q N L C g hq hN hLcard hProj hAO (by omega) houtLt hAnd (by rwa [hg_eq]) (by rwa [hg_eq])
          · exact hHalfOr q N L C g hq hN hLcard hProj hAO (by omega) houtLt hOr (by rwa [hg_eq]) (by rwa [hg_eq])
        by_cases haHalf : N * (q + (1 : ℕ)) ≤ (2 : ℕ) *
            ∑ l : Fin N, {p ∈ L l | (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a Bool.false = Bool.true}.card
        · exact hFinish a ha_lt (fun A B hB hF => (hFalseAB A B hB hF).1) haHalf
        · exact hFinish b hb_lt (fun A B hB hF => (hFalseAB A B hB hF).2) (by omega)
