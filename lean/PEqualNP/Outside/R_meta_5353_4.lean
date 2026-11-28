import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5353_4
    (hOneClean :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ),
        have w : ℕ → Finset (Fin N) → Finset (Fin N) → Bool := fun k A B => (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD k Bool.false;
        (350 : ℕ) ≤ q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, (L l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        u < C.output ∧ C.output < N + N + C.size →
        (∀ l : Fin N, ∀ p ∈ L l, w u {p} {l} = Bool.true) →
        (∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B → w u A B = Bool.false) →
        N * (q - (349 : ℕ)) ≤ (100 : ℕ) * C.size - (349 : ℕ) * N)
    (hBothDirty :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        have w : ℕ → Finset (Fin N) → Finset (Fin N) → Bool := fun k A B => (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD k Bool.false;
        (350 : ℕ) ≤ q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, (L l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        a < C.output ∧ b < C.output ∧ C.output < N + N + C.size →
        (∀ l : Fin N, ∀ p ∈ L l, w a {p} {l} = Bool.true ∧ w b {p} {l} = Bool.true) →
        (∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B → w a A B = Bool.false ∨ w b A B = Bool.false) →
        (∃ A B : Finset (Fin N), B.card ≤ q ∧ PEqualNP.GenericRejection.IsFalseInput L A B ∧ w a A B = Bool.true) →
        (∃ A B : Finset (Fin N), B.card ≤ q ∧ PEqualNP.GenericRejection.IsFalseInput L A B ∧ w b A B = Bool.true) →
        N * (q - (349 : ℕ)) ≤ (100 : ℕ) * C.size - (349 : ℕ) * N) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (350 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * (x1 - (349 : ℕ)) ≤ (100 : ℕ) * x4.size - (349 : ℕ) * x2 := by
  classical
  intro q N L C hq hN hLcard hProj hAO houtGe houtLt hOutAnd hRight hFalse
  obtain ⟨g, hgSome, hgop⟩ := hOutAnd
  let k : ℕ := C.output - (N + N)
  have hk_lt : k < C.gates.length := by
    change C.output - (N + N) < C.size
    omega
  have hg_eq : C.gates[k]'hk_lt = g := by
    rw [List.getElem?_eq_getElem hk_lt] at hgSome
    exact Option.some.inj hgSome
  have hg_mem : g ∈ C.gates := by
    rw [← hg_eq]
    exact List.getElem_mem hk_lt
  have hlen2 : g.inputs.length = 2 := hAO.2.2 g hg_mem
  cases hinp : g.inputs with
  | nil => rw [hinp] at hlen2; simp at hlen2
  | cons a rest =>
    cases rest with
    | nil => rw [hinp] at hlen2; simp at hlen2
    | cons b tail =>
      cases tail with
      | cons _ _ => rw [hinp] at hlen2; simp at hlen2
      | nil =>
        have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
          change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g
          rw [List.getD_eq_getElem _ _ hk_lt, hg_eq]
        have ha_lt : a < C.output := by
          have h1 := hAO.2.1 k hk_lt a (by rw [hga, hinp]; simp)
          omega
        have hb_lt : b < C.output := by
          have h1 := hAO.2.1 k hk_lt b (by rw [hga, hinp]; simp)
          omega
        have hEvalAnd : ∀ x : List Bool, x.length = N + N →
            C.eval x = ((C.wires x).getD a Bool.false && (C.wires x).getD b Bool.false) := by
          intro x hxlen
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
          have hsplit : C.gates = C.gates.take k ++ g :: C.gates.drop (k + 1) := by
            have h1 := (List.take_append_drop k C.gates).symm
            have h2 : C.gates.drop k = g :: C.gates.drop (k + 1) := by
              rw [← hg_eq]
              exact List.drop_eq_getElem_cons hk_lt
            rw [h2] at h1
            exact h1
          let w0 := (C.gates.take k).foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) x
          have hw0_len : w0.length = C.output := by
            have h1 := hfold_len (C.gates.take k) x
            rw [hxlen, List.length_take, Nat.min_eq_left (le_of_lt hk_lt)] at h1
            change w0.length = N + N + k at h1
            omega
          let bval := g.op.eval (g.inputs.map fun i => w0.getD i false)
          have hbval : bval = (w0.getD a false && w0.getD b false) := by
            dsimp only [bval]
            rw [hgop, hinp, List.map_cons, List.map_cons, List.map_nil]
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
        have hRightAB : ∀ l : Fin N, ∀ p ∈ L l,
            (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a Bool.false = Bool.true ∧
            (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b Bool.false = Bool.true := by
          intro l p hp
          have h1 := hRight l p hp
          rw [hEvalAnd _ (hLenInc {p} {l}), Bool.and_eq_true] at h1
          exact h1
        have hFalseAB : ∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B →
            (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD a Bool.false = Bool.false ∨
            (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD b Bool.false = Bool.false := by
          intro A B hB hF
          have h1 := hFalse A B hB hF
          rw [hEvalAnd _ (hLenInc A B), Bool.and_eq_false_iff] at h1
          exact h1
        by_cases haClean : ∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B →
            (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD a Bool.false = Bool.false
        · exact hOneClean q N L C a hq hN hLcard hProj hAO ⟨ha_lt, houtLt⟩
            (fun l p hp => (hRightAB l p hp).1) haClean
        · by_cases hbClean : ∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B →
              (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD b Bool.false = Bool.false
          · exact hOneClean q N L C b hq hN hLcard hProj hAO ⟨hb_lt, houtLt⟩
              (fun l p hp => (hRightAB l p hp).2) hbClean
          · push Not at haClean hbClean
            have haD : ∃ A B : Finset (Fin N), B.card ≤ q ∧ PEqualNP.GenericRejection.IsFalseInput L A B ∧
                (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD a Bool.false = Bool.true := by
              obtain ⟨A, B, hB, hF, hne⟩ := haClean
              exact ⟨A, B, hB, hF, Bool.eq_true_of_not_eq_false hne⟩
            have hbD : ∃ A B : Finset (Fin N), B.card ≤ q ∧ PEqualNP.GenericRejection.IsFalseInput L A B ∧
                (C.wires (PEqualNP.GenericRejection.incidenceInput A B)).getD b Bool.false = Bool.true := by
              obtain ⟨A, B, hB, hF, hne⟩ := hbClean
              exact ⟨A, B, hB, hF, Bool.eq_true_of_not_eq_false hne⟩
            exact hBothDirty q N L C a b hq hN hLcard hProj hAO ⟨ha_lt, hb_lt, houtLt⟩
              hRightAB hFalseAB haD hbD
