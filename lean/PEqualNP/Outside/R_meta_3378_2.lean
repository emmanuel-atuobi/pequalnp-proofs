import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3378_2
    (hOutAnd :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        (300 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
        x2 + x2 ≤ x4.output →
        x4.output < x2 + x2 + x4.size →
        x2 + x2 ≤ a ∧ a < x4.output ∧ x2 + x2 ≤ b ∧ b < x4.output →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (x2 + x2))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (x2 + x2))).inputs = [a, b] →
        (∀ (l : Fin x2), ∀ p ∈ x3 l,
          PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {p} {l}) a = Bool.true ∧
          PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {p} {l}) b = Bool.true) →
        (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) →
        x2 * x1 ≤ (100 : ℕ) * x4.size)
    (hOutOr :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        (300 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
        x2 + x2 ≤ x4.output →
        x4.output < x2 + x2 + x4.size →
        x2 + x2 ≤ a ∧ a < x4.output ∧ x2 + x2 ≤ b ∧ b < x4.output →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (x2 + x2))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (x2 + x2))).inputs = [a, b] →
        PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
        (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 →
          PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x12 x13) a = Bool.false ∧
          PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x12 x13) b = Bool.false) →
        x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q N L C hq hN hLcard hProj hAO houtLt hRight hSafeOut
  have hN2 : 2 ≤ N := by
    have hq2 : 1 ≤ q ^ 2 := by
      have : 1 * 1 ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
      simpa only [sq] using this
    rw [hN]
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
  have hLenInc : ∀ A B : Finset (Fin N), (PEqualNP.GenericRejection.incidenceInput A B).length = N + N := by
    intro A B
    change (List.ofFn (fun i : Fin N => decide (i ∈ A)) ++ List.ofFn (fun j : Fin N => decide (j ∈ B))).length = N + N
    simp only [List.length_append, List.length_ofFn]
  have hWireLt : ∀ (A B : Finset (Fin N)) (j : ℕ), j < N + N →
      PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput A B) j =
      (PEqualNP.GenericRejection.incidenceInput A B).getD j Bool.false := by
    intro A B j hj
    exact hfold_pref C.gates (PEqualNP.GenericRejection.incidenceInput A B) j (by rw [hLenInc A B]; exact hj)
  have hSafeGe : ∀ w : ℕ,
      (∀ (A B : Finset (Fin N)), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B →
        PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput A B) w = Bool.false) →
      N + N ≤ w := by
    intro w hsw
    by_contra hlt
    have hlt : w < N + N := Nat.lt_of_not_ge hlt
    by_cases hwN : w < N
    · let p0 : Fin N := ⟨w, hwN⟩
      have hf := hsw {p0} ∅ (by simp) (fun l hl => False.elim (Finset.notMem_empty l hl))
      rw [hWireLt {p0} ∅ w hlt] at hf
      change (List.ofFn (fun i : Fin N => decide (i ∈ ({p0} : Finset (Fin N)))) ++
        List.ofFn (fun j : Fin N => decide (j ∈ (∅ : Finset (Fin N))))).getD w false = false at hf
      rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hwN)] at hf
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hwN)] at hf
      simp only [List.getElem_ofFn, Finset.mem_singleton, decide_eq_true_eq] at hf
      have heq : (⟨w, hwN⟩ : Fin N) = p0 := rfl
      rw [heq] at hf
      simp at hf
    · let l0 : Fin N := ⟨w - N, by omega⟩
      have hf := hsw ∅ {l0} (by simp only [Finset.card_singleton]; omega)
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
  have hRightGe : ∀ w : ℕ,
      (∀ (l : Fin N), ∀ p ∈ L l, PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) w = Bool.true) →
      N + N ≤ w := by
    intro w hrw
    by_contra hlt
    have hlt : w < N + N := Nat.lt_of_not_ge hlt
    by_cases hwN : w < N
    · let p0 : Fin N := ⟨w, hwN⟩
      let l0 : Fin N := ⟨0, by omega⟩
      have hsub : L l0 ⊆ {p0} := by
        intro p hp
        have ht := hrw l0 p hp
        rw [hWireLt {p} {l0} w hlt] at ht
        change (List.ofFn (fun i : Fin N => decide (i ∈ ({p} : Finset (Fin N)))) ++
          List.ofFn (fun j : Fin N => decide (j ∈ ({l0} : Finset (Fin N))))).getD w false = true at ht
        rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hwN)] at ht
        rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hwN)] at ht
        simp only [List.getElem_ofFn, Finset.mem_singleton, decide_eq_true_eq] at ht
        exact Finset.mem_singleton.mpr ht.symm
      have hc1 := Finset.card_le_card hsub
      simp only [Finset.card_singleton, hLcard l0] at hc1
      omega
    · let l0 : Fin N := ⟨w - N, by omega⟩
      let l1 : Fin N := if l0.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hne : l1 ≠ l0 := by
        intro heq
        have hv := congrArg Fin.val heq
        by_cases h0 : l0.val = 0
        · simp only [l1, h0, ↓reduceIte] at hv; omega
        · exact h0 (by simpa only [l1, h0, ↓reduceIte] using hv.symm)
      obtain ⟨p1, hp1⟩ := Finset.card_pos.mp (by rw [hLcard l1]; omega)
      have ht := hrw l1 p1 hp1
      rw [hWireLt {p1} {l1} w hlt] at ht
      change (List.ofFn (fun i : Fin N => decide (i ∈ ({p1} : Finset (Fin N)))) ++
        List.ofFn (fun j : Fin N => decide (j ∈ ({l1} : Finset (Fin N))))).getD w false = true at ht
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)] at ht
      have hidx : w - (List.ofFn (fun i : Fin N => decide (i ∈ ({p1} : Finset (Fin N))))).length <
          (List.ofFn (fun j : Fin N => decide (j ∈ ({l1} : Finset (Fin N))))).length := by
        simp only [List.length_ofFn]
        omega
      rw [List.getD_eq_getElem _ _ hidx] at ht
      simp only [List.getElem_ofFn, List.length_ofFn, Finset.mem_singleton, decide_eq_true_eq] at ht
      have heq : (⟨w - N, by omega⟩ : Fin N) = l0 := rfl
      rw [heq] at ht
      exact hne ht.symm
  have houtGe : N + N ≤ C.output := hSafeGe C.output (fun A B hB hF => hSafeOut A B hB hF)
  let k : ℕ := C.output - (N + N)
  have hk_lt : k < C.gates.length := by change C.output - (N + N) < C.size; omega
  let g0 : PEqualNP.CircuitLowerBounds.Gate := C.gates[k]'hk_lt
  have hga0 : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g0 := by
    change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g0
    rw [List.getD_eq_getElem _ _ hk_lt]
  have hg0_mem : g0 ∈ C.gates := List.getElem_mem hk_lt
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
        have ha_lt : a < C.output := by
          have h1 := hAO.2.1 k hk_lt a (by rw [hga0, hinp]; simp)
          omega
        have hb_lt : b < C.output := by
          have h1 := hAO.2.1 k hk_lt b (by rw [hga0, hinp]; simp)
          omega
        have hEvalOut : ∀ x : List Bool, x.length = N + N →
            PEqualNP.CircuitLowerBounds.wireValue C x C.output =
            g0.op.eval [PEqualNP.CircuitLowerBounds.wireValue C x a, PEqualNP.CircuitLowerBounds.wireValue C x b] := by
          intro x hxlen
          have hsplit : C.gates = C.gates.take k ++ g0 :: C.gates.drop (k + 1) := by
            have h1 := (List.take_append_drop k C.gates).symm
            have h2 : C.gates.drop k = g0 :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk_lt
            rw [h2] at h1
            exact h1
          let w0 := (C.gates.take k).foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) x
          have hw0_len : w0.length = C.output := by
            have h1 := hfold_len (C.gates.take k) x
            rw [hxlen, List.length_take, Nat.min_eq_left (le_of_lt hk_lt)] at h1
            change w0.length = N + N + k at h1
            omega
          let bval := g0.op.eval (g0.inputs.map fun i => w0.getD i false)
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
          change (C.wires x).getD C.output false = g0.op.eval [(C.wires x).getD a false, (C.wires x).getD b false]
          rw [hw_out, hw_a, hw_b]
          dsimp only [bval]
          rw [hinp, List.map_cons, List.map_cons, List.map_nil]
        have hga_inp : (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [a, b] := by
          rw [hga0, hinp]
        rcases hAO.1 g0 hg0_mem with hAnd | hOr
        · have hAndEval : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [u, v] = (u && v) := by
            intro u v; cases u <;> cases v <;> rfl
          have hRightAB : ∀ (l : Fin N), ∀ p ∈ L l,
              PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) a = Bool.true ∧
              PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) b = Bool.true := by
            intro l p hp
            have h1 := hRight l p hp
            change PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) C.output = true at h1
            rw [hEvalOut _ (hLenInc {p} {l}), hAnd, hAndEval, Bool.and_eq_true] at h1
            exact h1
          have haGe : N + N ≤ a := hRightGe a (fun l p hp => (hRightAB l p hp).1)
          have hbGe : N + N ≤ b := hRightGe b (fun l p hp => (hRightAB l p hp).2)
          exact hOutAnd q N L C a b hq hN hLcard hProj hAO houtGe houtLt ⟨haGe, ha_lt, hbGe, hb_lt⟩
            (by rw [hga0]; exact hAnd) hga_inp hRightAB hSafeOut
        · have hOrEval : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [u, v] = (u || v) := by
            intro u v; cases u <;> cases v <;> rfl
          have hSafeAB : ∀ (A B : Finset (Fin N)), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B →
              PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput A B) a = Bool.false ∧
              PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput A B) b = Bool.false := by
            intro A B hB hF
            have h1 := hSafeOut A B hB hF
            change PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput A B) C.output = false at h1
            rw [hEvalOut _ (hLenInc A B), hOr, hOrEval, Bool.or_eq_false_iff] at h1
            exact h1
          have haGe : N + N ≤ a := hSafeGe a (fun A B hB hF => (hSafeAB A B hB hF).1)
          have hbGe : N + N ≤ b := hSafeGe b (fun A B hB hF => (hSafeAB A B hB hF).2)
          exact hOutOr q N L C a b hq hN hLcard hProj hAO houtGe houtLt ⟨haGe, ha_lt, hbGe, hb_lt⟩
            (by rw [hga0]; exact hOr) hga_inp hRight hSafeAB
