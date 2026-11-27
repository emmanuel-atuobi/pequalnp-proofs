import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18796_3
    (hTopAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (w a b : ℕ),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (26 : ℕ) ≤ w →
        w < (26 : ℕ) + x1.size →
        (26 : ℕ) ≤ a ∧ a < w ∧ (26 : ℕ) ≤ b ∧ b < w →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (w - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (w - (26 : ℕ))).inputs = [a, b] →
        have Good : ℕ → Prop := fun u =>
          ∀ (x3 : Fin (26 : ℕ) → Bool), x3 (0 : Fin (26 : ℕ)) = Bool.false →
            ((x1.wires (List.ofFn x3)).getD u Bool.false = Bool.true ↔
              ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)),
                x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧
                x3 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧
                x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true);
        Good w →
        (∀ u < w, ¬Good u) →
        (59 : ℕ) ≤ x1.size)
    (hTopOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (w a b : ℕ),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (26 : ℕ) ≤ w →
        w < (26 : ℕ) + x1.size →
        (26 : ℕ) ≤ a ∧ a < w ∧ (26 : ℕ) ≤ b ∧ b < w →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (w - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (w - (26 : ℕ))).inputs = [a, b] →
        have Good : ℕ → Prop := fun u =>
          ∀ (x3 : Fin (26 : ℕ) → Bool), x3 (0 : Fin (26 : ℕ)) = Bool.false →
            ((x1.wires (List.ofFn x3)).getD u Bool.false = Bool.true ↔
              ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)),
                x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧
                x3 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧
                x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true);
        Good w →
        (∀ u < w, ¬Good u) →
        (59 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x3 (0 : Fin (26 : ℕ)) = Bool.false → (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧ x3 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true)) → (59 : ℕ) ≤ x1.size := by
  classical
  intro C hAO hSpec
  have hDiag : ∀ p : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 p := by decide
  have hLineNZ : ∀ l : Fin 13, ∃ p : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ p ≠ 0 := by decide
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
  have hWireLt : ∀ (x : Fin 26 → Bool) (j : ℕ) (hj : j < 26),
      (C.wires (List.ofFn x)).getD j false = x ⟨j, hj⟩ := by
    intro x j hj
    have h1 := hfold_pref C.gates (List.ofFn x) j (by simp only [List.length_ofFn]; exact hj)
    change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD j false = x ⟨j, hj⟩
    rw [h1, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hj), List.getElem_ofFn]
  let Good : ℕ → Prop := fun u =>
    ∀ (x3 : Fin 26 → Bool), x3 0 = Bool.false →
      ((C.wires (List.ofFn x3)).getD u Bool.false = Bool.true ↔
        ∃ (x5 : Fin 13) (x6 : Fin 13),
          x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧
          x3 (Fin.castAdd 13 x5) = Bool.true ∧
          x3 (Fin.natAdd 13 x6) = Bool.true)
  have hGoodOut : Good C.output := hSpec
  have houtLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 (1 : Fin 13) ∨ i = Fin.natAdd 13 (1 : Fin 13))
    have hx0 : x 0 = false := by decide
    have ht : (C.wires (List.ofFn x)).getD C.output false = true :=
      (hGoodOut x hx0).mpr ⟨1, 1, hDiag 1, by decide, by decide⟩
    have hlen : (C.wires (List.ofFn x)).length = 26 + C.size := by
      change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x)).length = 26 + C.gates.length
      rw [hfold_len, List.length_ofFn]
    have hdf : (C.wires (List.ofFn x)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at ht
    exact Bool.noConfusion ht
  have hex : ∃ u, Good u := ⟨C.output, hGoodOut⟩
  let w : ℕ := Nat.find hex
  have hwGood : Good w := Nat.find_spec hex
  have hwLe : w ≤ C.output := Nat.find_min' hex hGoodOut
  have hwMin : ∀ u < w, ¬Good u := fun u hu => Nat.find_min hex hu
  have hwLt : w < 26 + C.size := lt_of_le_of_lt hwLe houtLt
  have hRejGe : ∀ u : ℕ, u ≠ 0 →
      (∀ (x : Fin 26 → Bool), x 0 = false →
        (¬∃ (p l : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (C.wires (List.ofFn x)).getD u false = false) →
      26 ≤ u := by
    intro u hu0 hrej
    by_contra hlt
    have hlt : u < 26 := Nat.lt_of_not_ge hlt
    let idx : Fin 26 := ⟨u, hlt⟩
    let x : Fin 26 → Bool := fun i => decide (i = idx)
    have hx0 : x 0 = false := by
      simp only [x, decide_eq_false_iff_not]
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero] at hv
      exact hu0 hv.symm
    have hno : ¬∃ (p l : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
      rintro ⟨p, l, _, hp, hl⟩
      simp only [x, decide_eq_true_eq] at hp hl
      have hv := congrArg Fin.val (hp.trans hl.symm)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    have hf := hrej x hx0 hno
    rw [hWireLt x u hlt] at hf
    have heq : (⟨u, hlt⟩ : Fin 26) = idx := rfl
    simp only [x, heq, decide_true] at hf
    exact Bool.noConfusion hf
  have hAccGe : ∀ u : ℕ,
      (∀ (x : Fin 26 → Bool), x 0 = false →
        (∃ (p l : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (C.wires (List.ofFn x)).getD u false = true) →
      26 ≤ u := by
    intro u hacc
    by_contra hlt
    have hlt : u < 26 := Nat.lt_of_not_ge hlt
    by_cases h13 : u < 13
    · let p : Fin 13 := if u = 1 then 2 else 1
      let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 p)
      have hpne0 : p ≠ 0 := by
        by_cases h1 : u = 1 <;> simp only [p, h1, ↓reduceIte] <;> decide
      have hx0 : x 0 = false := by
        simp only [x, decide_eq_false_iff_not, not_or]
        constructor
        · intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_zero, Fin.val_castAdd] at hv
          exact hpne0 (Fin.ext hv.symm)
        · intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_zero, Fin.val_natAdd] at hv
          omega
      have ht := hacc x hx0 ⟨p, p, hDiag p, by simp [x], by simp [x]⟩
      rw [hWireLt x u hlt] at ht
      simp only [x, decide_eq_true_eq] at ht
      rcases ht with h1 | h2
      · have hv := congrArg Fin.val h1
        simp only [Fin.val_castAdd] at hv
        by_cases hu1 : u = 1
        · simp only [p, hu1, ↓reduceIte, Fin.val_two] at hv; omega
        · simp only [p, hu1, ↓reduceIte, Fin.val_one] at hv
      · have hv := congrArg Fin.val h2
        simp only [Fin.val_natAdd] at hv
        omega
    · let l : Fin 13 := if u = 13 then 1 else 0
      obtain ⟨p, hpl, hpne0⟩ := hLineNZ l
      let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      have hx0 : x 0 = false := by
        simp only [x, decide_eq_false_iff_not, not_or]
        constructor
        · intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_zero, Fin.val_castAdd] at hv
          exact hpne0 (Fin.ext hv.symm)
        · intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_zero, Fin.val_natAdd] at hv
          omega
      have ht := hacc x hx0 ⟨p, l, hpl, by simp [x], by simp [x]⟩
      rw [hWireLt x u hlt] at ht
      simp only [x, decide_eq_true_eq] at ht
      rcases ht with h1 | h2
      · have hv := congrArg Fin.val h1
        simp only [Fin.val_castAdd] at hv
        omega
      · have hv := congrArg Fin.val h2
        simp only [Fin.val_natAdd] at hv
        by_cases hu13 : u = 13
        · simp only [l, hu13, ↓reduceIte, Fin.val_one] at hv; omega
        · simp only [l, hu13, ↓reduceIte, Fin.val_zero] at hv
  have hwGe : 26 ≤ w := hAccGe w (fun x hx0 hex' => (hwGood x hx0).mpr hex')
  let k : ℕ := w - 26
  have hk_lt : k < C.gates.length := by change w - 26 < C.size; omega
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
        have ha_lt : a < w := by
          have h1 := hAO.2.1 k hk_lt a (by rw [hga0, hinp]; simp)
          omega
        have hb_lt : b < w := by
          have h1 := hAO.2.1 k hk_lt b (by rw [hga0, hinp]; simp)
          omega
        have hEvalW : ∀ x : List Bool, x.length = 26 →
            (C.wires x).getD w false =
            g0.op.eval [(C.wires x).getD a false, (C.wires x).getD b false] := by
          intro x hxlen
          have hsplit : C.gates = C.gates.take k ++ g0 :: C.gates.drop (k + 1) := by
            have h1 := (List.take_append_drop k C.gates).symm
            have h2 : C.gates.drop k = g0 :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk_lt
            rw [h2] at h1
            exact h1
          let w0 := (C.gates.take k).foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) x
          have hw0_len : w0.length = w := by
            have h1 := hfold_len (C.gates.take k) x
            rw [hxlen, List.length_take, Nat.min_eq_left (le_of_lt hk_lt)] at h1
            change w0.length = 26 + k at h1
            omega
          let bval := g0.op.eval (g0.inputs.map fun i => w0.getD i false)
          have hw_eq : C.wires x = (C.gates.drop (k + 1)).foldl
              (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (w0 ++ [bval]) := by
            change C.gates.foldl _ x = _
            conv_lhs => rw [hsplit]
            rw [List.foldl_append, List.foldl_cons]
          have hw_w : (C.wires x).getD w false = bval := by
            rw [hw_eq, hfold_pref _ _ w (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
            rw [List.getD_append_right _ _ _ _ (by omega)]
            simp only [hw0_len, Nat.sub_self, List.getD_cons_zero]
          have hw_a : (C.wires x).getD a false = w0.getD a false := by
            rw [hw_eq, hfold_pref _ _ a (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
            exact List.getD_append _ _ _ _ (by omega)
          have hw_b : (C.wires x).getD b false = w0.getD b false := by
            rw [hw_eq, hfold_pref _ _ b (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
            exact List.getD_append _ _ _ _ (by omega)
          rw [hw_w, hw_a, hw_b]
          dsimp only [bval]
          rw [hinp, List.map_cons, List.map_cons, List.map_nil]
        have hga_inp : (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [a, b] := by
          rw [hga0, hinp]
        rcases hAO.1 g0 hg0_mem with hAnd | hOr
        · have hAndEval : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [u, v] = (u && v) := by
            intro u v; cases u <;> cases v <;> rfl
          have haGe : 26 ≤ a := hAccGe a (fun x hx0 hex' => by
            have h1 := (hwGood x hx0).mpr hex'
            rw [hEvalW _ (by simp only [List.length_ofFn]), hAnd, hAndEval, Bool.and_eq_true] at h1
            exact h1.1)
          have hbGe : 26 ≤ b := hAccGe b (fun x hx0 hex' => by
            have h1 := (hwGood x hx0).mpr hex'
            rw [hEvalW _ (by simp only [List.length_ofFn]), hAnd, hAndEval, Bool.and_eq_true] at h1
            exact h1.2)
          exact hTopAnd C w a b hAO hwGe hwLt ⟨haGe, ha_lt, hbGe, hb_lt⟩ (by rw [hga0]; exact hAnd) hga_inp hwGood hwMin
        · have hOrEval : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [u, v] = (u || v) := by
            intro u v; cases u <;> cases v <;> rfl
          have haNe0 : a ≠ 0 := by
            intro ha0
            apply hwMin b hb_lt
            intro x hx0
            have hw_eq := hEvalW (List.ofFn x) (by simp only [List.length_ofFn])
            rw [hOr, hOrEval, ha0, hWireLt x 0 (by decide)] at hw_eq
            change (C.wires (List.ofFn x)).getD w false = (x 0 || (C.wires (List.ofFn x)).getD b false) at hw_eq
            rw [hx0, Bool.false_or] at hw_eq
            rw [← hw_eq]
            exact hwGood x hx0
          have hbNe0 : b ≠ 0 := by
            intro hb0
            apply hwMin a ha_lt
            intro x hx0
            have hw_eq := hEvalW (List.ofFn x) (by simp only [List.length_ofFn])
            rw [hOr, hOrEval, hb0, hWireLt x 0 (by decide)] at hw_eq
            change (C.wires (List.ofFn x)).getD w false = ((C.wires (List.ofFn x)).getD a false || x 0) at hw_eq
            rw [hx0, Bool.or_false] at hw_eq
            rw [← hw_eq]
            exact hwGood x hx0
          have haGe : 26 ≤ a := hRejGe a haNe0 (fun x hx0 hno => by
            have h1 : (C.wires (List.ofFn x)).getD w false = false := by
              cases hval : (C.wires (List.ofFn x)).getD w false
              · rfl
              · exact False.elim (hno ((hwGood x hx0).mp hval))
            rw [hEvalW _ (by simp only [List.length_ofFn]), hOr, hOrEval, Bool.or_eq_false_iff] at h1
            exact h1.1)
          have hbGe : 26 ≤ b := hRejGe b hbNe0 (fun x hx0 hno => by
            have h1 : (C.wires (List.ofFn x)).getD w false = false := by
              cases hval : (C.wires (List.ofFn x)).getD w false
              · rfl
              · exact False.elim (hno ((hwGood x hx0).mp hval))
            rw [hEvalW _ (by simp only [List.length_ofFn]), hOr, hOrEval, Bool.or_eq_false_iff] at h1
            exact h1.2)
          exact hTopOr C w a b hAO hwGe hwLt ⟨haGe, ha_lt, hbGe, hb_lt⟩ (by rw [hga0]; exact hOr) hga_inp hwGood hwMin
