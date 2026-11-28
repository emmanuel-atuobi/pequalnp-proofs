import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_9059_1
    (hTopAndHasAndChild :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : DecidableRel x3) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (wa wb : ℕ) (ga : PEqualNP.CircuitLowerBounds.Gate),
        (400 : ℕ) ≤ x1 ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
        PEqualNP.MetaComplexity.Monotone2 x5 →
        x2 + x2 ≤ wa ∧ wa < x5.output ∧ x2 + x2 ≤ wb ∧ wb < x5.output ∧ wa ≠ wb ∧ x5.output < x2 + x2 + x5.size →
        x5.gates[wa - (x2 + x2)]? = Option.some ga ∧ ga.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) →
        (∀ (x15 x16 : Fin x2), x3 x15 x16 →
          (x5.wires (List.ofFn fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16))).getD wa Bool.false = Bool.true ∧
          (x5.wires (List.ofFn fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16))).getD wb Bool.false = Bool.true) →
        (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → ((x5.wires (List.ofFn x16)).getD wa Bool.false && (x5.wires (List.ofFn x16)).getD wb Bool.false) = Bool.false) →
        x2 * x1 ≤ (100 : ℕ) * x5.size)
    (hTopAndBothOr :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : DecidableRel x3) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (w1 w2 : ℕ) (g1 g2 : PEqualNP.CircuitLowerBounds.Gate),
        (400 : ℕ) ≤ x1 ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
        PEqualNP.MetaComplexity.Monotone2 x5 →
        x2 + x2 ≤ w1 ∧ w1 < w2 ∧ w2 < x5.output ∧ x5.output < x2 + x2 + x5.size →
        x5.gates[w1 - (x2 + x2)]? = Option.some g1 ∧ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x5.gates[w2 - (x2 + x2)]? = Option.some g2 ∧ g2.op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) →
        (∀ (x15 x16 : Fin x2), x3 x15 x16 →
          (x5.wires (List.ofFn fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16))).getD w1 Bool.false = Bool.true ∧
          (x5.wires (List.ofFn fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16))).getD w2 Bool.false = Bool.true) →
        (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → ((x5.wires (List.ofFn x16)).getD w1 Bool.false && (x5.wires (List.ofFn x16)).getD w2 Bool.false) = Bool.false) →
        x2 * x1 ≤ (100 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : DecidableRel x3) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (400 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → (∃ (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[(1 : ℕ)]? = Option.some x17) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N R hDec C hq hN hCard hUniq hM hoGe hoLt hTop hBin hInc hRej _
  have hN2 : 2 ≤ N := by
    have hq2 : 1 ≤ q ^ 2 := by
      have : 1 * 1 ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
      simpa only [sq] using this
    rw [hN]
    omega
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl step init).length = init.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro init; simp
    | cons hd tl ih =>
      intro init
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [step, List.length_append, List.length_singleton]
      omega
  have hfold_pref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (j : ℕ),
      j < init.length →
      (gs.foldl step init).getD j false = init.getD j false := by
    intro gs
    induction gs with
    | nil => intro init j _; rfl
    | cons hd tl ih =>
      intro init j hj
      simp only [List.foldl_cons]
      rw [ih _ j (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ hj
  obtain ⟨g0, hg0_some, hg0_and⟩ := hTop
  obtain ⟨w1, w2, hg0_inp, hw12, hw2_lt⟩ := hBin (C.output - (N + N)) g0 hg0_some
  let k : ℕ := C.output - (N + N)
  have hk_lt : k < C.gates.length := by change C.output - (N + N) < C.size; omega
  have hw2_out : w2 < C.output := by omega
  have hw1_out : w1 < C.output := by omega
  have hg0_eq : C.gates[k]'hk_lt = g0 := by
    have h1 : C.gates[k]? = Option.some (C.gates[k]'hk_lt) := List.getElem?_eq_getElem hk_lt
    rw [h1] at hg0_some
    exact Option.some.inj hg0_some
  have hEvalOut : ∀ f : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C f =
      ((C.wires (List.ofFn f)).getD w1 Bool.false && (C.wires (List.ofFn f)).getD w2 Bool.false) := by
    intro f
    let x := List.ofFn f
    have hxlen : x.length = N + N := List.length_ofFn
    have hsplit : C.gates = C.gates.take k ++ g0 :: C.gates.drop (k + 1) := by
      have h1 := (List.take_append_drop k C.gates).symm
      have h2 : C.gates.drop k = g0 :: C.gates.drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hk_lt, hg0_eq]
      rw [h2] at h1
      exact h1
    let w0 := (C.gates.take k).foldl step x
    have hw0_len : w0.length = C.output := by
      have h1 := hfold_len (C.gates.take k) x
      rw [hxlen, List.length_take, Nat.min_eq_left (le_of_lt hk_lt)] at h1
      change w0.length = N + N + k at h1
      omega
    let bval := g0.op.eval (g0.inputs.map fun i => w0.getD i false)
    have hw_eq : C.wires x = (C.gates.drop (k + 1)).foldl step (w0 ++ [bval]) := by
      change C.gates.foldl step x = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hw_out : (C.wires x).getD C.output false = bval := by
      rw [hw_eq, hfold_pref _ _ C.output (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [hw0_len, Nat.sub_self, List.getD_cons_zero]
    have hw_1 : (C.wires x).getD w1 false = w0.getD w1 false := by
      rw [hw_eq, hfold_pref _ _ w1 (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
      exact List.getD_append _ _ _ _ (by omega)
    have hw_2 : (C.wires x).getD w2 false = w0.getD w2 false := by
      rw [hw_eq, hfold_pref _ _ w2 (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
      exact List.getD_append _ _ _ _ (by omega)
    have hAndEval : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [u, v] = (u && v) := by
      intro u v; cases u <;> cases v <;> rfl
    change (C.wires x).getD C.output false = ((C.wires x).getD w1 false && (C.wires x).getD w2 false)
    rw [hw_out, hw_1, hw_2]
    dsimp only [bval]
    rw [hg0_and, hg0_inp, List.map_cons, List.map_cons, List.map_nil, hAndEval]
  have hInc12 : ∀ (p l : Fin N), R p l →
      (C.wires (List.ofFn fun (x18 : Fin (N + N)) => Decidable.decide (x18 = Fin.castAdd N p ∨ x18 = Fin.natAdd N l))).getD w1 Bool.false = Bool.true ∧
      (C.wires (List.ofFn fun (x18 : Fin (N + N)) => Decidable.decide (x18 = Fin.castAdd N p ∨ x18 = Fin.natAdd N l))).getD w2 Bool.false = Bool.true := by
    intro p l hpl
    have h1 := hInc p l hpl
    rw [hEvalOut, Bool.and_eq_true] at h1
    exact h1
  have hRej12 : ∀ (x16 : Fin (N + N) → Bool),
      Fintype.card { x17 : Fin N // x16 (Fin.natAdd N x17) = Bool.true } ≤ q →
      (¬∃ (x18 x19 : Fin N), R x18 x19 ∧ x16 (Fin.castAdd N x18) = Bool.true ∧ x16 (Fin.natAdd N x19) = Bool.true) →
      ((C.wires (List.ofFn x16)).getD w1 Bool.false && (C.wires (List.ofFn x16)).getD w2 Bool.false) = Bool.false := by
    intro x16 hle hno
    have h1 := hRej x16 hle hno
    rw [hEvalOut] at h1
    exact h1
  have hIncGe : ∀ w : ℕ,
      (∀ (p l : Fin N), R p l →
        (C.wires (List.ofFn fun (x18 : Fin (N + N)) => Decidable.decide (x18 = Fin.castAdd N p ∨ x18 = Fin.natAdd N l))).getD w Bool.false = Bool.true) →
      N + N ≤ w := by
    intro w hw
    by_contra hlt
    have hlt : w < N + N := Nat.lt_of_not_ge hlt
    by_cases hwN : w < N
    · let p0 : Fin N := ⟨w, hwN⟩
      let l0 : Fin N := ⟨0, by omega⟩
      have hExOtherP : ∃ p1 : Fin N, R p1 l0 ∧ p1 ≠ p0 := by
        by_contra hnone
        have hsub : ∀ s : { p : Fin N // R p l0 }, s.1 = p0 := by
          intro s
          by_contra hne
          exact hnone ⟨s.1, s.2, hne⟩
        have hinj : Function.Injective (fun _ : { p : Fin N // R p l0 } => (() : Unit)) := by
          intro a b _
          exact Subtype.ext ((hsub a).trans (hsub b).symm)
        have hle := Fintype.card_le_of_injective _ hinj
        simp only [Fintype.card_unit, hCard l0] at hle
        omega
      obtain ⟨p1, hp1, hne1⟩ := hExOtherP
      have ht := hw p1 l0 hp1
      change (C.gates.foldl step (List.ofFn _)).getD w false = true at ht
      rw [hfold_pref _ _ w (by simp only [List.length_ofFn]; exact hlt)] at ht
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn] at ht
      simp only [decide_eq_true_eq] at ht
      rcases ht with hEqP | hEqL
      · have hv := congrArg Fin.val hEqP
        simp only [Fin.val_castAdd] at hv
        exact hne1 (Fin.ext hv.symm)
      · have hv := congrArg Fin.val hEqL
        simp only [Fin.val_natAdd] at hv
        omega
    · let l0 : Fin N := ⟨w - N, by omega⟩
      let l1 : Fin N := if l0.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hneL : l1 ≠ l0 := by
        intro heq
        have hv := congrArg Fin.val heq
        by_cases h0 : l0.val = 0
        · simp only [l1, h0, ↓reduceIte] at hv; omega
        · exact h0 (by simpa only [l1, h0, ↓reduceIte] using hv.symm)
      have hExP : ∃ p1 : Fin N, R p1 l1 := by
        have hpos : 0 < Fintype.card { p : Fin N // R p l1 } := by rw [hCard l1]; omega
        obtain ⟨s⟩ := Fintype.card_pos_iff.mp hpos
        exact ⟨s.1, s.2⟩
      obtain ⟨p1, hp1⟩ := hExP
      have ht := hw p1 l1 hp1
      change (C.gates.foldl step (List.ofFn _)).getD w false = true at ht
      rw [hfold_pref _ _ w (by simp only [List.length_ofFn]; exact hlt)] at ht
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn] at ht
      simp only [decide_eq_true_eq] at ht
      rcases ht with hEqP | hEqL
      · have hv := congrArg Fin.val hEqP
        simp only [Fin.val_castAdd] at hv
        omega
      · have hv := congrArg Fin.val hEqL
        simp only [Fin.val_natAdd] at hv
        exact hneL (Fin.ext (by simp only [l0]; omega))
  have hw1Ge : N + N ≤ w1 := hIncGe w1 (fun p l hpl => (hInc12 p l hpl).1)
  have hw2Ge : N + N ≤ w2 := by omega
  have hk1_lt : w1 - (N + N) < C.gates.length := by change w1 - (N + N) < C.size; omega
  have hk2_lt : w2 - (N + N) < C.gates.length := by change w2 - (N + N) < C.size; omega
  let g1 : PEqualNP.CircuitLowerBounds.Gate := C.gates[w1 - (N + N)]'hk1_lt
  let g2 : PEqualNP.CircuitLowerBounds.Gate := C.gates[w2 - (N + N)]'hk2_lt
  have hg1_some : C.gates[w1 - (N + N)]? = Option.some g1 := List.getElem?_eq_getElem hk1_lt
  have hg2_some : C.gates[w2 - (N + N)]? = Option.some g2 := List.getElem?_eq_getElem hk2_lt
  rcases (hM g1 (List.getElem_mem hk1_lt)).1 with hg1_and | hg1_or
  · exact hTopAndHasAndChild q N R hDec C w1 w2 g1 ⟨hq, hN⟩ hCard hUniq hM
      ⟨hw1Ge, hw1_out, hw2Ge, hw2_out, by omega, hoLt⟩ ⟨hg1_some, hg1_and⟩ hBin hInc12 hRej12
  · rcases (hM g2 (List.getElem_mem hk2_lt)).1 with hg2_and | hg2_or
    · have hInc21 : ∀ (p l : Fin N), R p l →
          (C.wires (List.ofFn fun (x18 : Fin (N + N)) => Decidable.decide (x18 = Fin.castAdd N p ∨ x18 = Fin.natAdd N l))).getD w2 Bool.false = Bool.true ∧
          (C.wires (List.ofFn fun (x18 : Fin (N + N)) => Decidable.decide (x18 = Fin.castAdd N p ∨ x18 = Fin.natAdd N l))).getD w1 Bool.false = Bool.true :=
        fun p l hpl => ⟨(hInc12 p l hpl).2, (hInc12 p l hpl).1⟩
      have hRej21 : ∀ (x16 : Fin (N + N) → Bool),
          Fintype.card { x17 : Fin N // x16 (Fin.natAdd N x17) = Bool.true } ≤ q →
          (¬∃ (x18 x19 : Fin N), R x18 x19 ∧ x16 (Fin.castAdd N x18) = Bool.true ∧ x16 (Fin.natAdd N x19) = Bool.true) →
          ((C.wires (List.ofFn x16)).getD w2 Bool.false && (C.wires (List.ofFn x16)).getD w1 Bool.false) = Bool.false := by
        intro x16 hle hno
        rw [Bool.and_comm]
        exact hRej12 x16 hle hno
      exact hTopAndHasAndChild q N R hDec C w2 w1 g2 ⟨hq, hN⟩ hCard hUniq hM
        ⟨hw2Ge, hw2_out, hw1Ge, hw1_out, by omega, hoLt⟩ ⟨hg2_some, hg2_and⟩ hBin hInc21 hRej21
    · exact hTopAndBothOr q N R hDec C w1 w2 g1 g2 ⟨hq, hN⟩ hCard hUniq hM
        ⟨hw1Ge, hw12, hw2_out, hoLt⟩ ⟨hg1_some, hg1_or, hg2_some, hg2_or⟩ hBin hInc12 hRej12
