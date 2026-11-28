import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17130_3
    (hOutAnd :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (200 : ℕ) ≤ x1 ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧ x1 % (2 : ℕ) = (0 : ℕ) →
        (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
        PEqualNP.MetaComplexity.Monotone2 x5 →
        x2 + x2 ≤ x5.output ∧ x5.output < x2 + x2 + x5.size →
        (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →
        (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
        have x13 : ℕ := (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length;
        (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ x13 ∧ (100 : ℕ) * x13 < x2 * x1 →
        x2 * x1 ≤ (100 : ℕ) * x5.size)
    (hOutOr :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (200 : ℕ) ≤ x1 ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧ x1 % (2 : ℕ) = (0 : ℕ) →
        (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
        PEqualNP.MetaComplexity.Monotone2 x5 →
        x2 + x2 ≤ x5.output ∧ x5.output < x2 + x2 + x5.size →
        (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →
        (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
        have x13 : ℕ := (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length;
        (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ x13 ∧ (100 : ℕ) * x13 < x2 * x1 →
        x2 * x1 ≤ (100 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → have x13 : ℕ := (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length; (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ x13 → (100 : ℕ) * x13 < x2 * x1 → x1 % (2 : ℕ) = (0 : ℕ) → x2 * x1 - (100 : ℕ) * x13 ≤ (100 : ℕ) * (List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => !x17.op.eval [Bool.true, Bool.false]) x5.gates).length := by
  intro q N R hDec C hq hN hCard hUniq hM hInc hRej
  dsimp only
  intro hOrLo hOrHi hEven
  have hN1 : 1 ≤ N := by
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
  have hFilterSum : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (p : PEqualNP.CircuitLowerBounds.Gate → Bool),
      (gs.filter p).length + (gs.filter (fun g => !p g)).length = gs.length := by
    intro gs p
    induction gs with
    | nil => simp
    | cons hd tl ih =>
      cases h : p hd <;> simp only [List.filter_cons, h, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
  have hOutLt : C.output < N + N + C.size := by
    by_contra hge
    have hge : N + N + C.size ≤ C.output := Nat.le_of_not_lt hge
    let l0 : Fin N := ⟨0, by omega⟩
    have hpos : 0 < Fintype.card { p : Fin N // R p l0 } := by rw [hCard l0]; omega
    obtain ⟨s⟩ := Fintype.card_pos_iff.mp hpos
    have hT := hInc s.1 l0 s.2
    change (C.gates.foldl step (List.ofFn _)).getD C.output false = true at hT
    have hlen : (C.gates.foldl step (List.ofFn fun (x14 : Fin (N + N)) => Decidable.decide (x14 = Fin.castAdd N s.1 ∨ x14 = Fin.natAdd N l0))).length = N + N + C.size := by
      rw [hfold_len, List.length_ofFn]
      rfl
    have hF : (C.gates.foldl step (List.ofFn fun (x14 : Fin (N + N)) => Decidable.decide (x14 = Fin.castAdd N s.1 ∨ x14 = Fin.natAdd N l0))).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hF] at hT
    exact Bool.noConfusion hT
  have hOutGe : N + N ≤ C.output := by
    by_contra hlt
    have hlt : C.output < N + N := Nat.lt_of_not_ge hlt
    by_cases hwN : C.output < N
    · let p0 : Fin N := ⟨C.output, hwN⟩
      let f : Fin (N + N) → Bool := fun i => decide (i = Fin.castAdd N p0)
      have hEmpty : IsEmpty { l : Fin N // f (Fin.natAdd N l) = Bool.true } := by
        refine ⟨fun s => ?_⟩
        have h1 := s.2
        simp only [f, decide_eq_true_eq] at h1
        have hv := congrArg Fin.val h1
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      have hCard0 : Fintype.card { l : Fin N // f (Fin.natAdd N l) = Bool.true } ≤ q := by
        rw [Fintype.card_eq_zero]
        omega
      have hNoInc : ¬∃ (p l : Fin N), R p l ∧ f (Fin.castAdd N p) = Bool.true ∧ f (Fin.natAdd N l) = Bool.true := by
        rintro ⟨p, l, _, _, hl⟩
        exact hEmpty.false ⟨l, hl⟩
      have hF := hRej f hCard0 hNoInc
      change (C.gates.foldl step (List.ofFn f)).getD C.output false = false at hF
      rw [hfold_pref _ _ C.output (by simp only [List.length_ofFn]; exact hlt)] at hF
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn] at hF
      have heq : (⟨C.output, hlt⟩ : Fin (N + N)) = Fin.castAdd N p0 := by
        apply Fin.ext
        simp only [Fin.val_castAdd, p0]
      simp only [f, heq, decide_true] at hF
      exact Bool.noConfusion hF
    · let l0 : Fin N := ⟨C.output - N, by omega⟩
      let f : Fin (N + N) → Bool := fun i => decide (i = Fin.natAdd N l0)
      have hsub : ∀ s : { l : Fin N // f (Fin.natAdd N l) = Bool.true }, s.1 = l0 := by
        intro s
        have h1 := s.2
        simp only [f, decide_eq_true_eq] at h1
        have hv := congrArg Fin.val h1
        simp only [Fin.val_natAdd] at hv
        exact Fin.ext (by omega)
      have hinj : Function.Injective (fun _ : { l : Fin N // f (Fin.natAdd N l) = Bool.true } => (() : Unit)) := by
        intro a b _
        exact Subtype.ext ((hsub a).trans (hsub b).symm)
      have hCard1 : Fintype.card { l : Fin N // f (Fin.natAdd N l) = Bool.true } ≤ q := by
        have hle := Fintype.card_le_of_injective _ hinj
        simp only [Fintype.card_unit] at hle
        omega
      have hNoInc : ¬∃ (p l : Fin N), R p l ∧ f (Fin.castAdd N p) = Bool.true ∧ f (Fin.natAdd N l) = Bool.true := by
        rintro ⟨p, l, _, hp, _⟩
        simp only [f, decide_eq_true_eq] at hp
        have hv := congrArg Fin.val hp
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      have hF := hRej f hCard1 hNoInc
      change (C.gates.foldl step (List.ofFn f)).getD C.output false = false at hF
      rw [hfold_pref _ _ C.output (by simp only [List.length_ofFn]; exact hlt)] at hF
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn] at hF
      have heq : (⟨C.output, hlt⟩ : Fin (N + N)) = Fin.natAdd N l0 := by
        apply Fin.ext
        simp only [Fin.val_natAdd, l0]
        omega
      simp only [f, heq, decide_true] at hF
      exact Bool.noConfusion hF
  have hk_lt : C.output - (N + N) < C.gates.length := by change C.output - (N + N) < C.size; omega
  let g0 : PEqualNP.CircuitLowerBounds.Gate := C.gates[C.output - (N + N)]'hk_lt
  have hg0_some : C.gates[C.output - (N + N)]? = Option.some g0 := List.getElem?_eq_getElem hk_lt
  have hSizeBound : N * q ≤ (100 : ℕ) * C.size := by
    rcases (hM g0 (List.getElem_mem hk_lt)).1 with hg0_and | hg0_or
    · exact @hOutAnd q N R hDec C ⟨hq, hN, hEven⟩ hCard hUniq hM ⟨hOutGe, hOutLt⟩ ⟨g0, hg0_some, hg0_and⟩ hInc hRej ⟨hOrLo, hOrHi⟩
    · exact @hOutOr q N R hDec C ⟨hq, hN, hEven⟩ hCard hUniq hM ⟨hOutGe, hOutLt⟩ ⟨g0, hg0_some, hg0_or⟩ hInc hRej ⟨hOrLo, hOrHi⟩
  have hSum := hFilterSum C.gates (fun g => g.op.eval [Bool.true, Bool.false])
  change N * q ≤ (100 : ℕ) * C.gates.length at hSizeBound
  omega
