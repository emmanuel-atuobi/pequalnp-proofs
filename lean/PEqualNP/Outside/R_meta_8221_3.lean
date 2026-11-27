import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8221_3
    (hOutAnd :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        (26 : ℕ) ≤ x2.output ∧ x2.output < (26 : ℕ) + x2.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) →
        ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Fin.addCases (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x8)) (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) x10) = Bool.true)
    (hOutOr :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        (26 : ℕ) ≤ x2.output ∧ x2.output < (26 : ℕ) + x2.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) →
        ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Fin.addCases (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x8)) (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) x10) = Bool.true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) → ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Fin.addCases (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x8)) (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) x10) = Bool.true := by
  classical
  intro x1 C hMono hSz hLD1 hLD2 hInc
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
  have hEvalLt : ∀ (f : Fin 26 → Bool) (hj : C.output < 26),
      PEqualNP.MetaComplexity.circuitFun 26 C f = f ⟨C.output, hj⟩ := by
    intro f hj
    have h1 := hfold_pref C.gates (List.ofFn f) C.output (by simp only [List.length_ofFn]; exact hj)
    change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn f)).getD C.output false = f ⟨C.output, hj⟩
    rw [h1, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hj), List.getElem_ofFn]
  by_cases houtLt26 : C.output < 26
  · by_cases h13 : C.output < 13
    · let p0 : Fin 13 := ⟨C.output, h13⟩
      refine ⟨{p0}, ∅, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ hl; exact False.elim (Finset.notMem_empty _ hl)
      · intro l
        calc ({p ∈ ({p0} : Finset (Fin 13)) | p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9}).card
            ≤ ({p0} : Finset (Fin 13)).card := Finset.card_filter_le _ _
          _ = 1 := Finset.card_singleton _
          _ ≤ 2 := by decide
      · intro p; simp
      · rw [hEvalLt _ houtLt26]
        have heq : (⟨C.output, houtLt26⟩ : Fin 26) = Fin.castAdd 13 p0 := Fin.ext rfl
        rw [heq, Fin.addCases_left]
        simp
    · let l0 : Fin 13 := ⟨C.output - 13, by omega⟩
      refine ⟨∅, {l0}, ?_, ?_, ?_, ?_⟩
      · intro _ hp; exact False.elim (Finset.notMem_empty _ hp)
      · intro l; simp
      · intro p
        calc ({l ∈ ({l0} : Finset (Fin 13)) | p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9}).card
            ≤ ({l0} : Finset (Fin 13)).card := Finset.card_filter_le _ _
          _ = 1 := Finset.card_singleton _
          _ ≤ 2 := by decide
      · rw [hEvalLt _ houtLt26]
        have heq : (⟨C.output, houtLt26⟩ : Fin 26) = Fin.natAdd 13 l0 :=
          Fin.ext (by change C.output = 13 + (C.output - 13); omega)
        rw [heq, Fin.addCases_right]
        simp
  · have houtGe : 26 ≤ C.output := Nat.le_of_not_lt houtLt26
    have houtLt : C.output < 26 + C.size := by
      by_contra hge
      have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
      have ht := hInc 0 0 (Or.inl rfl)
      change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)])
        (List.ofFn fun x10 : Fin 26 => Decidable.decide (x10 = Fin.castAdd 13 (0 : Fin 13) ∨ x10 = Fin.natAdd 13 (0 : Fin 13)))).getD C.output false = true at ht
      have hlen : (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)])
        (List.ofFn fun x10 : Fin 26 => Decidable.decide (x10 = Fin.castAdd 13 (0 : Fin 13) ∨ x10 = Fin.natAdd 13 (0 : Fin 13)))).length = 26 + C.size := by
        rw [hfold_len, List.length_ofFn]
        rfl
      have hdf : (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)])
        (List.ofFn fun x10 : Fin 26 => Decidable.decide (x10 = Fin.castAdd 13 (0 : Fin 13) ∨ x10 = Fin.natAdd 13 (0 : Fin 13)))).getD C.output false = false :=
        List.getD_eq_default _ _ (by omega)
      rw [hdf] at ht
      exact Bool.noConfusion ht
    have hk_lt : C.output - 26 < C.gates.length := by change C.output - 26 < C.size; omega
    have hOp : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26) = C.gates[C.output - 26] :=
        List.getD_eq_getElem _ _ hk_lt
      rw [hge]
      have hm := (hMono C.gates[C.output - 26] (List.getElem_mem hk_lt)).1
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
    rcases hOp with hAnd | hOr
    · exact hOutAnd C hMono hSz ⟨houtGe, houtLt⟩ hAnd hLD1 hLD2 hInc
    · exact hOutOr C hMono hSz ⟨houtGe, houtLt⟩ hOr hLD1 hLD2 hInc
