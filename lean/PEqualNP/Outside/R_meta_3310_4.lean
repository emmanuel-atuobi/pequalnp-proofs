import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3310_4
    (hOutAnd :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
        (200 : ℕ) ≤ q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
        PEqualNP.MetaComplexity.Monotone2 C →
        N + N ≤ C.output →
        C.output < N + N + C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ p l : Fin N, I p l →
          PEqualNP.MetaComplexity.circuitFun (N + N) C (fun u : Fin (N + N) => Decidable.decide (u = Fin.castAdd N p ∨ u = Fin.natAdd N l)) = Bool.true) →
        (∀ x : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // x (Fin.natAdd N l) = Bool.true } ≤ q →
          (¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = Bool.true ∧ x (Fin.natAdd N l) = Bool.true) →
          PEqualNP.MetaComplexity.circuitFun (N + N) C x = Bool.false) →
        have ors : ℕ := (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [Bool.true, Bool.false]) C.gates).length;
        (2 : ℕ) * q ^ (2 : ℕ) + (1 : ℕ) ≤ ors →
        (100 : ℕ) * ors < N * q →
        N * q ≤ (100 : ℕ) * C.size)
    (hOutOr :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
        (200 : ℕ) ≤ q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) →
        PEqualNP.MetaComplexity.Monotone2 C →
        N + N ≤ C.output →
        C.output < N + N + C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ p l : Fin N, I p l →
          PEqualNP.MetaComplexity.circuitFun (N + N) C (fun u : Fin (N + N) => Decidable.decide (u = Fin.castAdd N p ∨ u = Fin.natAdd N l)) = Bool.true) →
        (∀ x : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // x (Fin.natAdd N l) = Bool.true } ≤ q →
          (¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = Bool.true ∧ x (Fin.natAdd N l) = Bool.true) →
          PEqualNP.MetaComplexity.circuitFun (N + N) C x = Bool.false) →
        have ors : ℕ := (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [Bool.true, Bool.false]) C.gates).length;
        (2 : ℕ) * q ^ (2 : ℕ) + (1 : ℕ) ≤ ors →
        (100 : ℕ) * ors < N * q →
        N * q ≤ (100 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →               (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →                 have x13 : ℕ := (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length;                 (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ x13 → (100 : ℕ) * x13 < x2 * x1 → x2 * x1 - (100 : ℕ) * x13 ≤ (100 : ℕ) * (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => !x16.op.eval [Bool.true, Bool.false]) x5.gates).length := by
  intro q N I _ C hq hN hCard hProj hMono hPos hNeg ors hOrsGe hOrsLt
  have hNpos : 0 < N := by rw [hN]; omega
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl (fun ws h => ws ++ [h.op.eval (h.inputs.map fun i => ws.getD i false)]) init).length =
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
  have houtLt : C.output < N + N + C.size := by
    by_contra hge
    let l0 : Fin N := ⟨0, hNpos⟩
    have hpos0 : 0 < Fintype.card { p : Fin N // I p l0 } := by rw [hCard l0]; omega
    obtain ⟨⟨p0, hp0⟩⟩ := Fintype.card_pos_iff.mp hpos0
    have ht := hPos p0 l0 hp0
    change (C.gates.foldl (fun ws h => ws ++ [h.op.eval (h.inputs.map fun i => ws.getD i false)])
      (List.ofFn fun u : Fin (N + N) => Decidable.decide (u = Fin.castAdd N p0 ∨ u = Fin.natAdd N l0))).getD C.output false = true at ht
    have hlen : (C.gates.foldl (fun ws h => ws ++ [h.op.eval (h.inputs.map fun i => ws.getD i false)])
        (List.ofFn fun u : Fin (N + N) => Decidable.decide (u = Fin.castAdd N p0 ∨ u = Fin.natAdd N l0))).length = N + N + C.size := by
      rw [hfold_len, List.length_ofFn]
      rfl
    rw [List.getD_eq_default _ _ (by omega)] at ht
    exact Bool.false_ne_true ht
  have houtGe : N + N ≤ C.output := by
    by_contra hlt
    have hlt : C.output < N + N := Nat.lt_of_not_ge hlt
    by_cases h1 : C.output < N
    · let p0 : Fin N := ⟨C.output, h1⟩
      let l0 : Fin N := ⟨0, hNpos⟩
      have hsub : (Finset.univ.filter fun p : Fin N => I p l0) ⊆ {p0} := by
        intro p hp
        have ht := hPos p l0 (Finset.mem_filter.mp hp).2
        change (C.gates.foldl (fun ws h => ws ++ [h.op.eval (h.inputs.map fun i => ws.getD i false)])
          (List.ofFn fun u : Fin (N + N) => Decidable.decide (u = Fin.castAdd N p ∨ u = Fin.natAdd N l0))).getD C.output false = true at ht
        rw [hfold_pref _ _ C.output (by rw [List.length_ofFn]; exact hlt)] at ht
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt)] at ht
        simp only [List.getElem_ofFn, decide_eq_true_eq] at ht
        rcases ht with hL | hR
        · have hv := congrArg Fin.val hL
          simp only [Fin.val_castAdd] at hv
          exact Finset.mem_singleton.mpr (Fin.ext hv.symm)
        · have hv := congrArg Fin.val hR
          simp only [Fin.val_natAdd] at hv
          omega
      have hc1 : (Finset.univ.filter fun p : Fin N => I p l0).card ≤ 1 :=
        le_trans (Finset.card_le_card hsub) (by simp only [Finset.card_singleton]; rfl)
      have hc2 : (Finset.univ.filter fun p : Fin N => I p l0).card = Fintype.card { p : Fin N // I p l0 } := by
        rw [Fintype.card_subtype]
      have hc3 := hCard l0
      omega
    · let l0 : Fin N := ⟨C.output - N, by omega⟩
      let x : Fin (N + N) → Bool := fun u => Decidable.decide (u = Fin.natAdd N l0)
      have hcard1 : Fintype.card { l : Fin N // x (Fin.natAdd N l) = Bool.true } ≤ q := by
        have hsub : (Finset.univ.filter fun l : Fin N => x (Fin.natAdd N l) = Bool.true) ⊆ {l0} := by
          intro l hl
          have ht := (Finset.mem_filter.mp hl).2
          simp only [x, decide_eq_true_eq] at ht
          have hv := congrArg Fin.val ht
          simp only [Fin.val_natAdd] at hv
          exact Finset.mem_singleton.mpr (Fin.ext (by omega))
        have hc1 : (Finset.univ.filter fun l : Fin N => x (Fin.natAdd N l) = Bool.true).card ≤ 1 :=
          le_trans (Finset.card_le_card hsub) (by simp only [Finset.card_singleton]; rfl)
        rw [Fintype.card_subtype]
        omega
      have hnoInc : ¬∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = Bool.true ∧ x (Fin.natAdd N l) = Bool.true := by
        rintro ⟨p, l, _, hp, _⟩
        simp only [x, decide_eq_true_eq] at hp
        have hv := congrArg Fin.val hp
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      have hf := hNeg x hcard1 hnoInc
      change (C.gates.foldl (fun ws h => ws ++ [h.op.eval (h.inputs.map fun i => ws.getD i false)]) (List.ofFn x)).getD C.output false = false at hf
      rw [hfold_pref _ _ C.output (by rw [List.length_ofFn]; exact hlt)] at hf
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt)] at hf
      simp only [List.getElem_ofFn, x, decide_eq_false_iff_not] at hf
      apply hf
      ext
      simp only [Fin.val_natAdd, l0]
      omega
  have hk_lt : C.output - (N + N) < C.gates.length := by
    change C.output - (N + N) < C.size
    omega
  have hg_mem : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - (N + N)) ∈ C.gates := by
    change C.gates.getD (C.output - (N + N)) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hk_lt]
    exact List.getElem_mem hk_lt
  have hBound : N * q ≤ (100 : ℕ) * C.size := by
    rcases (hMono _ hg_mem).1 with hAnd | hOr
    · exact @hOutAnd q N I _ C hq hN hCard hProj hMono houtGe houtLt hAnd hPos hNeg hOrsGe hOrsLt
    · exact @hOutOr q N I _ C hq hN hCard hProj hMono houtGe houtLt hOr hPos hNeg hOrsGe hOrsLt
  have hPart : ors + (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => !g.op.eval [Bool.true, Bool.false]) C.gates).length = C.size := by
    change (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [Bool.true, Bool.false]) C.gates).length +
      (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => !g.op.eval [Bool.true, Bool.false]) C.gates).length = C.gates.length
    induction C.gates with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.filter_cons, List.length_cons]
      cases hd.op.eval [Bool.true, Bool.false] <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
  omega
