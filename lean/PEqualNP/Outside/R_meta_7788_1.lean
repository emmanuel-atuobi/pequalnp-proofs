import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7788_1
    (hHasOr :
      let x1 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x1 x2 : Fin (26 : ℕ)) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ (x1 = Fin.castAdd (13 : ℕ) x3 ∧ x2 = Fin.natAdd (13 : ℕ) x4 ∨ x2 = Fin.castAdd (13 : ℕ) x3 ∧ x1 = Fin.natAdd (13 : ℕ) x4);
      have x2 : Fin (26 : ℕ) → Fin (26 : ℕ) → List Bool := fun (x2 x3 : Fin (26 : ℕ)) => List.ofFn fun (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = x2 ∨ x4 = x3);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false;
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt;
      have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) =>
        have x7 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;
        (x4 x5 x6).op = x7 ∧ ∃ x8 ∈ (x4 x5 x6).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x5 (x8 - (26 : ℕ))).op = x7;
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 g1 g2 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x6 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x6 →
        (26 : ℕ) ≤ x7 ∧ x7 < (26 : ℕ) + x6.size ∧ (26 : ℕ) ≤ x8 ∧ x8 < (26 : ℕ) + x6.size ∧ x7 ≠ x8 →
        (x4 x6 (x7 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x13 x14 : Fin (26 : ℕ)), (x3 x6 x7 (x2 x13 x14) || x3 x6 x8 (x2 x13 x14)) = Decidable.decide (x1 x13 x14)) →
        (∃ (x14 x15 : Fin (26 : ℕ)), x3 x6 x7 (x2 x14 x15) = Bool.true ∧ x3 x6 x8 (x2 x14 x15) = Bool.false) →
        (∃ (x15 x16 : Fin (26 : ℕ)), x3 x6 x8 (x2 x15 x16) = Bool.true ∧ x3 x6 x7 (x2 x15 x16) = Bool.false) →
        g1 < g2 ∧ g2 < x6.size ∧ x5 x6 g1 ∧ x5 x6 g2 ∧ (∀ g < x6.size, x5 x6 g → g = g1 ∨ g = g2) →
        (63 : ℕ) ≤ x6.size)
    (hBothAnd :
      let x1 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x1 x2 : Fin (26 : ℕ)) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ (x1 = Fin.castAdd (13 : ℕ) x3 ∧ x2 = Fin.natAdd (13 : ℕ) x4 ∨ x2 = Fin.castAdd (13 : ℕ) x3 ∧ x1 = Fin.natAdd (13 : ℕ) x4);
      have x2 : Fin (26 : ℕ) → Fin (26 : ℕ) → List Bool := fun (x2 x3 : Fin (26 : ℕ)) => List.ofFn fun (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = x2 ∨ x4 = x3);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false;
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt;
      have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) =>
        have x7 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;
        (x4 x5 x6).op = x7 ∧ ∃ x8 ∈ (x4 x5 x6).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x5 (x8 - (26 : ℕ))).op = x7;
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 g1 g2 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x6 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x6 →
        (26 : ℕ) ≤ x7 ∧ x7 < x8 ∧ x8 < (26 : ℕ) + x6.size →
        (x4 x6 (x7 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x4 x6 (x8 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x13 x14 : Fin (26 : ℕ)), (x3 x6 x7 (x2 x13 x14) || x3 x6 x8 (x2 x13 x14)) = Decidable.decide (x1 x13 x14)) →
        (∃ (x14 x15 : Fin (26 : ℕ)), x3 x6 x7 (x2 x14 x15) = Bool.true ∧ x3 x6 x8 (x2 x14 x15) = Bool.false) →
        (∃ (x15 x16 : Fin (26 : ℕ)), x3 x6 x8 (x2 x15 x16) = Bool.true ∧ x3 x6 x7 (x2 x15 x16) = Bool.false) →
        g1 < g2 ∧ g2 < x6.size ∧ x5 x6 g1 ∧ x5 x6 g2 ∧ (∀ g < x6.size, x5 x6 g → g = g1 ∨ g = g2) →
        (63 : ℕ) ≤ x6.size) :
    let x1 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x1 x2 : Fin (26 : ℕ)) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ (x1 = Fin.castAdd (13 : ℕ) x3 ∧ x2 = Fin.natAdd (13 : ℕ) x4 ∨ x2 = Fin.castAdd (13 : ℕ) x3 ∧ x1 = Fin.natAdd (13 : ℕ) x4); have x2 : Fin (26 : ℕ) → Fin (26 : ℕ) → List Bool := fun (x2 x3 : Fin (26 : ℕ)) => List.ofFn fun (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = x2 ∨ x4 = x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) =>   have x7 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;   (x4 x5 x6).op = x7 ∧ ∃ x8 ∈ (x4 x5 x6).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x5 (x8 - (26 : ℕ))).op = x7; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), PEqualNP.MetaComplexity.Monotone2 x6 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x6 → x7 < (26 : ℕ) + x6.size → x8 < (26 : ℕ) + x6.size → (∀ (x13 x14 : Fin (26 : ℕ)), (x3 x6 x7 (x2 x13 x14) || x3 x6 x8 (x2 x13 x14)) = Decidable.decide (x1 x13 x14)) → (∃ (x14 x15 : Fin (26 : ℕ)), x3 x6 x7 (x2 x14 x15) = Bool.true ∧ x3 x6 x8 (x2 x14 x15) = Bool.false) → (∃ (x15 x16 : Fin (26 : ℕ)), x3 x6 x8 (x2 x15 x16) = Bool.true ∧ x3 x6 x7 (x2 x15 x16) = Bool.false) → (∃ x16 ∈ Finset.range x6.size, ∃ x17 ∈ Finset.range x6.size, x16 ≠ x17 ∧ x5 x6 x16 ∧ x5 x6 x17 ∧ ∀ x18 ∈ Finset.range x6.size, x5 x6 x18 → x18 = x16 ∨ x18 = x17) → (63 : ℕ) ≤ x6.size := by
  classical
  dsimp only
  intro C w1 w2 hM hRB hw1Lt hw2Lt hOr hOnly1 hOnly2 hNest
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool),
      (gs.foldl step v).length = v.length + gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro v; simp
    | append_singleton gs g ih =>
      intro v
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, step, List.length_append, List.length_singleton]
      rw [ih v]
      omega
  have hPref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool) (i : ℕ),
      i < v.length → (gs.foldl step v).getD i false = v.getD i false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro v i _; rfl
    | append_singleton gs g ih =>
      intro v i hi
      have hl : (gs.foldl step v).length = v.length + gs.length := hLen gs v
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((gs.foldl step v) ++ [_]).getD i false = v.getD i false
      rw [List.getD_append _ _ _ _ (by omega)]
      exact ih v i hi
  have hNoSelf : ∀ v : Fin 26,
      ¬∃ (p l : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
        (v = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l ∨ v = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) := by
    intro v h
    obtain ⟨p, l, _, h⟩ := h
    rcases h with ⟨hp, hl⟩ | ⟨hp, hl⟩
    · have hv := congrArg Fin.val (hp.symm.trans hl)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    · have hv := congrArg Fin.val (hp.symm.trans hl)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
  have hNotRaw : ∀ w : ℕ,
      (∀ u : Fin 26, (C.wires (List.ofFn fun i : Fin 26 => Decidable.decide (i = u ∨ i = u))).getD w false = true → False) →
      26 ≤ w := by
    intro w hFalse
    by_contra hlt
    have hlt : w < 26 := Nat.lt_of_not_ge hlt
    let u : Fin 26 := ⟨w, hlt⟩
    apply hFalse u
    change (C.gates.foldl step (List.ofFn fun i : Fin 26 => Decidable.decide (i = u ∨ i = u))).getD w false = true
    rw [hPref C.gates _ w (by rw [List.length_ofFn]; exact hlt)]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn]
    exact decide_eq_true (Or.inl rfl)
  have hw1Ge : 26 ≤ w1 := by
    apply hNotRaw w1
    intro u hT
    have h1 := hOr u u
    rw [hT, Bool.true_or] at h1
    exact hNoSelf u (of_decide_eq_true h1.symm)
  have hw2Ge : 26 ≤ w2 := by
    apply hNotRaw w2
    intro u hT
    have h1 := hOr u u
    rw [hT, Bool.or_true] at h1
    exact hNoSelf u (of_decide_eq_true h1.symm)
  have hNe : w1 ≠ w2 := by
    intro hEq
    obtain ⟨a, b, h1T, h2F⟩ := hOnly1
    rw [hEq] at h1T
    rw [h1T] at h2F
    exact Bool.noConfusion h2F
  obtain ⟨a1, ha1, a2, ha2, haNe, ha51, ha52, haAll⟩ := hNest
  have ha1Lt : a1 < C.size := Finset.mem_range.mp ha1
  have ha2Lt : a2 < C.size := Finset.mem_range.mp ha2
  have hNestOrd : ∃ g1 g2 : ℕ, g1 < g2 ∧ g2 < C.size ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
       ∃ x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).inputs, 26 ≤ x8 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (x8 - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
       ∃ x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, 26 ≤ x8 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (x8 - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
      (∀ g < C.size,
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
         ∃ x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs, 26 ≤ x8 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (x8 - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        g = g1 ∨ g = g2) := by
    rcases Nat.lt_or_gt_of_ne haNe with h12 | h21
    · exact ⟨a1, a2, h12, ha2Lt, ha51, ha52, fun g hg h5 => haAll g (Finset.mem_range.mpr hg) h5⟩
    · exact ⟨a2, a1, h21, ha1Lt, ha52, ha51, fun g hg h5 => (haAll g (Finset.mem_range.mpr hg) h5).symm⟩
  obtain ⟨g1, g2, hOrd⟩ := hNestOrd
  have hk1 : w1 - 26 < C.gates.length := by change w1 - 26 < C.size; omega
  have hk2 : w2 - 26 < C.gates.length := by change w2 - 26 < C.size; omega
  have hga1 : PEqualNP.MetaComplexity.NestedCover.gateAt C (w1 - 26) = C.gates[w1 - 26]'hk1 :=
    List.getD_eq_getElem _ _ hk1
  have hga2 : PEqualNP.MetaComplexity.NestedCover.gateAt C (w2 - 26) = C.gates[w2 - 26]'hk2 :=
    List.getD_eq_getElem _ _ hk2
  have hOrSwap : ∀ u v : Fin 26,
      ((C.wires (List.ofFn fun i : Fin 26 => Decidable.decide (i = u ∨ i = v))).getD w2 false ||
       (C.wires (List.ofFn fun i : Fin 26 => Decidable.decide (i = u ∨ i = v))).getD w1 false) =
      Decidable.decide (∃ (p l : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
        (u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l ∨ v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)) := by
    intro u v
    rw [Bool.or_comm]
    exact hOr u v
  rcases (hM (C.gates[w1 - 26]'hk1) (List.getElem_mem hk1)).1 with h1And | h1Or
  · rcases (hM (C.gates[w2 - 26]'hk2) (List.getElem_mem hk2)).1 with h2And | h2Or
    · rcases Nat.lt_or_gt_of_ne hNe with h12 | h21
      · exact hBothAnd C w1 w2 g1 g2 hM hRB ⟨hw1Ge, h12, hw2Lt⟩
          ⟨by rw [hga1]; exact h1And, by rw [hga2]; exact h2And⟩ hOr hOnly1 hOnly2 hOrd
      · exact hBothAnd C w2 w1 g1 g2 hM hRB ⟨hw2Ge, h21, hw1Lt⟩
          ⟨by rw [hga2]; exact h2And, by rw [hga1]; exact h1And⟩ hOrSwap hOnly2 hOnly1 hOrd
    · exact hHasOr C w2 w1 g1 g2 hM hRB ⟨hw2Ge, hw2Lt, hw1Ge, hw1Lt, hNe.symm⟩
        (by rw [hga2]; exact h2Or) hOrSwap hOnly2 hOnly1 hOrd
  · exact hHasOr C w1 w2 g1 g2 hM hRB ⟨hw1Ge, hw1Lt, hw2Ge, hw2Lt, hNe⟩
      (by rw [hga1]; exact h1Or) hOr hOnly1 hOnly2 hOrd
