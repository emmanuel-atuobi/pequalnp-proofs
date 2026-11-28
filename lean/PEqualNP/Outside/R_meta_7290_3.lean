import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7290_3
    (hHasOr :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 →
        (26 : ℕ) ≤ x3 ∧ x3 < (26 : ℕ) + x2.size →
        (26 : ℕ) ≤ x4 ∧ x4 < (26 : ℕ) + x2.size →
        x3 ≠ x4 →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x3 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → ℕ → Bool := fun (x7 x8 x9 x10 : Fin (13 : ℕ)) (x11 : ℕ) => (x2.wires ((List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x7 ∨ x12 = x8)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x9 ∨ x12 = x10))).getD x11 Bool.false;
        (∀ (x8 x9 x10 x11 : Fin (13 : ℕ)), (x7 x8 x9 x10 x11 x3 || x7 x8 x9 x10 x11 x4) = Decidable.decide (x8 - x10 ∈ x1 ∨ x8 - x11 ∈ x1 ∨ x9 - x10 ∈ x1 ∨ x9 - x11 ∈ x1)) →
        (∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x7 x9 x9 x10 x10 x3 = Bool.true ∧ x7 x9 x9 x10 x10 x4 = Bool.false) →
        (∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)), x7 x10 x10 x11 x11 x4 = Bool.true ∧ x7 x10 x10 x11 x11 x3 = Bool.false) →
        (63 : ℕ) ≤ x2.size)
    (hBothAnd :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 →
        (26 : ℕ) ≤ x3 ∧ x3 < x4 ∧ x4 < (26 : ℕ) + x2.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x3 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x4 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → ℕ → Bool := fun (x7 x8 x9 x10 : Fin (13 : ℕ)) (x11 : ℕ) => (x2.wires ((List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x7 ∨ x12 = x8)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x9 ∨ x12 = x10))).getD x11 Bool.false;
        (∀ (x8 x9 x10 x11 : Fin (13 : ℕ)), (x7 x8 x9 x10 x11 x3 || x7 x8 x9 x10 x11 x4) = Decidable.decide (x8 - x10 ∈ x1 ∨ x8 - x11 ∈ x1 ∨ x9 - x10 ∈ x1 ∨ x9 - x11 ∈ x1)) →
        (∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x7 x9 x9 x10 x10 x3 = Bool.true ∧ x7 x9 x9 x10 x10 x4 = Bool.false) →
        (∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)), x7 x10 x10 x11 x11 x4 = Bool.true ∧ x7 x10 x10 x11 x11 x3 = Bool.false) →
        (63 : ℕ) ≤ x2.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 →       have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → ℕ → Bool := fun (x7 x8 x9 x10 : Fin (13 : ℕ)) (x11 : ℕ) => (x2.wires ((List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x7 ∨ x12 = x8)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x9 ∨ x12 = x10))).getD x11 Bool.false;       (∀ (x8 x9 x10 x11 : Fin (13 : ℕ)), (x7 x8 x9 x10 x11 x3 || x7 x8 x9 x10 x11 x4) = Decidable.decide (x8 - x10 ∈ x1 ∨ x8 - x11 ∈ x1 ∨ x9 - x10 ∈ x1 ∨ x9 - x11 ∈ x1)) → (∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x7 x9 x9 x10 x10 x3 = Bool.true ∧ x7 x9 x9 x10 x10 x4 = Bool.false) → (∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)), x7 x10 x10 x11 x11 x4 = Bool.true ∧ x7 x10 x10 x11 x11 x3 = Bool.false) → (63 : ℕ) ≤ x2.size := by
  classical
  intro x1 x2 x3 x4 hMono hRB x7 hCov hW1 hW2
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
  have hTwoNotMem : (2 : Fin 13) ∉ x1 := by
    change (2 : Fin 13) ∉ ({(0 : Fin 13), (1 : Fin 13), (3 : Fin 13), (9 : Fin 13)} : Finset (Fin 13))
    decide
  have hBounds : ∀ u : ℕ,
      (∀ (a b c d : Fin 13), x7 a b c d u = true → a - c ∈ x1 ∨ a - d ∈ x1 ∨ b - c ∈ x1 ∨ b - d ∈ x1) →
      (∃ (p l : Fin 13), x7 p p l l u = true) →
      26 ≤ u ∧ u < 26 + x2.size := by
    intro u hSound hPos
    constructor
    · by_contra hlt
      have hlt : u < 26 := Nat.lt_of_not_ge hlt
      by_cases h13 : u < 13
      · let p0 : Fin 13 := ⟨u, h13⟩
        let l0 : Fin 13 := p0 - 2
        have ht : x7 p0 p0 l0 l0 u = true := by
          change (x2.gates.foldl step ((List.ofFn fun x12 : Fin 13 => Decidable.decide (x12 = p0 ∨ x12 = p0)) ++ List.ofFn fun x12 : Fin 13 => Decidable.decide (x12 = l0 ∨ x12 = l0))).getD u false = true
          rw [hPref x2.gates _ u (by simp only [List.length_append, List.length_ofFn]; exact hlt)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13)]
          rw [List.getElem?_ofFn]
          simp only [h13, ↓reduceDIte, Option.getD_some, or_self]
          have heq : (⟨u, h13⟩ : Fin 13) = p0 := rfl
          rw [heq]
          simp
        have hm := hSound p0 p0 l0 l0 ht
        have hdiff : p0 - l0 = 2 := by
          dsimp only [l0]
          abel
        rw [hdiff] at hm
        rcases hm with h | h | h | h <;> exact hTwoNotMem h
      · let l0 : Fin 13 := ⟨u - 13, by omega⟩
        let p0 : Fin 13 := l0 + 2
        have ht : x7 p0 p0 l0 l0 u = true := by
          change (x2.gates.foldl step ((List.ofFn fun x12 : Fin 13 => Decidable.decide (x12 = p0 ∨ x12 = p0)) ++ List.ofFn fun x12 : Fin 13 => Decidable.decide (x12 = l0 ∨ x12 = l0))).getD u false = true
          rw [hPref x2.gates _ u (by simp only [List.length_append, List.length_ofFn]; exact hlt)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_ofFn]; omega)]
          simp only [List.length_ofFn]
          rw [List.getElem?_ofFn]
          have hsub : u - 13 < 13 := by omega
          simp only [hsub, ↓reduceDIte, Option.getD_some, or_self]
          have heq : (⟨u - 13, hsub⟩ : Fin 13) = l0 := rfl
          rw [heq]
          simp
        have hm := hSound p0 p0 l0 l0 ht
        have hdiff : p0 - l0 = 2 := by
          dsimp only [p0]
          abel
        rw [hdiff] at hm
        rcases hm with h | h | h | h <;> exact hTwoNotMem h
    · by_contra hge
      have hge : 26 + x2.size ≤ u := Nat.le_of_not_lt hge
      obtain ⟨p, l, hpl⟩ := hPos
      change (x2.gates.foldl step _).getD u false = true at hpl
      have hl : (x2.gates.foldl step ((List.ofFn fun x12 : Fin 13 => Decidable.decide (x12 = p ∨ x12 = p)) ++ List.ofFn fun x12 : Fin 13 => Decidable.decide (x12 = l ∨ x12 = l))).length = 26 + x2.size := by
        rw [hLen]
        simp only [List.length_append, List.length_ofFn]
        rfl
      have hdf : (x2.gates.foldl step ((List.ofFn fun x12 : Fin 13 => Decidable.decide (x12 = p ∨ x12 = p)) ++ List.ofFn fun x12 : Fin 13 => Decidable.decide (x12 = l ∨ x12 = l))).getD u false = false :=
        List.getD_eq_default _ _ (by omega)
      rw [hdf] at hpl
      exact Bool.noConfusion hpl
  have hSound3 : ∀ (a b c d : Fin 13), x7 a b c d x3 = true → a - c ∈ x1 ∨ a - d ∈ x1 ∨ b - c ∈ x1 ∨ b - d ∈ x1 := by
    intro a b c d h3
    have hc := hCov a b c d
    rw [h3, Bool.true_or] at hc
    exact of_decide_eq_true hc.symm
  have hSound4 : ∀ (a b c d : Fin 13), x7 a b c d x4 = true → a - c ∈ x1 ∨ a - d ∈ x1 ∨ b - c ∈ x1 ∨ b - d ∈ x1 := by
    intro a b c d h4
    have hc := hCov a b c d
    rw [h4, Bool.or_true] at hc
    exact of_decide_eq_true hc.symm
  have hB3 : 26 ≤ x3 ∧ x3 < 26 + x2.size :=
    hBounds x3 hSound3 (by obtain ⟨p, l, hp, _⟩ := hW1; exact ⟨p, l, hp⟩)
  have hB4 : 26 ≤ x4 ∧ x4 < 26 + x2.size :=
    hBounds x4 hSound4 (by obtain ⟨p, l, hp, _⟩ := hW2; exact ⟨p, l, hp⟩)
  have hNe : x3 ≠ x4 := by
    intro heq
    obtain ⟨p, l, h3, h4⟩ := hW1
    rw [heq] at h3
    rw [h3] at h4
    exact Bool.noConfusion h4
  have hOp : ∀ j, j < x2.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x2 j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x2 j).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro j hj
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt x2 j = x2.gates[j] :=
      List.getD_eq_getElem _ _ hj
    rw [hge]
    have hmem : x2.gates[j] ∈ x2.gates := List.getElem_mem hj
    have hm := (hMono x2.gates[j] hmem).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  have hCovSwap : ∀ (x8 x9 x10 x11 : Fin (13 : ℕ)),
      (x7 x8 x9 x10 x11 x4 || x7 x8 x9 x10 x11 x3) =
        Decidable.decide (x8 - x10 ∈ x1 ∨ x8 - x11 ∈ x1 ∨ x9 - x10 ∈ x1 ∨ x9 - x11 ∈ x1) :=
    fun a b c d => (Bool.or_comm _ _).trans (hCov a b c d)
  rcases hOp (x3 - 26) (by omega) with h3And | h3Or
  · rcases hOp (x4 - 26) (by omega) with h4And | h4Or
    · rcases Nat.lt_or_gt_of_ne hNe with hlt | hgt
      · exact hBothAnd x2 x3 x4 hMono hRB ⟨hB3.1, hlt, hB4.2⟩ h3And h4And hCov hW1 hW2
      · exact hBothAnd x2 x4 x3 hMono hRB ⟨hB4.1, hgt, hB3.2⟩ h4And h3And hCovSwap hW2 hW1
    · exact hHasOr x2 x4 x3 hMono hRB hB4 hB3 hNe.symm h4Or hCovSwap hW2 hW1
  · exact hHasOr x2 x3 x4 hMono hRB hB3 hB4 hNe h3Or hCov hW1 hW2
