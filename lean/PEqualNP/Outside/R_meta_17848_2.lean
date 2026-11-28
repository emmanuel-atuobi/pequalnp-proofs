import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17848_2
    (hOutAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        have x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (finSumFinEquiv.symm x4 ∉ x3));
        (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x3 (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x4) = Bool.true) →
        (∀ x5 ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, x3 {Sum.inl x5.1, Sum.inr x5.2} = Bool.false) →
        (64 : ℕ) ≤ x1.size)
    (hOutOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        have x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (finSumFinEquiv.symm x4 ∉ x3));
        (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x3 (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x4) = Bool.true) →
        (∀ x5 ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, x3 {Sum.inl x5.1, Sum.inr x5.2} = Bool.false) →
        (64 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → have x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (finSumFinEquiv.symm x4 ∉ x3)); (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x3 (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x4) = Bool.true) → (∀ x5 ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, x3 {Sum.inl x5.1, Sum.inr x5.2} = Bool.false) → (64 : ℕ) ≤ x1.size := by
  intro C hM
  dsimp only
  intro hQuad hInc
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
  let Q0 : Finset (Fin 13) := {(0 : Fin 13), 1, 2, 5}
  have hQ0 : Q0 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 :=
    Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by decide⟩, by decide⟩
  have he0 : ((0 : Fin 13), (0 : Fin 13)) ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩⟩
  have he1 : ((1 : Fin 13), (1 : Fin 13)) ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩⟩
  have hAvoidInc : ∀ w : Fin (13 + 13),
      ∃ e ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3,
        finSumFinEquiv.symm w ∉ ({Sum.inl e.1, Sum.inr e.2} : Finset (Fin 13 ⊕ Fin 13)) := by
    intro w
    by_cases h0 : finSumFinEquiv.symm w ∈ ({Sum.inl (0 : Fin 13), Sum.inr (0 : Fin 13)} : Finset (Fin 13 ⊕ Fin 13))
    · refine ⟨(1, 1), he1, ?_⟩
      intro h1
      rcases Finset.mem_insert.mp h0 with h0a | h0b
      · rcases Finset.mem_insert.mp h1 with h1a | h1b
        · rw [h0a] at h1a; exact absurd (Sum.inl.inj h1a) (by decide)
        · rw [Finset.mem_singleton] at h1b; rw [h0a] at h1b; exact absurd h1b (by decide)
      · rw [Finset.mem_singleton] at h0b
        rcases Finset.mem_insert.mp h1 with h1a | h1b
        · rw [h0b] at h1a; exact absurd h1a (by decide)
        · rw [Finset.mem_singleton] at h1b; rw [h0b] at h1b; exact absurd (Sum.inr.inj h1b) (by decide)
    · exact ⟨(0, 0), he0, h0⟩
  have hOutLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hT := hQuad Q0 hQ0
    change (C.gates.foldl step (List.ofFn fun (x4 : Fin (13 + 13)) => Decidable.decide (finSumFinEquiv.symm x4 ∉ PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 Q0))).getD C.output false = true at hT
    have hL : (C.gates.foldl step (List.ofFn fun (x4 : Fin (13 + 13)) => Decidable.decide (finSumFinEquiv.symm x4 ∉ PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 Q0))).length = 26 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hF : (C.gates.foldl step (List.ofFn fun (x4 : Fin (13 + 13)) => Decidable.decide (finSumFinEquiv.symm x4 ∉ PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 Q0))).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hF] at hT
    exact Bool.noConfusion hT
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    obtain ⟨e, he, hnot⟩ := hAvoidInc ⟨C.output, hlt⟩
    have hF := hInc e he
    change (C.gates.foldl step (List.ofFn fun (x4 : Fin (13 + 13)) => Decidable.decide (finSumFinEquiv.symm x4 ∉ ({Sum.inl e.1, Sum.inr e.2} : Finset (Fin 13 ⊕ Fin 13))))).getD C.output false = false at hF
    rw [hPref C.gates _ C.output (by rw [List.length_ofFn]; exact hlt)] at hF
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn] at hF
    rw [decide_eq_true hnot] at hF
    exact Bool.noConfusion hF
  have hk_lt : C.output - 26 < C.gates.length := by change C.output - 26 < C.size; omega
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26) = C.gates[C.output - 26]'hk_lt :=
    List.getD_eq_getElem _ _ hk_lt
  rcases (hM (C.gates[C.output - 26]'hk_lt) (List.getElem_mem hk_lt)).1 with hAnd | hOr
  · exact hOutAnd C hM ⟨hOutGe, hOutLt⟩ (by rw [hge]; exact hAnd) hQuad hInc
  · exact hOutOr C hM ⟨hOutGe, hOutLt⟩ (by rw [hge]; exact hOr) hQuad hInc
