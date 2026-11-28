import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8867_4
    (hOutAnd :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),
        let V : Type := Fin (x2 + x2) → Bool;
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5;
        have x12 : ℕ → V → Bool := PEqualNP.CleanedNonEdge.wireVal (x2 + x2) x5;
        have x13 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (x2 + x2) x5;
        have x14 : Fin x2 × Fin x2 → V := fun (p : Fin x2 × Fin x2) (u : Fin (x2 + x2)) => Decidable.decide (u = Fin.castAdd x2 p.1 ∨ u = Fin.natAdd x2 p.2);
        have x15 : Fin x2 × Fin x2 → Fin (x2 + x2) → ℕ → Prop := fun (p : Fin x2 × Fin x2) (u : Fin (x2 + x2)) (k : ℕ) => k < x5.size ∧ (ga k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ Relation.ReflTransGen (fun (a b : ℕ) => ∃ j < x5.size, b = x2 + x2 + j ∧ a ∈ (ga j).inputs ∧ x12 a (x14 p) = Bool.true ∧ x12 b (x14 p) = Bool.true) (x2 + x2 + k) x5.output ∧ ∀ (i : Fin (2 : ℕ)), (x12 (PEqualNP.TopForm.opnd x5 k i) fun (v : Fin (x2 + x2)) => Decidable.decide (v = u)) = Bool.false;
        (87 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (l : Fin x2), Fintype.card { p : Fin x2 // x3 p l } = x1 + (1 : ℕ)) →
        (∀ (p r : Fin x2), p ≠ r → ∃! l : Fin x2, x3 p l ∧ x3 r l) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →
        x6.Nonempty →
        x2 + x2 ≤ x5.output ∧ x5.output < x2 + x2 + x5.size →
        (ga (x5.output - (x2 + x2))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (f : V), Fintype.card { l : Fin x2 // f (Fin.natAdd x2 l) = Bool.true } ≤ x1 → (¬∃ (p l : Fin x2), x3 p l ∧ f (Fin.castAdd x2 p) = Bool.true ∧ f (Fin.natAdd x2 l) = Bool.true) → x12 x5.output f = Bool.false) →
        (∀ e ∈ x6, x3 e.1 e.2 ∧ x12 x5.output (x14 e) = Bool.true ∧ ∃ (a b : ℕ), (x13 a b ∨ x13 b a) ∧ x15 e (Fin.castAdd x2 e.1) a ∧ x15 e (Fin.natAdd x2 e.2) b) →
        x6.card ≤ (8 : ℕ) * x5.size)
    (hOutOr :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),
        let V : Type := Fin (x2 + x2) → Bool;
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5;
        have x12 : ℕ → V → Bool := PEqualNP.CleanedNonEdge.wireVal (x2 + x2) x5;
        have x13 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (x2 + x2) x5;
        have x14 : Fin x2 × Fin x2 → V := fun (p : Fin x2 × Fin x2) (u : Fin (x2 + x2)) => Decidable.decide (u = Fin.castAdd x2 p.1 ∨ u = Fin.natAdd x2 p.2);
        have x15 : Fin x2 × Fin x2 → Fin (x2 + x2) → ℕ → Prop := fun (p : Fin x2 × Fin x2) (u : Fin (x2 + x2)) (k : ℕ) => k < x5.size ∧ (ga k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ Relation.ReflTransGen (fun (a b : ℕ) => ∃ j < x5.size, b = x2 + x2 + j ∧ a ∈ (ga j).inputs ∧ x12 a (x14 p) = Bool.true ∧ x12 b (x14 p) = Bool.true) (x2 + x2 + k) x5.output ∧ ∀ (i : Fin (2 : ℕ)), (x12 (PEqualNP.TopForm.opnd x5 k i) fun (v : Fin (x2 + x2)) => Decidable.decide (v = u)) = Bool.false;
        (87 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (l : Fin x2), Fintype.card { p : Fin x2 // x3 p l } = x1 + (1 : ℕ)) →
        (∀ (p r : Fin x2), p ≠ r → ∃! l : Fin x2, x3 p l ∧ x3 r l) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →
        x6.Nonempty →
        x2 + x2 ≤ x5.output ∧ x5.output < x2 + x2 + x5.size →
        (ga (x5.output - (x2 + x2))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (f : V), Fintype.card { l : Fin x2 // f (Fin.natAdd x2 l) = Bool.true } ≤ x1 → (¬∃ (p l : Fin x2), x3 p l ∧ f (Fin.castAdd x2 p) = Bool.true ∧ f (Fin.natAdd x2 l) = Bool.true) → x12 x5.output f = Bool.false) →
        (∀ e ∈ x6, x3 e.1 e.2 ∧ x12 x5.output (x14 e) = Bool.true ∧ ∃ (a b : ℕ), (x13 a b ∨ x13 b a) ∧ x15 e (Fin.castAdd x2 e.1) a ∧ x15 e (Fin.natAdd x2 e.2) b) →
        x6.card ≤ (8 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             have x12 : ℕ → (Fin (x2 + x2) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (x2 + x2) x5;             have x13 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (x2 + x2) x5;             have x14 : Fin x2 × Fin x2 → Fin (x2 + x2) → Bool := fun (x14 : Fin x2 × Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x14.1 ∨ x15 = Fin.natAdd x2 x14.2);             have x15 : Fin x2 × Fin x2 → Fin (x2 + x2) → ℕ → Prop := fun (x15 : Fin x2 × Fin x2) (x16 : Fin (x2 + x2)) (x17 : ℕ) => x17 < x5.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ Relation.ReflTransGen (fun (x18 x19 : ℕ) => ∃ x20 < x5.size, x19 = x2 + x2 + x20 ∧ x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x20).inputs ∧ x12 x18 (x14 x15) = Bool.true ∧ x12 x19 (x14 x15) = Bool.true) (x2 + x2 + x17) x5.output ∧ ∀ (x18 : Fin (2 : ℕ)), (x12 (PEqualNP.TopForm.opnd x5 x17 x18) fun (x19 : Fin (x2 + x2)) => Decidable.decide (x19 = x16)) = Bool.false;             (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → x12 x5.output x16 = Bool.false) → (∀ x17 ∈ x6, x3 x17.1 x17.2 ∧ x12 x5.output (x14 x17) = Bool.true ∧ ∃ (x19 : ℕ) (x20 : ℕ), (x13 x19 x20 ∨ x13 x20 x19) ∧ x15 x17 (Fin.castAdd x2 x17.1) x19 ∧ x15 x17 (Fin.natAdd x2 x17.2) x20) → x6.card ≤ (8 : ℕ) * x5.size := by
  classical
  intro q N inc _ C E hq hN hCard hProj hAO x12 x13 x14 x15 hSound hE
  by_cases hEmp : E = ∅
  · rw [hEmp, Finset.card_empty]
    exact Nat.zero_le _
  · have hNE : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmp
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
    have hOutGe : N + N ≤ C.output := by
      by_contra hlt
      have hlt : C.output < N + N := Nat.lt_of_not_ge hlt
      let idx : Fin (N + N) := ⟨C.output, hlt⟩
      let f : Fin (N + N) → Bool := fun u => Decidable.decide (u = idx)
      have hCardLe : Fintype.card { l : Fin N // f (Fin.natAdd N l) = Bool.true } ≤ q := by
        rw [Fintype.card_subtype]
        by_cases h1 : C.output < N
        · have hEmpF : (Finset.univ.filter fun l : Fin N => f (Fin.natAdd N l) = Bool.true) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro l _
            simp only [f, decide_eq_true_eq]
            intro heq
            have hv := congrArg Fin.val heq
            simp only [Fin.val_natAdd] at hv
            have : N + l.val = C.output := hv
            omega
          rw [hEmpF, Finset.card_empty]
          exact Nat.zero_le _
        · let l0 : Fin N := ⟨C.output - N, by omega⟩
          have hSub : (Finset.univ.filter fun l : Fin N => f (Fin.natAdd N l) = Bool.true) ⊆ {l0} := by
            intro l hl
            have hm := (Finset.mem_filter.mp hl).2
            simp only [f, decide_eq_true_eq] at hm
            have hv := congrArg Fin.val hm
            simp only [Fin.val_natAdd] at hv
            change N + l.val = C.output at hv
            have hlv : l.val = l0.val := by change l.val = C.output - N; omega
            exact Finset.mem_singleton.mpr (Fin.ext hlv)
          have hc := Finset.card_le_card hSub
          simp only [Finset.card_singleton] at hc
          omega
      have hNoInc : ¬∃ (p l : Fin N), inc p l ∧ f (Fin.castAdd N p) = Bool.true ∧ f (Fin.natAdd N l) = Bool.true := by
        rintro ⟨p, l, _, hp, hl⟩
        simp only [f, decide_eq_true_eq] at hp hl
        have heq := hp.trans hl.symm
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      have hFl : x12 C.output f = Bool.false := hSound f hCardLe hNoInc
      have hTr : x12 C.output f = Bool.true := by
        change (C.gates.foldl step (List.ofFn f)).getD C.output false = true
        rw [hPref C.gates (List.ofFn f) C.output (by simp only [List.length_ofFn]; exact hlt)]
        rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn]
        have heq : (⟨C.output, hlt⟩ : Fin (N + N)) = idx := rfl
        simp only [f, heq, decide_true]
      rw [hFl] at hTr
      exact Bool.noConfusion hTr
    have hOutLt : C.output < N + N + C.size := by
      by_contra hge
      have hge : N + N + C.size ≤ C.output := Nat.le_of_not_lt hge
      obtain ⟨e, he⟩ := hNE
      have hTr : x12 C.output (x14 e) = Bool.true := (hE e he).2.1
      change (C.gates.foldl step (List.ofFn (x14 e))).getD C.output false = true at hTr
      have hlen : (C.gates.foldl step (List.ofFn (x14 e))).length = N + N + C.size := by
        rw [hLen, List.length_ofFn]
        rfl
      have hdf : (C.gates.foldl step (List.ofFn (x14 e))).getD C.output false = false :=
        List.getD_eq_default _ _ (by omega)
      rw [hdf] at hTr
      exact Bool.noConfusion hTr
    have hjLt : C.output - (N + N) < C.gates.length := by change C.output - (N + N) < C.size; omega
    have hGateEq : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - (N + N)) = C.gates[C.output - (N + N)]'hjLt := by
      change C.gates.getD (C.output - (N + N)) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
      exact List.getD_eq_getElem _ _ hjLt
    have hOp := hAO.1 (C.gates[C.output - (N + N)]'hjLt) (List.getElem_mem hjLt)
    rw [← hGateEq] at hOp
    rcases hOp with hAnd | hOr
    · exact @hOutAnd q N inc _ C E hq hN hCard hProj hAO hNE ⟨hOutGe, hOutLt⟩ hAnd hSound hE
    · exact @hOutOr q N inc _ C E hq hN hCard hProj hAO hNE ⟨hOutGe, hOutLt⟩ hOr hSound hE
