import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7971_3
    (hHasOr :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) x2 ∧ x2.toRight.card ≤ (3 : ℕ) ∧ (∀ (x3 : Fin (13 : ℕ)), (x2.toLeft ∩ x1 x3).card ≤ (2 : ℕ)) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2.toRight | x3 ∈ x1 x4}.card ≤ (2 : ℕ);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (x3.wires (PEqualNP.GenericRejection.incidenceInput x5.toLeft x5.toRight)).getD x4 Bool.false;
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ¬∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6;
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧ x4 x5 →
        (26 : ℕ) ≤ x6 ∧ (26 : ℕ) ≤ x7 ∧ x7 < (26 : ℕ) + x5.size ∧ x6 ≠ x7 ∧ PEqualNP.ReadTwo.isOr x5 (x6 - (26 : ℕ)) →
        have R : ℕ → Prop := fun w => PEqualNP.GenericRejection.RightOnIncidentPairs x1 { gates := x5.gates, output := w };
        R x6 ∧ R x7 →
        (∀ (x12 x13 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x12.card ≤ (2 : ℕ) → x13.card ≤ (2 : ℕ) → x2 (x12 ∪ x13) → (x3 x5 x6 x12 && x3 x5 x7 x13) = Bool.false) →
        (∀ x13 ∈ [x6, x7], ∃ (x15 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x15.card ≤ (2 : ℕ) ∧ x2 x15 ∧ x3 x5 x13 x15 = Bool.true) →
        (63 : ℕ) ≤ x5.size)
    (hBothAnd :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) x2 ∧ x2.toRight.card ≤ (3 : ℕ) ∧ (∀ (x3 : Fin (13 : ℕ)), (x2.toLeft ∩ x1 x3).card ≤ (2 : ℕ)) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2.toRight | x3 ∈ x1 x4}.card ≤ (2 : ℕ);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (x3.wires (PEqualNP.GenericRejection.incidenceInput x5.toLeft x5.toRight)).getD x4 Bool.false;
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ¬∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6;
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧ x4 x5 →
        (26 : ℕ) ≤ x6 ∧ x6 < x7 ∧ PEqualNP.ReadTwo.isAnd x5 (x6 - (26 : ℕ)) ∧ PEqualNP.ReadTwo.isAnd x5 (x7 - (26 : ℕ)) →
        have R : ℕ → Prop := fun w => PEqualNP.GenericRejection.RightOnIncidentPairs x1 { gates := x5.gates, output := w };
        R x6 ∧ R x7 →
        (∀ (x12 x13 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x12.card ≤ (2 : ℕ) → x13.card ≤ (2 : ℕ) → x2 (x12 ∪ x13) → (x3 x5 x6 x12 && x3 x5 x7 x13) = Bool.false) →
        (∀ x13 ∈ [x6, x7], ∃ (x15 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x15.card ≤ (2 : ℕ) ∧ x2 x15 ∧ x3 x5 x13 x15 = Bool.true) →
        (63 : ℕ) ≤ x5.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) x2 ∧ x2.toRight.card ≤ (3 : ℕ) ∧ (∀ (x3 : Fin (13 : ℕ)), (x2.toLeft ∩ x1 x3).card ≤ (2 : ℕ)) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2.toRight | x3 ∈ x1 x4}.card ≤ (2 : ℕ); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (x3.wires (PEqualNP.GenericRejection.incidenceInput x5.toLeft x5.toRight)).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ¬∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x5 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 →       x4 x5 →         (∀ (x11 x12 : Fin (13 : ℕ)),             x11 ∈ x1 x12 →               have x14 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) := {Sum.inl x11, Sum.inr x12};               (x3 x5 x6 x14 && x3 x5 x7 x14) = Bool.true) →           (∀ (x12 x13 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x12.card ≤ (2 : ℕ) → x13.card ≤ (2 : ℕ) → x2 (x12 ∪ x13) → (x3 x5 x6 x12 && x3 x5 x7 x13) = Bool.false) → (∀ x13 ∈ [x6, x7], ∃ (x15 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x15.card ≤ (2 : ℕ) ∧ x2 x15 ∧ x3 x5 x13 x15 = Bool.true) → (63 : ℕ) ≤ x5.size := by
  dsimp only
  intro C w1 w2 hM hRB hNoNest hPos hNeg hWit
  have hPairLR : ∀ p l : Fin 13,
      ({Sum.inl p, Sum.inr l} : Finset (Fin 13 ⊕ Fin 13)).toLeft = {p} ∧
      ({Sum.inl p, Sum.inr l} : Finset (Fin 13 ⊕ Fin 13)).toRight = {l} := by
    intro p l
    constructor
    · ext q; simp
    · ext q; simp
  have hR1 : PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := C.gates, output := w1 } := by
    intro l p hpl
    have h1 := hPos p l hpl
    rw [(hPairLR p l).1, (hPairLR p l).2, Bool.and_eq_true] at h1
    exact h1.1
  have hR2 : PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := C.gates, output := w2 } := by
    intro l p hpl
    have h1 := hPos p l hpl
    rw [(hPairLR p l).1, (hPairLR p l).2, Bool.and_eq_true] at h1
    exact h1.2
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
  have hLen26 : ∀ (A B : Finset (Fin 13)), (PEqualNP.GenericRejection.incidenceInput A B).length = 26 := by
    intro A B
    change (List.ofFn (fun i : Fin 13 => decide (i ∈ A)) ++ List.ofFn (fun j : Fin 13 => decide (j ∈ B))).length = 26
    simp only [List.length_append, List.length_ofFn]
  have h00 : (0 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have h10 : (1 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have h11 : (1 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 1 := by decide
  have hWBounds : ∀ w : ℕ,
      PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := C.gates, output := w } →
      26 ≤ w ∧ w < 26 + C.size := by
    intro w hR
    have hLt : w < 26 + C.size := by
      by_contra hge
      have hge : 26 + C.size ≤ w := Nat.le_of_not_lt hge
      have hT := hR 0 0 h00
      change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)})).getD w false = true at hT
      have hL : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)})).length = 26 + C.size := by
        rw [hLen, hLen26]; rfl
      have hF : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)})).getD w false = false :=
        List.getD_eq_default _ _ (by omega)
      rw [hF] at hT
      exact Bool.noConfusion hT
    have hGe : 26 ≤ w := by
      by_contra hlt
      have hlt : w < 26 := Nat.lt_of_not_ge hlt
      by_cases h13 : w < 13
      · by_cases h0 : w = 0
        · have hT := hR 0 1 h10
          change (C.gates.foldl step _).getD w false = true at hT
          rw [hPref C.gates _ w (by rw [hLen26]; exact hlt), h0] at hT
          have hF : (PEqualNP.GenericRejection.incidenceInput ({(1 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD 0 false = false := by decide
          rw [hF] at hT
          exact Bool.noConfusion hT
        · have hT := hR 0 0 h00
          change (C.gates.foldl step _).getD w false = true at hT
          rw [hPref C.gates _ w (by rw [hLen26]; exact hlt)] at hT
          have hF : ∀ i : Fin 13, i.val ≠ 0 →
              (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD i.val false = false := by decide
          rw [hF ⟨w, h13⟩ h0] at hT
          exact Bool.noConfusion hT
      · by_cases h13eq : w = 13
        · have hT := hR 1 1 h11
          change (C.gates.foldl step _).getD w false = true at hT
          rw [hPref C.gates _ w (by rw [hLen26]; exact hlt), h13eq] at hT
          have hF : (PEqualNP.GenericRejection.incidenceInput ({(1 : Fin 13)} : Finset (Fin 13)) {(1 : Fin 13)}).getD 13 false = false := by decide
          rw [hF] at hT
          exact Bool.noConfusion hT
        · have hT := hR 0 0 h00
          change (C.gates.foldl step _).getD w false = true at hT
          rw [hPref C.gates _ w (by rw [hLen26]; exact hlt)] at hT
          have hF : ∀ i : Fin 26, 13 < i.val →
              (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD i.val false = false := by decide
          rw [hF ⟨w, hlt⟩ (by show 13 < w; omega)] at hT
          exact Bool.noConfusion hT
    exact ⟨hGe, hLt⟩
  obtain ⟨hw1Ge, hw1Lt⟩ := hWBounds w1 hR1
  obtain ⟨hw2Ge, hw2Lt⟩ := hWBounds w2 hR2
  have hNe : w1 ≠ w2 := by
    intro hEq
    obtain ⟨S, hScard, hSfree, hStrue⟩ := hWit w1 List.mem_cons_self
    have hF := hNeg S S hScard hScard (by rw [Finset.union_idempotent]; exact hSfree)
    rw [← hEq, hStrue] at hF
    exact Bool.noConfusion hF
  have hk1 : w1 - 26 < C.gates.length := by change w1 - 26 < C.size; omega
  have hk2 : w2 - 26 < C.gates.length := by change w2 - 26 < C.size; omega
  have hga1 : PEqualNP.MetaComplexity.NestedCover.gateAt C (w1 - 26) = C.gates[w1 - 26]'hk1 :=
    List.getD_eq_getElem _ _ hk1
  have hga2 : PEqualNP.MetaComplexity.NestedCover.gateAt C (w2 - 26) = C.gates[w2 - 26]'hk2 :=
    List.getD_eq_getElem _ _ hk2
  have hNegSwap : ∀ (x12 x13 : Finset (Fin 13 ⊕ Fin 13)),
      x12.card ≤ 2 → x13.card ≤ 2 →
      (PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) (x12 ∪ x13) ∧
       (x12 ∪ x13).toRight.card ≤ 3 ∧
       (∀ x3 : Fin 13, ((x12 ∪ x13).toLeft ∩ PEqualNP.HeptadCover.singerLines3 x3).card ≤ 2) ∧
       ∀ x3 : Fin 13, {x4 ∈ (x12 ∪ x13).toRight | x3 ∈ PEqualNP.HeptadCover.singerLines3 x4}.card ≤ 2) →
      ((C.wires (PEqualNP.GenericRejection.incidenceInput x12.toLeft x12.toRight)).getD w2 false &&
       (C.wires (PEqualNP.GenericRejection.incidenceInput x13.toLeft x13.toRight)).getD w1 false) = false := by
    intro S T hS hT hFree
    rw [Bool.and_comm]
    exact hNeg T S hT hS (by rw [Finset.union_comm]; exact hFree)
  have hWitSwap : ∀ w ∈ [w2, w1],
      ∃ S : Finset (Fin 13 ⊕ Fin 13), S.card ≤ 2 ∧
        (PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) S ∧
         S.toRight.card ≤ 3 ∧
         (∀ x3 : Fin 13, (S.toLeft ∩ PEqualNP.HeptadCover.singerLines3 x3).card ≤ 2) ∧
         ∀ x3 : Fin 13, {x4 ∈ S.toRight | x3 ∈ PEqualNP.HeptadCover.singerLines3 x4}.card ≤ 2) ∧
        (C.wires (PEqualNP.GenericRejection.incidenceInput S.toLeft S.toRight)).getD w false = true := by
    intro w hw
    rcases List.mem_cons.mp hw with hEq | hw'
    · rw [hEq]
      exact hWit w2 (List.mem_cons_of_mem w1 List.mem_cons_self)
    · rw [List.mem_singleton.mp hw']
      exact hWit w1 List.mem_cons_self
  rcases (hM (C.gates[w1 - 26]'hk1) (List.getElem_mem hk1)).1 with h1And | h1Or
  · rcases (hM (C.gates[w2 - 26]'hk2) (List.getElem_mem hk2)).1 with h2And | h2Or
    · rcases Nat.lt_or_gt_of_ne hNe with h12 | h21
      · exact hBothAnd C w1 w2 ⟨hM, hRB, hNoNest⟩ ⟨hw1Ge, h12, ⟨hk1, by rw [hga1]; exact h1And⟩, ⟨hk2, by rw [hga2]; exact h2And⟩⟩
          ⟨hR1, hR2⟩ hNeg hWit
      · exact hBothAnd C w2 w1 ⟨hM, hRB, hNoNest⟩ ⟨hw2Ge, h21, ⟨hk2, by rw [hga2]; exact h2And⟩, ⟨hk1, by rw [hga1]; exact h1And⟩⟩
          ⟨hR2, hR1⟩ hNegSwap hWitSwap
    · exact hHasOr C w2 w1 ⟨hM, hRB, hNoNest⟩ ⟨hw2Ge, hw1Ge, hw1Lt, hNe.symm, ⟨hk2, by rw [hga2]; exact h2Or⟩⟩
        ⟨hR2, hR1⟩ hNegSwap hWitSwap
  · exact hHasOr C w1 w2 ⟨hM, hRB, hNoNest⟩ ⟨hw1Ge, hw2Ge, hw2Lt, hNe, ⟨hk1, by rw [hga1]; exact h1Or⟩⟩
      ⟨hR1, hR2⟩ hNeg hWit
