import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8059_4
    (hNoNestedAnd :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),
        have x6 : ℕ := (25 : ℕ) + x4.size;
        (PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 ∧ (26 : ℕ) ≤ x5 ∧ x5 < x6) →
        (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x1 x12 → x3 x4 x5 (x2 {x11} {x12}) = Bool.true ∨ x3 x4 x6 (x2 {x11} {x12}) = Bool.true) →
        (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x12 → (x3 x4 x5 (x2 x12 (PEqualNP.HeptadCover.missLines x1 x12)) || x3 x4 x6 (x2 x12 (PEqualNP.HeptadCover.missLines x1 x12))) = Bool.false) →
        (∀ (x13 : Bool), ∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 ∧ x3 x4 x5 (x2 {x14} {x15}) = x13 ∧ x3 x4 x6 (x2 {x14} {x15}) = !x13) →
        (∀ j < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs, (26 : ℕ) ≤ u → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (u - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (63 : ℕ) ≤ x4.size)
    (hUniqueNestedAnd :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 g0 u0 : ℕ),
        have x6 : ℕ := (25 : ℕ) + x4.size;
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x4;
        (PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 ∧ (26 : ℕ) ≤ x5 ∧ x5 < x6 ∧ g0 < x4.size ∧ (26 : ℕ) ≤ u0 ∧ u0 < (26 : ℕ) + g0 ∧ (ga g0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ u0 ∈ (ga g0).inputs ∧ (ga (u0 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (∀ j < x4.size, j ≠ g0 → (ga j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u ∈ (ga j).inputs, (26 : ℕ) ≤ u → (ga (u - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x1 x12 → x3 x4 x5 (x2 {x11} {x12}) = Bool.true ∨ x3 x4 x6 (x2 {x11} {x12}) = Bool.true) →
        (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x12 → (x3 x4 x5 (x2 x12 (PEqualNP.HeptadCover.missLines x1 x12)) || x3 x4 x6 (x2 x12 (PEqualNP.HeptadCover.missLines x1 x12))) = Bool.false) →
        (∀ (x13 : Bool), ∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 ∧ x3 x4 x5 (x2 {x14} {x15}) = x13 ∧ x3 x4 x6 (x2 {x14} {x15}) = !x13) →
        (63 : ℕ) ≤ x4.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),   have x6 : ℕ := (25 : ℕ) + x4.size;   PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → (26 : ℕ) ≤ x5 → x5 < x6 → (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x1 x12 → x3 x4 x5 (x2 {x11} {x12}) = Bool.true ∨ x3 x4 x6 (x2 {x11} {x12}) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x12 → (x3 x4 x5 (x2 x12 (PEqualNP.HeptadCover.missLines x1 x12)) || x3 x4 x6 (x2 x12 (PEqualNP.HeptadCover.missLines x1 x12))) = Bool.false) → (∀ (x13 : Bool), ∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 ∧ x3 x4 x5 (x2 {x14} {x15}) = x13 ∧ x3 x4 x6 (x2 {x14} {x15}) = !x13) → {x14 : ℕ | x14 < x4.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).inputs, (26 : ℕ) ≤ x15 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x15 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and}.encard ≤ (1 : ℕ∞) → (63 : ℕ) ≤ x4.size := by
  classical
  intro x1 x2 x3 x4 x5 x6 hMono hRB hx5Lo hx5Hi hPos hQuad hComp hNest
  let S : Set ℕ := {x14 : ℕ | x14 < x4.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).inputs, (26 : ℕ) ≤ x15 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x15 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and}
  have hOp : ∀ k < x4.size,
      (PEqualNP.MetaComplexity.NestedCover.gateAt x4 k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x4 k).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro k hk
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt x4 k = x4.gates[k] :=
      List.getD_eq_getElem _ _ hk
    rw [hge]
    have hm := (hMono x4.gates[k] (List.getElem_mem hk)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  have hNotInS : ∀ j < x4.size, j ∉ S →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs, (26 : ℕ) ≤ u →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (u - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro j hj hjNot hAnd u hu hu26
    have huLt : u < 26 + j := hRB j hj u hu
    rcases hOp (u - 26) (by omega) with hUAnd | hUOr
    · exact False.elim (hjNot ⟨hj, hAnd, u, hu, hu26, hUAnd⟩)
    · exact hUOr
  rcases Set.eq_empty_or_nonempty S with hE | ⟨g0, hg0⟩
  · refine hNoNestedAnd x4 x5 ⟨hMono, hRB, hx5Lo, hx5Hi⟩ hPos hQuad hComp ?_
    intro j hj
    exact hNotInS j hj (by rw [hE]; exact Set.notMem_empty j)
  · have hg0S : g0 ∈ S := hg0
    obtain ⟨hg0Lt, hg0And, u0, hu0Mem, hu0Ge, hu0And⟩ := hg0
    have hu0Lt : u0 < 26 + g0 := hRB g0 hg0Lt u0 hu0Mem
    have hOther : ∀ j < x4.size, j ≠ g0 →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs, (26 : ℕ) ≤ u →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (u - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro j hj hne
      apply hNotInS j hj
      intro hjS
      exact hne (Set.encard_le_one_iff.mp hNest j g0 hjS hg0S)
    exact hUniqueNestedAnd x4 x5 g0 u0 ⟨hMono, hRB, hx5Lo, hx5Hi, hg0Lt, hu0Ge, hu0Lt, hg0And, hu0Mem, hu0And⟩ hOther hPos hQuad hComp
