import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18629_3
    (hReadsInput :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p l : Fin (7 : ℕ)) (g a b : ℕ),
        C.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) C →
        (∀ h ∈ C.gates, h.inputs.Nodup) →
        PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines C →
        p ∈ PEqualNP.CircuitLowerBounds.fanoLines l →
        (2 : ℕ) ≤ C.lineDeg (14 : ℕ) {↑p} →
        (2 : ℕ) ≤ C.lineDeg (14 : ℕ) {(7 : ℕ) + ↑l} →
        g < C.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [a, b] →
        a ≠ b →
        a < (14 : ℕ) + g →
        b < (14 : ℕ) + g →
        (a < (14 : ℕ) ∨ b < (14 : ℕ)) →
        (2 : ℕ) ≤ List.count ((14 : ℕ) + g) (C.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates) →
        False)
    (hBothInternal :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p l : Fin (7 : ℕ)) (g a b : ℕ),
        C.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) C →
        (∀ h ∈ C.gates, h.inputs.Nodup) →
        PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines C →
        p ∈ PEqualNP.CircuitLowerBounds.fanoLines l →
        (2 : ℕ) ≤ C.lineDeg (14 : ℕ) {↑p} →
        (2 : ℕ) ≤ C.lineDeg (14 : ℕ) {(7 : ℕ) + ↑l} →
        g < C.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [a, b] →
        a ≠ b →
        (14 : ℕ) ≤ a →
        a < (14 : ℕ) + g →
        (14 : ℕ) ≤ b →
        b < (14 : ℕ) + g →
        (2 : ℕ) ≤ List.count ((14 : ℕ) + g) (C.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (7 : ℕ)), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 ∈ x1.gates, x6.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x1 → x2 ∈ PEqualNP.CircuitLowerBounds.fanoLines x3 → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2} → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x3} → (∃ x11 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (2 : ℕ) ≤ List.count ((14 : ℕ) + x11) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)) → False := by
  classical
  intro C p l hSz hAO hNd hComp hInc hDp hDl hWit
  obtain ⟨g, hglt, hgop, hcnt⟩ := hWit
  have hgmem : PEqualNP.MetaComplexity.NestedCover.gateAt C g ∈ C.gates := by
    change C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hglt]
    exact List.getElem_mem hglt
  have hlen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.length = 2 := hAO.2.2 _ hgmem
  have hndg : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.Nodup := hNd _ hgmem
  cases hinp : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs with
  | nil => rw [hinp] at hlen2; simp at hlen2
  | cons a rest =>
    cases rest with
    | nil => rw [hinp] at hlen2; simp at hlen2
    | cons b tail =>
      cases tail with
      | cons _ _ => rw [hinp] at hlen2; simp at hlen2
      | nil =>
        rw [hinp] at hndg
        have hab : a ≠ b := by
          simp only [List.nodup_cons, List.mem_singleton] at hndg
          exact hndg.1
        have ha_lt : a < 14 + g := hAO.2.1 g hglt a (by rw [hinp]; simp)
        have hb_lt : b < 14 + g := hAO.2.1 g hglt b (by rw [hinp]; simp)
        by_cases hIn : a < 14 ∨ b < 14
        · exact hReadsInput C p l g a b hSz hAO hNd hComp hInc hDp hDl hglt hgop hinp hab ha_lt hb_lt hIn hcnt
        · push Not at hIn
          exact hBothInternal C p l g a b hSz hAO hNd hComp hInc hDp hDl hglt hgop hinp hab hIn.1 ha_lt hIn.2 hb_lt hcnt
