import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17595_3
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        have x9 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x7;
        (x2.size ≤ (21 : ℕ) ∧
         PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
         PEqualNP.TopForm.centreless x1 x2 = ∅ ∧
         (6 : ℕ) ≤ x7.card ∧
         (11 : ℕ) ≤ x8 ∧
         x8 < (2 : ℕ) * x7.card ∧
         (5 : ℕ) ≤ x8 - x7.card ∧
         x8 - x7.card ≤ (6 : ℕ)) →
        (∃ (x15 : Fin (11 : ℕ)) (x16 : Fin (11 : ℕ)), x9.Adj x15 x16) ∧
        (x8 - x7.card = (5 : ℕ) → ∀ (x16 : Fin (11 : ℕ)), ∃ (x17 : Fin (11 : ℕ)) (x18 : Fin (11 : ℕ)), x9.Adj x17 x18 ∧ x16 ≠ x17 ∧ x16 ≠ x18))
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        have x9 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x7;
        (x2.size ≤ (21 : ℕ) ∧
         PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
         (PEqualNP.TopForm.centreless x1 x2).Nonempty ∧
         (6 : ℕ) ≤ x7.card ∧
         (11 : ℕ) ≤ x8 ∧
         x8 < (2 : ℕ) * x7.card ∧
         (5 : ℕ) ≤ x8 - x7.card ∧
         x8 - x7.card ≤ (6 : ℕ)) →
        (∃ (x15 : Fin (11 : ℕ)) (x16 : Fin (11 : ℕ)), x9.Adj x15 x16) ∧
        (x8 - x7.card = (5 : ℕ) → ∀ (x16 : Fin (11 : ℕ)), ∃ (x17 : Fin (11 : ℕ)) (x18 : Fin (11 : ℕ)), x9.Adj x17 x18 ∧ x16 ≠ x17 ∧ x16 ≠ x18)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           have x9 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x7;           (4 : ℕ) ≤ x8 → x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → (5 : ℕ) ≤ x8 - x7.card → x8 - x7.card ≤ (6 : ℕ) → (∃ (x15 : Fin (11 : ℕ)) (x16 : Fin (11 : ℕ)), x9.Adj x15 x16) ∧ (x8 - x7.card = (5 : ℕ) → ∀ (x16 : Fin (11 : ℕ)), ∃ (x17 : Fin (11 : ℕ)) (x18 : Fin (11 : ℕ)), x9.Adj x17 x18 ∧ x16 ≠ x17 ∧ x16 ≠ x18) := by
  classical
  intro x1 x2 hSz hLeast hTF hJ2 x7 x8 x9 h4 hLe hLt hGe5 hLe6
  have hU6 : 6 ≤ x7.card := by omega
  have hB11 : 11 ≤ x8 := by omega
  by_cases hc : PEqualNP.TopForm.centreless x1 x2 = ∅
  · have hc0 : (PEqualNP.TopForm.centreless x1 x2).card = 0 := by
      rw [hc]
      exact Finset.card_empty
    have hx8eq : x8 = (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
      change 2 * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card +
        (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card = _
      rw [hc0]
      omega
    have hRes := hNoCentreless x2 ⟨hSz, hLeast, hTF, hJ2, hc, hU6,
      hx8eq ▸ hB11, hx8eq ▸ hLt, hx8eq ▸ hGe5, hx8eq ▸ hLe6⟩
    exact ⟨hRes.1, fun h5 => hRes.2 (hx8eq ▸ h5)⟩
  · have hcNE : (PEqualNP.TopForm.centreless x1 x2).Nonempty := Finset.nonempty_iff_ne_empty.mpr hc
    exact hHasCentreless x2 ⟨hSz, hLeast, hTF, hJ2, hcNE, hU6, hB11, hLt, hGe5, hLe6⟩
