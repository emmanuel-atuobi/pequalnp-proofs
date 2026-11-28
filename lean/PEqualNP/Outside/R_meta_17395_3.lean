import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17395_3
    (hComparable :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        (x2.size ≤ (21 : ℕ) ∧
         PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         PEqualNP.TopForm.junk x1 x2 = {a, b} ∧
         a ≠ b ∧
         PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 a b ∧
         (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).Nonempty ∧
         ((PEqualNP.TopForm.centreless x1 x2).Nonempty ∨ (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) ∧
         (3 : ℕ) ≤ x7.card ∧
         x7.card ≤ x8 ∧
         x8 < (2 : ℕ) * x7.card ∧
         x8 - x7.card < (7 : ℕ) ∧
         (∀ (x15 : Finset (Fin (11 : ℕ))), (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x7 → x16 ∈ x15 ∨ x17 ∈ x15) → x8 - x7.card < x15.card)) →
        ∃ (x16 : Finset (Fin (11 : ℕ))) (x17 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x16 ∧ x1.IsVertexCover ↑(x16 ∪ x17) ∧ x17.card ≤ x8 - x7.card)
    (hIncomparable :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        (x2.size ≤ (21 : ℕ) ∧
         PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         PEqualNP.TopForm.junk x1 x2 = {a, b} ∧
         a ≠ b ∧
         ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 a b ∧
         ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 b a ∧
         (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).Nonempty ∧
         ((PEqualNP.TopForm.centreless x1 x2).Nonempty ∨ (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) ∧
         (3 : ℕ) ≤ x7.card ∧
         x7.card ≤ x8 ∧
         x8 < (2 : ℕ) * x7.card ∧
         x8 - x7.card < (7 : ℕ) ∧
         (∀ (x15 : Finset (Fin (11 : ℕ))), (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x7 → x16 ∈ x15 ∨ x17 ∈ x15) → x8 - x7.card < x15.card)) →
        ∃ (x16 : Finset (Fin (11 : ℕ))) (x17 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x16 ∧ x1.IsVertexCover ↑(x16 ∪ x17) ∧ x17.card ≤ x8 - x7.card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).Nonempty → (PEqualNP.TopForm.centreless x1 x2).Nonempty ∨ (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card → (4 : ℕ) ≤ x8 → x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → x8 - x7.card < (7 : ℕ) → (∀ (x15 : Finset (Fin (11 : ℕ))), (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x7 → x16 ∈ x15 ∨ x17 ∈ x15) → x8 - x7.card < x15.card) → ∃ (x16 : Finset (Fin (11 : ℕ))) (x17 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x16 ∧ x1.IsVertexCover ↑(x16 ∪ x17) ∧ x17.card ≤ x8 - x7.card := by
  intro G C hSz hLeast hTF hJ2 U x8 hOrNE hDisj h4 hLe hLt2 hSub7 hCov
  obtain ⟨a, b, hab, hJunk⟩ := Finset.card_eq_two.mp hJ2
  have hU3 : 3 ≤ U.card := by omega
  have hx8Eq : x8 = 2 * (PEqualNP.TopForm.centreless G C).card + 2 + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card := by
    change 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card = _
    rw [hJ2]
  rw [hx8Eq] at hLe hLt2 hSub7 hCov ⊢
  by_cases h1 : PEqualNP.EdgeOwnership.InCone 11 C a b
  · exact hComparable C a b ⟨hSz, hLeast, hTF, hJunk, hab, h1, hOrNE, hDisj, hU3, hLe, hLt2, hSub7, hCov⟩
  · by_cases h2 : PEqualNP.EdgeOwnership.InCone 11 C b a
    · have hJunk' : PEqualNP.TopForm.junk G C = {b, a} := by rw [hJunk, Finset.pair_comm]
      exact hComparable C b a ⟨hSz, hLeast, hTF, hJunk', hab.symm, h2, hOrNE, hDisj, hU3, hLe, hLt2, hSub7, hCov⟩
    · exact hIncomparable C a b ⟨hSz, hLeast, hTF, hJunk, hab, h1, h2, hOrNE, hDisj, hU3, hLe, hLt2, hSub7, hCov⟩
