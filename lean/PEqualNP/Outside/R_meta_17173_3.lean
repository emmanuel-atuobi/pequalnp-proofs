import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17173_3
    (hAllActive :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),
        have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (3 : ℕ) ≤ x6.card →
        x3 ⊆ x5 →
        x4 ⊆ x6 →
        x3.card + x6.card = x5.card + x4.card →
        (3 : ℕ) ≤ x3.card ∧ x4.Nonempty →
        (∀ x15 ∈ x3, ∃ x17 ∈ x4, x15 ∈ x7 x17) →
        (∀ x16 ∈ x4, (2 : ℕ) ≤ (x7 x16).card) →
        (∀ x17 ∈ x4, ∀ x19 ∈ x7 x17, ∀ x21 ∈ x7 x17, ¬Disjoint x19.toFinset x21.toFinset) →
        (∃ x18 ∈ x4, x7 x18 = {s((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), s((1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), s((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)))} ∨ x7 x18 = {s((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))), s((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), s((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))} ∨ x7 x18 = {s((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), s((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), s((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)))}) →
        x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
    (hHasIdle :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ) (g0 : ℕ),
        have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (3 : ℕ) ≤ x6.card →
        x3 ⊆ x5 →
        x4 ⊆ x6 →
        x3.card + x6.card = x5.card + x4.card →
        g0 ∈ x4 ∧ x7 g0 = ∅ ∧ (2 : ℕ) ≤ x4.card ∧ (3 : ℕ) ≤ x3.card →
        (∀ x15 ∈ x3, ∃ x17 ∈ x4.erase g0, x15 ∈ x7 x17) →
        (∀ x16 ∈ x4, (x7 x16).card ≠ (1 : ℕ)) →
        (∀ x17 ∈ x4, ∀ x19 ∈ x7 x17, ∀ x21 ∈ x7 x17, ¬Disjoint x19.toFinset x21.toFinset) →
        (∃ x18 ∈ x4.erase g0, x7 x18 = {s((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), s((1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), s((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)))} ∨ x7 x18 = {s((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))), s((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), s((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))} ∨ x7 x18 = {s((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), s((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), s((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)))}) →
        x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),   have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;   have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;   x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (3 : ℕ) ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card → (∀ x15 ∈ x3, ∃ x17 ∈ x4, x15 ∈ x7 x17) → (∀ x16 ∈ x4, (x7 x16).card ≠ (1 : ℕ)) → (∀ x17 ∈ x4, ∀ x19 ∈ x7 x17, ∀ x21 ∈ x7 x17, ¬Disjoint x19.toFinset x21.toFinset) → (∃ x18 ∈ x4, x7 x18 = {s((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), s((1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), s((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)))} ∨ x7 x18 = {s((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))), s((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), s((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))} ∨ x7 x18 = {s((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), s((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), s((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)))}) → x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  classical
  intro G C S A U J cov hSz hL hTF hJ3 hSU hAJ hEq hCov hNe1 hInt hTri
  obtain ⟨gt, hgtA, hgtTri⟩ := hTri
  have hAne : A.Nonempty := ⟨gt, hgtA⟩
  have hgtCard : (cov gt).card = 3 := by
    rcases hgtTri with h1 | h2 | h3
    · rw [h1]; decide
    · rw [h2]; decide
    · rw [h3]; decide
  have hS3 : 3 ≤ S.card := by
    have hsub : cov gt ⊆ S := Finset.inter_subset_left
    exact hgtCard ▸ Finset.card_le_card hsub
  by_cases hIdle : ∃ g0 ∈ A, cov g0 = ∅
  · obtain ⟨g0, hg0, hEmpty⟩ := hIdle
    have hgtNe : gt ≠ g0 := by
      intro hEqg
      rw [hEqg, hEmpty, Finset.card_empty] at hgtCard
      omega
    have hCov' : ∀ e ∈ S, ∃ g ∈ A.erase g0, e ∈ cov g := by
      intro e he
      obtain ⟨g, hg, heg⟩ := hCov e he
      have hne : g ≠ g0 := by
        intro hEqg
        rw [hEqg, hEmpty] at heg
        exact Finset.notMem_empty e heg
      exact ⟨g, Finset.mem_erase.mpr ⟨hne, hg⟩, heg⟩
    have hA2 : 2 ≤ A.card := by
      have hsub : ({g0, gt} : Finset ℕ) ⊆ A := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx1
        · exact hg0
        · rw [Finset.mem_singleton.mp hx1]; exact hgtA
      have hc : ({g0, gt} : Finset ℕ).card = 2 := Finset.card_pair hgtNe.symm
      exact hc ▸ Finset.card_le_card hsub
    exact hHasIdle C S A g0 hSz hL hTF hJ3 hSU hAJ hEq ⟨hg0, hEmpty, hA2, hS3⟩ hCov' hNe1 hInt
      ⟨gt, Finset.mem_erase.mpr ⟨hgtNe, hgtA⟩, hgtTri⟩
  · have hAct : ∀ g ∈ A, 2 ≤ (cov g).card := by
      intro g hg
      have hne0 : (cov g).card ≠ 0 := by
        intro h0
        exact hIdle ⟨g, hg, Finset.card_eq_zero.mp h0⟩
      have hne1 := hNe1 g hg
      omega
    exact hAllActive C S A hSz hL hTF hJ3 hSU hAJ hEq ⟨hS3, hAne⟩ hCov hAct hInt ⟨gt, hgtA, hgtTri⟩
