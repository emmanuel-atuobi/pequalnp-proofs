import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17171_3
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
        (2 : ℕ) ≤ x3.card →
        x4.Nonempty →
        x3 ⊆ x5 →
        x4 ⊆ x6 →
        x3.card + x6.card = x5.card + x4.card →
        (∀ x15 ∈ x3, ∃ x17 ∈ x4, x15 ∈ x7 x17) →
        (∀ x16 ∈ x4, (2 : ℕ) ≤ (x7 x16).card) →
        (∀ x17 ∈ x4, ∃ (x19 : Fin (11 : ℕ)), ∀ x20 ∈ x7 x17, x19 ∈ x20) →
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
        (2 : ℕ) ≤ x3.card →
        (2 : ℕ) ≤ x4.card →
        g0 ∈ x4 →
        x7 g0 = ∅ →
        x3 ⊆ x5 →
        x4 ⊆ x6 →
        x3.card + x6.card = x5.card + x4.card →
        (∀ x15 ∈ x3, ∃ x17 ∈ x4.erase g0, x15 ∈ x7 x17) →
        (∀ x16 ∈ x4.erase g0, (x7 x16).card ≠ (1 : ℕ)) →
        (∀ x17 ∈ x4.erase g0, ∃ (x19 : Fin (11 : ℕ)), ∀ x20 ∈ x7 x17, x19 ∈ x20) →
        x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),   have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;   have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;   x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (3 : ℕ) ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card → (∀ x15 ∈ x3, ∃ x17 ∈ x4, x15 ∈ x7 x17) → (∀ x16 ∈ x4, (x7 x16).card ≠ (1 : ℕ)) → (∀ x17 ∈ x4, ∃ (x19 : Fin (11 : ℕ)), ∀ x20 ∈ x7 x17, x19 ∈ x20) → x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  intro G C S A U J cov hSz hLeast hTF hJ3 hSU hAJ hEq hCov hNe1 hStar
  by_cases hSEmp : S = ∅
  · rw [hSEmp, Finset.card_empty]
    exact Nat.zero_le _
  · have hSNE : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSEmp
    obtain ⟨e0, he0⟩ := hSNE
    obtain ⟨g1, hg1A, he0In⟩ := hCov e0 he0
    have hANE : A.Nonempty := ⟨g1, hg1A⟩
    have hg1Pos : 1 ≤ (cov g1).card := Finset.Nonempty.card_pos ⟨e0, he0In⟩
    have hg1Ne1 : (cov g1).card ≠ 1 := hNe1 g1 hg1A
    have hg1Ge2 : 2 ≤ (cov g1).card := by omega
    have hCovSub : cov g1 ⊆ S := Finset.inter_subset_left
    have hSGe2 : 2 ≤ S.card := le_trans hg1Ge2 (Finset.card_le_card hCovSub)
    by_cases hIdle : ∃ g0 ∈ A, cov g0 = ∅
    · obtain ⟨g0, hg0A, hg0Emp⟩ := hIdle
      have hCovErase : ∀ e ∈ S, ∃ g ∈ A.erase g0, e ∈ cov g := by
        intro e he
        obtain ⟨g, hgA, heg⟩ := hCov e he
        refine ⟨g, Finset.mem_erase.mpr ⟨?_, hgA⟩, heg⟩
        intro heq
        rw [heq, hg0Emp] at heg
        exact Finset.notMem_empty e heg
      have hg1NeG0 : g1 ≠ g0 := by
        intro heq
        rw [heq, hg0Emp] at he0In
        exact Finset.notMem_empty e0 he0In
      have hAGe2 : 2 ≤ A.card := by
        have hsub : ({g0, g1} : Finset ℕ) ⊆ A := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hg0A
          · exact hg1A
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hg1NeG0.symm] at hc
        exact hc
      exact hHasIdle C S A g0 hSz hLeast hTF hJ3 hSGe2 hAGe2 hg0A hg0Emp hSU hAJ hEq hCovErase
        (fun g hg => hNe1 g (Finset.mem_of_mem_erase hg))
        (fun g hg => hStar g (Finset.mem_of_mem_erase hg))
    · have hAll2 : ∀ g ∈ A, 2 ≤ (cov g).card := by
        intro g hgA
        have hne0 : cov g ≠ ∅ := fun h0 => hIdle ⟨g, hgA, h0⟩
        have hpos : 1 ≤ (cov g).card := Finset.Nonempty.card_pos (Finset.nonempty_iff_ne_empty.mpr hne0)
        have hne1 : (cov g).card ≠ 1 := hNe1 g hgA
        omega
      exact hAllActive C S A hSz hLeast hTF hJ3 hSGe2 hANE hSU hAJ hEq hCov hAll2 hStar
