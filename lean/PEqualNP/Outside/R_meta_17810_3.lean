import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17810_3
    (hSingleActive :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        (2 : ℕ) ≤ x6.card →
        (∃ (x9 : ℕ) (x10 : ℕ), x9 ∈ x6 ∧ x10 ∈ x6 ∧ x9 ≠ x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x9) →
        (3 : ℕ) ≤ x7.card →
        ∀ x11 ⊆ x7, ∀ g0 ∈ x6,
          (2 : ℕ) ≤ x11.card →
          (1 : ℕ) + (x7 \ x11).card ≤ x6.card →
          x11 ⊆ PEqualNP.TopForm.gammaE x1 x2 g0 →
          (∀ g ∈ x6, g ≠ g0 → Disjoint x11 (PEqualNP.TopForm.gammaE x1 x2 g)) →
          (∀ x16 ∈ x7, ∃ x18 ∈ x6, x16 ∈ PEqualNP.TopForm.gammaE x1 x2 x18) →
          x11.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x11).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
    (hMultiActive :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        (2 : ℕ) ≤ x6.card →
        (∃ (x9 : ℕ) (x10 : ℕ), x9 ∈ x6 ∧ x10 ∈ x6 ∧ x9 ≠ x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x9) →
        (3 : ℕ) ≤ x7.card →
        ∀ x11 ⊆ x7, ∀ A ⊆ x6,
          (2 : ℕ) ≤ x11.card →
          (2 : ℕ) ≤ A.card →
          A.card + (x7 \ x11).card ≤ x6.card →
          x11 = A.biUnion (fun g => x11 ∩ PEqualNP.TopForm.gammaE x1 x2 g) →
          (∀ g ∈ A, (2 : ℕ) ≤ (x11 ∩ PEqualNP.TopForm.gammaE x1 x2 g).card) →
          (∀ g ∈ x6 \ A, Disjoint x11 (PEqualNP.TopForm.gammaE x1 x2 g)) →
          (∀ x16 ∈ x7, ∃ x18 ∈ x6, x16 ∈ PEqualNP.TopForm.gammaE x1 x2 x18) →
          x11.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x11).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         (2 : ℕ) ≤ x6.card → (∃ (x9 : ℕ) (x10 : ℕ), x9 ∈ x6 ∧ x10 ∈ x6 ∧ x9 ≠ x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x9) → (3 : ℕ) ≤ x7.card → ∀ x11 ⊆ x7, x11.Nonempty → (x7 \ x11).card ≤ {x14 ∈ x6 | Disjoint x11 (PEqualNP.TopForm.gammaE x1 x2 x14)}.card → (∀ x15 ∈ x6, (x11 ∩ PEqualNP.TopForm.gammaE x1 x2 x15).card ≠ (1 : ℕ)) → (∀ x16 ∈ x7, ∃ x18 ∈ x6, x16 ∈ PEqualNP.TopForm.gammaE x1 x2 x18) → x11.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x11).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  intro G C hSz hLeast hTF J U hJ2 hIncomp hU3 S hSub hSne hDisjLe hNe1 hCov
  let Γ : ℕ → Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.gammaE G C
  let A : Finset ℕ := J.filter (fun g => ¬Disjoint S (Γ g))
  let D : Finset ℕ := J.filter (fun g => Disjoint S (Γ g))
  have hAsub : A ⊆ J := Finset.filter_subset _ _
  have hAD : A.card + D.card = J.card := by
    have hDisjAD : Disjoint A D := by
      refine Finset.disjoint_left.mpr fun g hgA hgD => ?_
      exact (Finset.mem_filter.mp hgA).2 (Finset.mem_filter.mp hgD).2
    have hUnAD : A ∪ D = J := by
      ext g
      constructor
      · intro hg
        rcases Finset.mem_union.mp hg with hgA | hgD
        · exact (Finset.mem_filter.mp hgA).1
        · exact (Finset.mem_filter.mp hgD).1
      · intro hgJ
        by_cases hd : Disjoint S (Γ g)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hgJ, hd⟩))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hgJ, hd⟩))
    rw [← Finset.card_union_of_disjoint hDisjAD, hUnAD]
  have hD_le : (U \ S).card ≤ D.card := hDisjLe
  have hBudget : A.card + (U \ S).card ≤ J.card := by omega
  have hBiU : S = A.biUnion (fun g => S ∩ Γ g) := by
    ext e
    constructor
    · intro heS
      obtain ⟨g, hgJ, heg⟩ := hCov e (hSub heS)
      refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨hgJ, ?_⟩, Finset.mem_inter.mpr ⟨heS, heg⟩⟩
      intro hdj
      exact Finset.disjoint_left.mp hdj heS heg
    · intro heB
      obtain ⟨_, _, heI⟩ := Finset.mem_biUnion.mp heB
      exact (Finset.mem_inter.mp heI).1
  have hGe2 : ∀ g ∈ A, 2 ≤ (S ∩ Γ g).card := by
    intro g hgA
    have hgJ : g ∈ J := (Finset.mem_filter.mp hgA).1
    have hnd : ¬Disjoint S (Γ g) := (Finset.mem_filter.mp hgA).2
    have hpos : 0 < (S ∩ Γ g).card := by
      apply Finset.card_pos.mpr
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      exact hnd (Finset.disjoint_iff_inter_eq_empty.mpr hempty)
    have hne : (S ∩ Γ g).card ≠ 1 := hNe1 g hgJ
    omega
  have hDisjRest : ∀ g ∈ J \ A, Disjoint S (Γ g) := by
    intro g hg
    have hgJ : g ∈ J := (Finset.mem_sdiff.mp hg).1
    have hgNA : g ∉ A := (Finset.mem_sdiff.mp hg).2
    by_contra hnd
    exact hgNA (Finset.mem_filter.mpr ⟨hgJ, hnd⟩)
  have hAne : A.Nonempty := by
    obtain ⟨e, heS⟩ := hSne
    rw [hBiU] at heS
    obtain ⟨g, hgA, _⟩ := Finset.mem_biUnion.mp heS
    exact ⟨g, hgA⟩
  have hSge2 : 2 ≤ S.card := by
    obtain ⟨g, hgA⟩ := hAne
    exact le_trans (hGe2 g hgA) (Finset.card_le_card Finset.inter_subset_left)
  rcases Nat.lt_or_ge A.card 2 with hA1 | hA2
  · have hAeq1 : A.card = 1 := by
      have hpos := Finset.card_pos.mpr hAne
      omega
    obtain ⟨g0, hg0Eq⟩ := Finset.card_eq_one.mp hAeq1
    have hg0A : g0 ∈ A := by rw [hg0Eq]; exact Finset.mem_singleton_self g0
    have hg0J : g0 ∈ J := hAsub hg0A
    have hSsubG0 : S ⊆ Γ g0 := by
      intro e heS
      rw [hBiU, hg0Eq] at heS
      obtain ⟨g, hg, heI⟩ := Finset.mem_biUnion.mp heS
      rw [Finset.mem_singleton.mp hg] at heI
      exact (Finset.mem_inter.mp heI).2
    have hRest0 : ∀ g ∈ J, g ≠ g0 → Disjoint S (Γ g) := by
      intro g hgJ hne
      apply hDisjRest g
      rw [Finset.mem_sdiff, hg0Eq, Finset.mem_singleton]
      exact ⟨hgJ, hne⟩
    have hBud1 : 1 + (U \ S).card ≤ J.card := by omega
    exact hSingleActive C hSz hLeast hTF hJ2 hIncomp hU3 S hSub g0 hg0J hSge2 hBud1 hSsubG0 hRest0 hCov
  · exact hMultiActive C hSz hLeast hTF hJ2 hIncomp hU3 S hSub A hAsub hSge2 hA2 hBudget hBiU hGe2 hDisjRest hCov
