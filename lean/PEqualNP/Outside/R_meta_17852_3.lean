import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17852_3
    (hEmpty :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        ∀ x9 ∈ x7,
          ∀ x11 ∈ x7,
            x9 ≠ x11 →
            PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x11 →
            have x15 : Finset ℕ := (x7.erase x9).erase x11;
            x15.Nonempty →
            x15.card + (2 : ℕ) = x7.card →
            x15.card < x6.card →
            x8 + (3 : ℕ) ≤ x6.card →
            x6 ⊆ x7.biUnion (PEqualNP.TopForm.gammaE x1 x2) →
            (∀ x24 ⊆ x15, x24.Nonempty → x24.card < (x6 ∩ x24.biUnion (PEqualNP.TopForm.gammaE x1 x2)).card) →
            x6.card ≤ x8 + x7.card)
    (hNonempty :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        ∀ x9 ∈ x7,
          ∀ x11 ∈ x7,
            x9 ≠ x11 →
            PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x11 →
            have x15 : Finset ℕ := (x7.erase x9).erase x11;
            have x16 : Finset ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x16 : Finset ℕ) => x6 ∩ x16.biUnion (PEqualNP.TopForm.gammaE x1 x2);
            ∀ x17 ⊆ x15,
              have x19 : Finset (Sym2 (Fin (11 : ℕ))) := x6 \ x16 x17;
              x17.Nonempty →
              (x15 \ x17).Nonempty →
              x17.card + (x15 \ x17).card + (2 : ℕ) = x7.card →
              (4 : ℕ) ≤ x7.card →
              (x15 \ x17).card < x19.card →
              (x16 x17).card ≤ x17.card →
              x8 + (3 : ℕ) ≤ x19.card →
              x19 ⊆ (x7 \ x17).biUnion (PEqualNP.TopForm.gammaE x1 x2) →
              (∀ x24 ⊆ x15 \ x17, x24.Nonempty → x24.card < (x19 ∩ x24.biUnion (PEqualNP.TopForm.gammaE x1 x2)).card) →
              x19.card ≤ x8 + (x7.card - (x16 x17).card)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;         ∀ x9 ∈ x7,           ∀ x11 ∈ x7,             x9 ≠ x11 →               PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x11 →                 have x15 : Finset ℕ := (x7.erase x9).erase x11;                 have x16 : Finset ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x16 : Finset ℕ) => x6 ∩ x16.biUnion (PEqualNP.TopForm.gammaE x1 x2);                 ∀ x17 ⊆ x15,                   have x19 : Finset (Sym2 (Fin (11 : ℕ))) := x6 \ x16 x17;                   (x15 \ x17).Nonempty → (x16 x17).card ≤ x17.card → x8 + (3 : ℕ) ≤ x19.card → x19 ⊆ (x7 \ x17).biUnion (PEqualNP.TopForm.gammaE x1 x2) → (∀ x24 ⊆ x15 \ x17, x24.Nonempty → x24.card < (x19 ∩ x24.biUnion (PEqualNP.TopForm.gammaE x1 x2)).card) → x19.card ≤ x8 + (x7.card - (x16 x17).card) := by
  classical
  intro G C hSz hLeast hTF U J c0 a ha b hb hab hCone R phi S hSR x19 hRemNE hPhiLe hU3 hCov hHall
  have hbInErase : b ∈ J.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hCard1 : (J.erase a).card + 1 = J.card := Finset.card_erase_add_one ha
  have hCard2 : R.card + 1 = (J.erase a).card := Finset.card_erase_add_one hbInErase
  have hRCard : R.card + 2 = J.card := by omega
  have hSDecomp : S.card + (R \ S).card = R.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSR
    omega
  have hThreeWay : S.card + (R \ S).card + 2 = J.card := by omega
  have hHallAll : (R \ S).card < (x19 ∩ (R \ S).biUnion (PEqualNP.TopForm.gammaE G C)).card :=
    hHall (R \ S) (Finset.Subset.refl _) hRemNE
  have hInterLe : (x19 ∩ (R \ S).biUnion (PEqualNP.TopForm.gammaE G C)).card ≤ x19.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hRemLtU : (R \ S).card < x19.card := lt_of_lt_of_le hHallAll hInterLe
  by_cases hSEmp : S = ∅
  · subst hSEmp
    have hPhiEmp : phi ∅ = ∅ := by
      change U ∩ (∅ : Finset ℕ).biUnion (PEqualNP.TopForm.gammaE G C) = ∅
      rw [Finset.biUnion_empty, Finset.inter_empty]
    have hUeq : x19 = U := by
      change U \ phi ∅ = U
      rw [hPhiEmp, Finset.sdiff_empty]
    have hReq : R \ ∅ = R := Finset.sdiff_empty
    have hJeq : J \ ∅ = J := Finset.sdiff_empty
    rw [hUeq, hPhiEmp, Finset.card_empty, Nat.sub_zero]
    rw [hReq] at hRemNE hHall hRemLtU
    rw [hUeq] at hU3 hCov hHall hRemLtU
    rw [hJeq] at hCov
    exact hEmpty C hSz hLeast hTF a ha b hb hab hCone hRemNE hRCard hRemLtU hU3 hCov hHall
  · have hSNE : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSEmp
    have hSpos : 1 ≤ S.card := Finset.Nonempty.card_pos hSNE
    have hRpos : 1 ≤ (R \ S).card := Finset.Nonempty.card_pos hRemNE
    have hJ4 : 4 ≤ J.card := by omega
    exact hNonempty C hSz hLeast hTF a ha b hb hab hCone S hSR hSNE hRemNE hThreeWay hJ4 hRemLtU hPhiLe hU3 hCov hHall
