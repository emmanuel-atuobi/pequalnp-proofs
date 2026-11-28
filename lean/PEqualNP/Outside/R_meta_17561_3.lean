import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17561_3
    (hJunkThree :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (a b c : ℕ),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        PEqualNP.TopForm.junk x1 x2 = {a, b, c} →
        a ≠ b →
        a ≠ c →
        b ≠ c →
        PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 a b →
        (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) →
        (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card →
        (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (3 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
        (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (3 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
    (hJunkGe4 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (4 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        a ∈ PEqualNP.TopForm.junk x1 x2 →
        b ∈ PEqualNP.TopForm.junk x1 x2 →
        a ≠ b →
        PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 a b →
        (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) →
        (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card →
        (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
        (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ (PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∨ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7)) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  intro G C hSz hLeast hTF _ hPair hCov hU3 hLt hJ3
  have hOriented : ∃ a b : ℕ, a ∈ PEqualNP.TopForm.junk G C ∧ b ∈ PEqualNP.TopForm.junk G C ∧ a ≠ b ∧ PEqualNP.EdgeOwnership.InCone 11 C a b := by
    obtain ⟨u, v, hu, hv, huv, hcone⟩ := hPair
    rcases hcone with h1 | h2
    · exact ⟨u, v, hu, hv, huv, h1⟩
    · exact ⟨v, u, hv, hu, huv.symm, h2⟩
  obtain ⟨a, b, ha, hb, hab, hCone⟩ := hOriented
  rcases Nat.eq_or_lt_of_le hJ3 with hEq3 | hGt3
  · have hbEr : b ∈ (PEqualNP.TopForm.junk G C).erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    have hc1 : ((PEqualNP.TopForm.junk G C).erase a).card + 1 = (PEqualNP.TopForm.junk G C).card :=
      Finset.card_erase_add_one ha
    have hc2 : (((PEqualNP.TopForm.junk G C).erase a).erase b).card + 1 = ((PEqualNP.TopForm.junk G C).erase a).card :=
      Finset.card_erase_add_one hbEr
    have hcRem : (((PEqualNP.TopForm.junk G C).erase a).erase b).card = 1 := by omega
    obtain ⟨c, hcEq⟩ := Finset.card_eq_one.mp hcRem
    have hcMem : c ∈ ((PEqualNP.TopForm.junk G C).erase a).erase b := by rw [hcEq]; exact Finset.mem_singleton_self c
    have hcb : c ≠ b := (Finset.mem_erase.mp hcMem).1
    have hcErA : c ∈ (PEqualNP.TopForm.junk G C).erase a := (Finset.mem_erase.mp hcMem).2
    have hca : c ≠ a := (Finset.mem_erase.mp hcErA).1
    have hcJ : c ∈ PEqualNP.TopForm.junk G C := (Finset.mem_erase.mp hcErA).2
    have hJunkEq : PEqualNP.TopForm.junk G C = {a, b, c} := by
      ext z
      constructor
      · intro hz
        by_cases hza : z = a
        · rw [hza]; exact Finset.mem_insert_self a {b, c}
        · by_cases hzb : z = b
          · rw [hzb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self b {c})
          · have hzRem : z ∈ ((PEqualNP.TopForm.junk G C).erase a).erase b :=
              Finset.mem_erase.mpr ⟨hzb, Finset.mem_erase.mpr ⟨hza, hz⟩⟩
            rw [hcEq] at hzRem
            have hzc : z = c := Finset.mem_singleton.mp hzRem
            rw [hzc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
      · intro hz
        rcases Finset.mem_insert.mp hz with rfl | hz1
        · exact ha
        · rcases Finset.mem_insert.mp hz1 with rfl | hz2
          · exact hb
          · rw [Finset.mem_singleton.mp hz2]; exact hcJ
    have hCard3 : (PEqualNP.TopForm.junk G C).card = 3 := hEq3.symm
    rw [hCard3] at hLt ⊢
    exact hJunkThree C a b c hSz hLeast hTF hJunkEq hab hca.symm hcb.symm hCone hCov hU3 hLt
  · exact hJunkGe4 C a b hSz hLeast hTF hGt3 ha hb hab hCone hCov hU3 hLt
