import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8387_4
    (hNoJunk :
      ∀ (n : ℕ) (G : SimpleGraph (Fin (n + n))) [DecidableRel G.Adj]
        (mate : Fin (n + n) → Fin (n + n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (3 : ℕ) ≤ n →
        PEqualNP.TopForm.NoFourCycle G →
        (∀ a b : Fin n, ¬G.Adj (Fin.castAdd n a) (Fin.castAdd n b)) →
        (∀ a b : Fin n, ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b)) →
        Function.Involutive mate →
        (∀ u : Fin (n + n), G.Adj u (mate u)) →
        (∀ u : Fin (n + n), ∃ v : Fin (n + n), G.Adj u v ∧ v ≠ mate u) →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        PEqualNP.TopForm.junk G C = ∅ →
        (PEqualNP.TopForm.Ustar G C).card + n ≤
          (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
          (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card)
    (hHasJunk :
      ∀ (n : ℕ) (G : SimpleGraph (Fin (n + n))) [DecidableRel G.Adj]
        (mate : Fin (n + n) → Fin (n + n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (3 : ℕ) ≤ n →
        PEqualNP.TopForm.NoFourCycle G →
        (∀ a b : Fin n, ¬G.Adj (Fin.castAdd n a) (Fin.castAdd n b)) →
        (∀ a b : Fin n, ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b)) →
        Function.Involutive mate →
        (∀ u : Fin (n + n), G.Adj u (mate u)) →
        (∀ u : Fin (n + n), ∃ v : Fin (n + n), G.Adj u v ∧ v ≠ mate u) →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (PEqualNP.TopForm.junk G C).Nonempty →
        (PEqualNP.TopForm.Ustar G C).card + n ≤
          (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
          (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin (x1 + x1))) [x3 : DecidableRel x2.Adj] (x4 : Fin (x1 + x1) → Bool) (x5 : Fin (x1 + x1) → Fin (x1 + x1)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → (∀ (x8 x9 : Fin x1), ¬x2.Adj (Fin.castAdd x1 x8) (Fin.castAdd x1 x9)) → (∀ (x9 x10 : Fin x1), ¬x2.Adj (Fin.natAdd x1 x9) (Fin.natAdd x1 x10)) → (∀ (x10 x11 : Fin (x1 + x1)), x2.Adj x10 x11 → x4 x10 ≠ x4 x11) → Function.Involutive x5 → (∀ (x12 : Fin (x1 + x1)), x2.Adj x12 (x5 x12)) → (∀ (x13 : Fin (x1 + x1)), ∃ (x14 : Fin (x1 + x1)), x2.Adj x13 x14 ∧ x14 ≠ x5 x13) → (∀ (x14 : Fin (x1 + x1)), ∃ (x15 : Fin (x1 + x1)), x2.Adj x15 x14 ∧ x15 ≠ x5 x14) → PEqualNP.TopForm.IsLeastAO x2 x6 → PEqualNP.TopForm.TopForm x2 x6 → (PEqualNP.TopForm.Ustar x2 x6).card + x1 ≤ (PEqualNP.TopForm.tops x2 x6 \ PEqualNP.TopForm.centreless x2 x6).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x6).card + (PEqualNP.TopForm.junk x2 x6).card + (PEqualNP.TopForm.orN x2 x6 \ PEqualNP.TopForm.lam x2 x6).card := by
  classical
  intro n G _ _col mate C hC4 hIndL hIndR _hCol hInv hMate hDeg2 _hDeg2' hLeast hTF
  by_cases hn0 : n = 0
  · subst hn0
    have hU0 : PEqualNP.TopForm.Ustar G C = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e _
      exact Sym2.ind (fun a _ => Fin.elim0 a) e
    rw [hU0, Finset.card_empty]
    omega
  have hL_to_R : ∀ (a : Fin n) (w : Fin (n + n)), G.Adj (Fin.castAdd n a) w → ∃ b : Fin n, w = Fin.natAdd n b := by
    intro a w haw
    by_cases hlt : w.val < n
    · exfalso
      have hw : w = Fin.castAdd n ⟨w.val, hlt⟩ := by ext; rfl
      rw [hw] at haw
      exact hIndL a ⟨w.val, hlt⟩ haw
    · refine ⟨⟨w.val - n, by omega⟩, ?_⟩
      ext
      simp only [Fin.val_natAdd]
      omega
  have hn_ne1 : n ≠ 1 := by
    intro h1
    subst h1
    let a0 : Fin 1 := ⟨0, by omega⟩
    obtain ⟨b1, hb1⟩ := hL_to_R a0 (mate (Fin.castAdd 1 a0)) (hMate (Fin.castAdd 1 a0))
    obtain ⟨v, hav, hvne⟩ := hDeg2 (Fin.castAdd 1 a0)
    obtain ⟨b2, hb2⟩ := hL_to_R a0 v hav
    have hbeq : b2 = b1 := Subsingleton.elim b2 b1
    exact hvne (hb2.trans (by rw [hbeq, ← hb1]))
  have hn_ne2 : n ≠ 2 := by
    intro h2
    subst h2
    let a0 : Fin 2 := ⟨0, by omega⟩
    let a1 : Fin 2 := ⟨1, by omega⟩
    let b0 : Fin 2 := ⟨0, by omega⟩
    let b1 : Fin 2 := ⟨1, by omega⟩
    have hall : ∀ a : Fin 2, G.Adj (Fin.castAdd 2 a) (Fin.natAdd 2 b0) ∧ G.Adj (Fin.castAdd 2 a) (Fin.natAdd 2 b1) := by
      intro a
      obtain ⟨r1, hr1⟩ := hL_to_R a (mate (Fin.castAdd 2 a)) (hMate (Fin.castAdd 2 a))
      obtain ⟨v, hav, hvne⟩ := hDeg2 (Fin.castAdd 2 a)
      obtain ⟨r2, hr2⟩ := hL_to_R a v hav
      have hrne : r2 ≠ r1 := fun heq => hvne (hr2.trans (by rw [heq, ← hr1]))
      have ha1 : G.Adj (Fin.castAdd 2 a) (Fin.natAdd 2 r1) := by rw [← hr1]; exact hMate _
      have ha2 : G.Adj (Fin.castAdd 2 a) (Fin.natAdd 2 r2) := by rw [← hr2]; exact hav
      have hfin2 : ∀ r : Fin 2, r = b0 ∨ r = b1 := by
        intro r
        rcases Nat.lt_succ_iff_lt_or_eq.mp r.isLt with hlt | heq
        · left; ext; simp only [b0]; omega
        · right; ext; simp only [b1]; omega
      rcases hfin2 r1 with rfl | rfl
      · rcases hfin2 r2 with hbad | rfl
        · exact absurd hbad hrne
        · exact ⟨ha1, ha2⟩
      · rcases hfin2 r2 with rfl | hbad
        · exact ⟨ha2, ha1⟩
        · exact absurd hbad hrne
    have h0 := hall a0
    have h1 := hall a1
    have hneA : Fin.castAdd 2 a0 ≠ Fin.castAdd 2 a1 := by
      intro heq
      have := congrArg Fin.val heq
      simp only [Fin.val_castAdd, a0, a1] at this
      omega
    have hneB : Fin.natAdd 2 b0 ≠ Fin.natAdd 2 b1 := by
      intro heq
      have := congrArg Fin.val heq
      simp only [Fin.val_natAdd, b0, b1] at this
      omega
    have hsub : ({Fin.natAdd 2 b0, Fin.natAdd 2 b1} : Finset (Fin (2 + 2))) ⊆
        Finset.univ.filter (fun w => G.Adj (Fin.castAdd 2 a0) w ∧ G.Adj (Fin.castAdd 2 a1) w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨h0.1, h1.1⟩
      · exact ⟨h0.2, h1.2⟩
    have hc1 := hC4 (Fin.castAdd 2 a0) (Fin.castAdd 2 a1) hneA
    have hc2 : ({Fin.natAdd 2 b0, Fin.natAdd 2 b1} : Finset (Fin (2 + 2))).card = 2 :=
      Finset.card_pair hneB
    have hc3 := Finset.card_le_card hsub
    omega
  have hn3 : (3 : ℕ) ≤ n := by omega
  by_cases hj : PEqualNP.TopForm.junk G C = ∅
  · have h := @hNoJunk n G _ mate C hn3 hC4 hIndL hIndR hInv hMate hDeg2 hLeast hTF hj
    rw [hj, Finset.card_empty]
    omega
  · exact @hHasJunk n G _ mate C hn3 hC4 hIndL hIndR hInv hMate hDeg2 hLeast hTF (Finset.nonempty_iff_ne_empty.mpr hj)
