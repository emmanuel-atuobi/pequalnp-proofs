import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18802_4
    (hUstarStar :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        have U : Finset (Sym2 (Fin n)) := PEqualNP.TopForm.Ustar G C;
        have B : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card;
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (2 : ℕ) ≤ U.card →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
        B < (2 : ℕ) * U.card →
        (∃ v : Fin n, ∀ e ∈ U, v ∈ e) →
        (1 : ℕ) + U.card ≤ B)
    (hUstarNonStar :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        have U : Finset (Sym2 (Fin n)) := PEqualNP.TopForm.Ustar G C;
        have B : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card;
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (2 : ℕ) ≤ U.card →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
        B < (2 : ℕ) * U.card →
        (¬∃ v : Fin n, ∀ e ∈ U, v ∈ e) →
        ∃ V : Finset (Fin n),
          (∀ a b : Fin n, G.Adj a b → s(a, b) ∈ U → a ∈ V ∨ b ∈ V) ∧
          V.card + U.card ≤ B) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (PEqualNP.TopForm.Ustar x2 x4).Nonempty → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → ∃ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → s(x12, x13) ∈ PEqualNP.TopForm.Ustar x2 x4 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  classical
  intro n G _ C hC4 hNE hLeast hTop hU hJ
  by_cases hSmall : (2 : ℕ) * (PEqualNP.TopForm.Ustar G C).card ≤
      (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
      (PEqualNP.TopForm.junk G C).card +
      (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
  · have hex : ∀ e : Sym2 (Fin n), ∃ v : Fin n, v ∈ e := by
      intro e
      exact Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left a b⟩) e
    let pick : Sym2 (Fin n) → Fin n := fun e => Classical.choose (hex e)
    let V : Finset (Fin n) := (PEqualNP.TopForm.Ustar G C).image pick
    refine ⟨V, ?_, ?_⟩
    · intro a b _ hab
      have hm : pick s(a, b) ∈ s(a, b) := Classical.choose_spec (hex s(a, b))
      have hpin : pick s(a, b) ∈ V := Finset.mem_image_of_mem pick hab
      rcases Sym2.mem_iff.mp hm with hEq | hEq
      · exact Or.inl (hEq ▸ hpin)
      · exact Or.inr (hEq ▸ hpin)
    · have hVle : V.card ≤ (PEqualNP.TopForm.Ustar G C).card := Finset.card_image_le
      omega
  · have hBlt : (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card <
        (2 : ℕ) * (PEqualNP.TopForm.Ustar G C).card := by omega
    have hU2 : (2 : ℕ) ≤ (PEqualNP.TopForm.Ustar G C).card := by omega
    by_cases hStar : ∃ v : Fin n, ∀ e ∈ PEqualNP.TopForm.Ustar G C, v ∈ e
    · have h1 := hUstarStar n G C hC4 hNE hLeast hTop hU2 hJ hBlt hStar
      obtain ⟨v, hv⟩ := hStar
      refine ⟨{v}, ?_, ?_⟩
      · intro a b _ hab
        rcases Sym2.mem_iff.mp (hv s(a, b) hab) with rfl | rfl
        · exact Or.inl (Finset.mem_singleton_self v)
        · exact Or.inr (Finset.mem_singleton_self v)
      · rw [Finset.card_singleton]
        exact h1
    · exact hUstarNonStar n G C hC4 hNE hLeast hTop hU2 hJ hBlt hStar
