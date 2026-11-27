import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8307_5
    (hHasDisjoint :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        (2 : ℕ) ≤ G.edgeFinset.card →
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        (∃ j ∈ PEqualNP.TopForm.junk G C,
          have C' : PEqualNP.CircuitLowerBounds.Circuit :=
            { gates := PEqualNP.NotPremium.replaceByConst C.gates j Bool.false, output := C.output };
          ∃ (a b c d : Fin n),
            a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
            G.Adj a b ∧ G.Adj c d ∧
            PEqualNP.MetaComplexity.circuitFun n C' (PEqualNP.EdgeOwnership.pairInput a b) = Bool.false ∧
            PEqualNP.MetaComplexity.circuitFun n C' (PEqualNP.EdgeOwnership.pairInput c d) = Bool.false) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 D ∧
          PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
          D.size ≤ C.size ∧
          (PEqualNP.TopForm.junk G D).card < (PEqualNP.TopForm.junk G C).card)
    (hAllShared :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        (2 : ℕ) ≤ G.edgeFinset.card →
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        (PEqualNP.TopForm.junk G C).Nonempty →
        (∀ j ∈ PEqualNP.TopForm.junk G C,
          have C' : PEqualNP.CircuitLowerBounds.Circuit :=
            { gates := PEqualNP.NotPremium.replaceByConst C.gates j Bool.false, output := C.output };
          ∃ (u v w : Fin n),
            v ≠ w ∧ G.Adj u v ∧ G.Adj u w ∧
            PEqualNP.MetaComplexity.circuitFun n C' (PEqualNP.EdgeOwnership.pairInput u v) = Bool.false ∧
            PEqualNP.MetaComplexity.circuitFun n C' (PEqualNP.EdgeOwnership.pairInput u w) = Bool.false) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 D ∧
          PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
          D.size ≤ C.size ∧
          (PEqualNP.TopForm.junk G D).card < (PEqualNP.TopForm.junk G C).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (PEqualNP.TopForm.junk x2 x4).Nonempty → (∀ x9 ∈ PEqualNP.TopForm.junk x2 x4, ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ PEqualNP.EdgeOwnership.pairInput x11 x12 ≠ PEqualNP.EdgeOwnership.pairInput x13 x14 ∧ PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x4.gates x9 Bool.false, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit } (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.false ∧ PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x4.gates x9 Bool.false, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit } (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.false) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x4.size ∧ (PEqualNP.TopForm.junk x2 x10).card < (PEqualNP.TopForm.junk x2 x4).card := by
  classical
  intro n G _ C hC4 hMono hFun hJunk hEss
  have hPairSym : ∀ a b : Fin n,
      PEqualNP.EdgeOwnership.pairInput a b = PEqualNP.EdgeOwnership.pairInput b a := by
    intro a b
    funext k
    change decide (k = a ∨ k = b) = decide (k = b ∨ k = a)
    by_cases ha : k = a <;> by_cases hb : k = b <;> simp [ha, hb]
  have hE2 : (2 : ℕ) ≤ G.edgeFinset.card := by
    have hj0 := hJunk.choose_spec
    obtain ⟨a, b, c, d, hab, hcd, hne, _, _⟩ := hEss hJunk.choose hj0
    have hse : s(a, b) ≠ s(c, d) := by
      intro hs
      rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne rfl
      · exact hne (hPairSym a b)
    have hsub : ({s(a, b), s(c, d)} : Finset (Sym2 (Fin n))) ⊆ G.edgeFinset := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he2
      · exact SimpleGraph.mem_edgeFinset.mpr hab
      · rw [Finset.mem_singleton.mp he2]
        exact SimpleGraph.mem_edgeFinset.mpr hcd
    have hle := Finset.card_le_card hsub
    rw [Finset.card_pair hse] at hle
    exact hle
  by_cases hDisj : ∃ j ∈ PEqualNP.TopForm.junk G C,
      ∃ (a b c d : Fin n),
        a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
        G.Adj a b ∧ G.Adj c d ∧
        PEqualNP.MetaComplexity.circuitFun n
          { gates := PEqualNP.NotPremium.replaceByConst C.gates j Bool.false, output := C.output }
          (PEqualNP.EdgeOwnership.pairInput a b) = Bool.false ∧
        PEqualNP.MetaComplexity.circuitFun n
          { gates := PEqualNP.NotPremium.replaceByConst C.gates j Bool.false, output := C.output }
          (PEqualNP.EdgeOwnership.pairInput c d) = Bool.false
  · exact hHasDisjoint n G C hC4 hE2 hMono hFun hDisj
  · refine hAllShared n G C hC4 hE2 hMono hFun hJunk ?_
    intro j hj
    dsimp only
    obtain ⟨a, b, c, d, hab, hcd, hne, hfab, hfcd⟩ := hEss j hj
    by_cases hac : a = c
    · refine ⟨a, b, d, ?_, hab, hac ▸ hcd, hfab, hac ▸ hfcd⟩
      intro hbd
      exact hne (by rw [hac, hbd])
    · by_cases had : a = d
      · refine ⟨a, b, c, ?_, hab, had ▸ hcd.symm, hfab, ?_⟩
        · intro hbc
          exact hne (by rw [had, hbc, hPairSym])
        · rw [had, hPairSym d c]; exact hfcd
      · by_cases hbc : b = c
        · refine ⟨b, a, d, ?_, hab.symm, hbc ▸ hcd, ?_, hbc ▸ hfcd⟩
          · intro had'
            exact hne (by rw [hbc, had', hPairSym])
          · rw [hPairSym b a]; exact hfab
        · by_cases hbd : b = d
          · refine ⟨b, a, c, ?_, hab.symm, hbd ▸ hcd.symm, ?_, ?_⟩
            · intro hac'
              exact hne (by rw [hbd, hac'])
            · rw [hPairSym b a]; exact hfab
            · rw [hbd, hPairSym d c]; exact hfcd
          · exact False.elim (hDisj ⟨j, hj, a, b, c, d, hac, had, hbc, hbd, hab, hcd, hfab, hfcd⟩)
