import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18593_4
    (hDisjoint :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        have J : Finset ℕ := PEqualNP.TopForm.junk G C;
        have O : ℕ := (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card;
        have K : ℕ := (PEqualNP.TopForm.centreless G C).card;
        have U : Finset (Sym2 (Fin n)) := PEqualNP.TopForm.Ustar G C;
        G.IsBipartite → ¬G.IsAcyclic → PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        (∀ V : Finset (Fin n), G.IsVertexCover ↑V → C.size + (1 : ℕ) < G.edgeFinset.card + V.card) →
        (2 : ℕ) ≤ J.card → (1 : ℕ) ≤ O → (3 : ℕ) ≤ K + O →
        (5 : ℕ) ≤ (2 : ℕ) * K + J.card + O → (3 : ℕ) ≤ U.card →
        (2 : ℕ) * K + J.card + O < (2 : ℕ) * U.card →
        (∀ V : Finset (Fin n), (∀ e ∈ U, ∃ v ∈ V, v ∈ e) →
          (2 : ℕ) * K + J.card + O < V.card + U.card) →
        (∃ j ∈ J, ∃ (a b c d : Fin n),
          a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
          s(a, b) ∈ U ∧ s(c, d) ∈ U ∧
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput a b) = Bool.true ∧
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput c d) = Bool.true) →
        False)
    (hShared :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        have J : Finset ℕ := PEqualNP.TopForm.junk G C;
        have O : ℕ := (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card;
        have K : ℕ := (PEqualNP.TopForm.centreless G C).card;
        have U : Finset (Sym2 (Fin n)) := PEqualNP.TopForm.Ustar G C;
        G.IsBipartite → ¬G.IsAcyclic → PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        (∀ V : Finset (Fin n), G.IsVertexCover ↑V → C.size + (1 : ℕ) < G.edgeFinset.card + V.card) →
        (2 : ℕ) ≤ J.card → (1 : ℕ) ≤ O → (3 : ℕ) ≤ K + O →
        (5 : ℕ) ≤ (2 : ℕ) * K + J.card + O → (3 : ℕ) ≤ U.card →
        (2 : ℕ) * K + J.card + O < (2 : ℕ) * U.card →
        (∀ V : Finset (Fin n), (∀ e ∈ U, ∃ v ∈ V, v ∈ e) →
          (2 : ℕ) * K + J.card + O < V.card + U.card) →
        (∃ j ∈ J, ∃ (u v w : Fin n),
          v ≠ w ∧
          s(u, v) ∈ U ∧ s(u, w) ∈ U ∧
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = Bool.true ∧
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u w) = Bool.true) →
        False) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∀ (x10 : Finset (Fin x1)), x2.IsVertexCover ↑x10 → x4.size + (1 : ℕ) < x2.edgeFinset.card + x10.card) → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (1 : ℕ) ≤ (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (3 : ℕ) ≤ (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (5 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x2 x4).card → (∀ (x16 : Finset (Fin x1)), (∀ x17 ∈ PEqualNP.TopForm.Ustar x2 x4, ∃ x19 ∈ x16, x19 ∈ x17) → (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card < x16.card + (PEqualNP.TopForm.Ustar x2 x4).card) → (∃ x17 ∈ PEqualNP.TopForm.junk x2 x4, ∃ (x18 : Fin x1) (x19 : Fin x1) (x20 : Fin x1) (x21 : Fin x1), s(x18, x19) ∈ PEqualNP.TopForm.Ustar x2 x4 ∧ s(x20, x21) ∈ PEqualNP.TopForm.Ustar x2 x4 ∧ s(x18, x19) ≠ s(x20, x21) ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x18 x19) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true) → False := by
  classical
  intro n G _ C hBip hCyc hC4 hLeast hTop hVC hJ hO hKO hSum hU hUcov hWit
  have hPairSym : ∀ a b : Fin n,
      PEqualNP.EdgeOwnership.pairInput a b = PEqualNP.EdgeOwnership.pairInput b a := by
    intro a b
    funext k
    change decide (k = a ∨ k = b) = decide (k = b ∨ k = a)
    by_cases ha : k = a <;> by_cases hb : k = b <;> simp [ha, hb]
  have hUbd : (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
      (PEqualNP.TopForm.junk G C).card +
      (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card <
      (2 : ℕ) * (PEqualNP.TopForm.Ustar G C).card := by
    have hex : ∀ e : Sym2 (Fin n), ∃ v : Fin n, v ∈ e := by
      intro e
      exact Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left a b⟩) e
    let pick : Sym2 (Fin n) → Fin n := fun e => Classical.choose (hex e)
    let V : Finset (Fin n) := (PEqualNP.TopForm.Ustar G C).image pick
    have hVcov : ∀ e ∈ PEqualNP.TopForm.Ustar G C, ∃ v ∈ V, v ∈ e := by
      intro e he
      exact ⟨pick e, Finset.mem_image_of_mem pick he, Classical.choose_spec (hex e)⟩
    have hVcard : V.card ≤ (PEqualNP.TopForm.Ustar G C).card := Finset.card_image_le
    have h1 := hUcov V hVcov
    omega
  obtain ⟨j, hj, a, b, c, d, habU, hcdU, hne, hgab, hgcd⟩ := hWit
  by_cases hac : a = c
  · apply hShared n G C hBip hCyc hC4 hLeast hTop hVC hJ hO hKO hSum hU hUbd hUcov
    refine ⟨j, hj, a, b, d, ?_, habU, hac ▸ hcdU, hgab, hac ▸ hgcd⟩
    intro hbd
    exact hne (by rw [hac, hbd])
  · by_cases had : a = d
    · apply hShared n G C hBip hCyc hC4 hLeast hTop hVC hJ hO hKO hSum hU hUbd hUcov
      refine ⟨j, hj, a, b, c, ?_, habU, ?_, hgab, ?_⟩
      · intro hbc
        exact hne (by rw [had, hbc, Sym2.eq_swap])
      · rw [had, Sym2.eq_swap]; exact hcdU
      · rw [had, hPairSym d c]; exact hgcd
    · by_cases hbc : b = c
      · apply hShared n G C hBip hCyc hC4 hLeast hTop hVC hJ hO hKO hSum hU hUbd hUcov
        refine ⟨j, hj, b, a, d, ?_, ?_, hbc ▸ hcdU, ?_, hbc ▸ hgcd⟩
        · intro had'
          exact hne (by rw [hbc, had', Sym2.eq_swap])
        · rw [Sym2.eq_swap]; exact habU
        · rw [hPairSym b a]; exact hgab
      · by_cases hbd : b = d
        · apply hShared n G C hBip hCyc hC4 hLeast hTop hVC hJ hO hKO hSum hU hUbd hUcov
          refine ⟨j, hj, b, a, c, ?_, ?_, ?_, ?_, ?_⟩
          · intro hac'
            exact hne (by rw [hbd, hac'])
          · rw [Sym2.eq_swap]; exact habU
          · rw [hbd, Sym2.eq_swap]; exact hcdU
          · rw [hPairSym b a]; exact hgab
          · rw [hbd, hPairSym d c]; exact hgcd
        · exact hDisjoint n G C hBip hCyc hC4 hLeast hTop hVC hJ hO hKO hSum hU hUbd hUcov
            ⟨j, hj, a, b, c, d, hac, had, hbc, hbd, habU, hcdU, hgab, hgcd⟩
