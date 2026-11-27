import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17625_4
    (hDisjointEdges :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.IsBipartite →
        ¬G.IsAcyclic →
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (∃ j < C.size,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ¬PEqualNP.TopForm.BelowF G C j ∧
          ∃ (e1 e2 : Fin n × Fin n),
            e1.1 ≠ e2.1 ∧ e1.1 ≠ e2.2 ∧ e1.2 ≠ e2.1 ∧ e1.2 ≠ e2.2 ∧
            ∀ e ∈ [e1, e2],
              G.Adj e.1 e.2 ∧
              PEqualNP.ReadK.readsAtMost C n [↑e.1, ↑e.2] (1 : ℕ) = Bool.false ∧
              PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput e.1 e.2) = Bool.true) →
        ∃ V : Finset (Fin n),
          (∀ u v : Fin n, G.Adj u v → u ∈ V ∨ v ∈ V) ∧
          G.edgeFinset.card + V.card ≤ C.size + (1 : ℕ))
    (hSharedVertex :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.IsBipartite →
        ¬G.IsAcyclic →
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (∃ j < C.size,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ¬PEqualNP.TopForm.BelowF G C j ∧
          ∃ (e1 e2 : Fin n × Fin n),
            s(e1.1, e1.2) ≠ s(e2.1, e2.2) ∧
            (e1.1 = e2.1 ∨ e1.1 = e2.2 ∨ e1.2 = e2.1 ∨ e1.2 = e2.2) ∧
            ∀ e ∈ [e1, e2],
              G.Adj e.1 e.2 ∧
              PEqualNP.ReadK.readsAtMost C n [↑e.1, ↑e.2] (1 : ℕ) = Bool.false ∧
              PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput e.1 e.2) = Bool.true) →
        ∃ V : Finset (Fin n),
          (∀ u v : Fin n, G.Adj u v → u ∈ V ∨ v ∈ V) ∧
          G.edgeFinset.card + V.card ≤ C.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x2.IsBipartite →     ¬x2.IsAcyclic →       PEqualNP.TopForm.NoFourCycle x2 →         PEqualNP.TopForm.IsLeastAO x2 x4 →           PEqualNP.TopForm.TopForm x2 x4 →             (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1 × Fin x1) (x12 : Fin x1 × Fin x1), s(x11.1, x11.2) ≠ s(x12.1, x12.2) ∧ ∀ x13 ∈ [x11, x12], x2.Adj x13.1 x13.2 ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13.1, ↑x13.2] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13.1 x13.2) = Bool.true) →               ∀ (x11 : Finset (Fin x1)) (x12 : ↥x11 → Fin x1),                 Function.Injective x12 →                   (∀ (x14 : ↥x11), x12 x14 ∉ x11 ∧ x2.Adj (↑x14) (x12 x14)) →                     have x15 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates;                     have x16 : Finset ℕ := {x16 ∈ x15.toFinset | x16 < x1};                     x2.edgeFinset.card + x11.card - x16.card ≤ x15.length - x15.toFinset.card := by
  classical
  intro n G _ C hBip hCyc hC4 hLeast hTop hWit M mate hInj hEdges
  obtain ⟨j, hj, hAnd, hDirty, e1, e2, hne, hall⟩ := hWit
  have hCover : ∃ V : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → u ∈ V ∨ v ∈ V) ∧ G.edgeFinset.card + V.card ≤ C.size + (1 : ℕ) := by
    by_cases hShare : e1.1 = e2.1 ∨ e1.1 = e2.2 ∨ e1.2 = e2.1 ∨ e1.2 = e2.2
    · exact hSharedVertex n G C hBip hCyc hC4 hLeast hTop ⟨j, hj, hAnd, hDirty, e1, e2, hne, hShare, hall⟩
    · have h11 : e1.1 ≠ e2.1 := fun h => hShare (Or.inl h)
      have h12 : e1.1 ≠ e2.2 := fun h => hShare (Or.inr (Or.inl h))
      have h21 : e1.2 ≠ e2.1 := fun h => hShare (Or.inr (Or.inr (Or.inl h)))
      have h22 : e1.2 ≠ e2.2 := fun h => hShare (Or.inr (Or.inr (Or.inr h)))
      exact hDisjointEdges n G C hBip hCyc hC4 hLeast hTop
        ⟨j, hj, hAnd, hDirty, e1, e2, h11, h12, h21, h22, hall⟩
  obtain ⟨V, hVcov, hVbd⟩ := hCover
  let pick : ↥M → Fin n := fun a => if (a : Fin n) ∈ V then a else mate a
  have hPickMem : ∀ a : ↥M, pick a ∈ V := by
    intro a
    dsimp only [pick]
    split_ifs with ha
    · exact ha
    · exact (hVcov a (mate a) (hEdges a).2).resolve_left ha
  have hPickInj : Function.Injective pick := by
    intro a b hab
    dsimp only [pick] at hab
    split_ifs at hab with ha hb hb
    · exact Subtype.ext hab
    · exact False.elim ((hEdges b).1 (hab ▸ a.2))
    · exact False.elim ((hEdges a).1 (hab.symm ▸ b.2))
    · exact hInj hab
  have hMV : M.card ≤ V.card := by
    have h1 := Fintype.card_le_of_injective
      (fun a : ↥M => (⟨pick a, hPickMem a⟩ : ↥V))
      (fun a b hab => hPickInj (congrArg Subtype.val hab))
    simpa only [Fintype.card_coe] using h1
  let refs : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates
  let inRefs : Finset ℕ := {w ∈ refs.toFinset | w < n}
  let gateRefs : Finset ℕ := {w ∈ refs.toFinset | ¬w < n}
  have hFlatLen : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      (∀ g ∈ gs, g.inputs.length = 2) →
      (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs gs).length = 2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; rfl
    | cons g gs ih =>
      intro hg
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 : g.inputs.length = 2 := hg g List.mem_cons_self
      have h2 := ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      omega
  have hrefs_len : refs.length = 2 * C.size := hFlatLen C.gates hLeast.1.2.2
  have hPart : inRefs.card + gateRefs.card = refs.toFinset.card := by
    have hd : Disjoint inRefs gateRefs := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      exact (Finset.mem_filter.mp hw2).2 (Finset.mem_filter.mp hw1).2
    have hu : inRefs ∪ gateRefs = refs.toFinset := by
      ext w
      simp only [inRefs, gateRefs, Finset.mem_union, Finset.mem_filter]
      by_cases h : w < n <;> tauto
    rw [← Finset.card_union_of_disjoint hd, hu]
  have hGateSub : gateRefs ⊆ Finset.Ico n (n + (C.size - 1)) := by
    intro w hw
    have hwm : w ∈ refs.toFinset := (Finset.mem_filter.mp hw).1
    have hwge : ¬w < n := (Finset.mem_filter.mp hw).2
    rw [List.mem_toFinset, List.mem_flatMap] at hwm
    obtain ⟨g, hg, hwg⟩ := hwm
    obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hg
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C idx = C.gates[idx]'hidx :=
      List.getD_eq_getElem C.gates ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ hidx
    have hlt : w < n + idx := hLeast.1.2.1 idx hidx w (by rw [hga]; exact hwg)
    have hidx' : idx < C.size := hidx
    rw [Finset.mem_Ico]
    omega
  have hGateCard : gateRefs.card ≤ C.size - 1 := by
    have h1 := Finset.card_le_card hGateSub
    rw [Nat.card_Ico] at h1
    omega
  have hPos : 0 < C.size := Nat.zero_lt_of_lt hj
  change G.edgeFinset.card + M.card - inRefs.card ≤ refs.length - refs.toFinset.card
  omega
