import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8181_2
    (hStrictReader :
      ∀ (m n : ℕ) (E M : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (G : SimpleGraph (Fin (m + n))),
        have rep : Finset (Fin m × Fin n) → PEqualNP.CircuitLowerBounds.Circuit → Prop :=
          fun E0 C0 => PEqualNP.TopForm.IsAO2 (m + n) C0 ∧
            ∀ z : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C0 z =
              Decidable.decide (∃ (a : Fin m) (b : Fin n), (a, b) ∈ E0 ∧
                z (Fin.castAdd n a) = Bool.true ∧ z (Fin.natAdd m b) = Bool.true);
        (∀ u v : Fin (m + n), G.Adj u v ↔
          ∃ e ∈ E, u = Fin.castAdd n e.1 ∧ v = Fin.natAdd m e.2 ∨
            v = Fin.castAdd n e.1 ∧ u = Fin.natAdd m e.2) →
        ¬G.IsAcyclic →
        rep E C →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1.1 = e2.1 → e1 = e2) →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1.2 = e2.2 → e1 = e2) →
        M ⊆ E →
        (E \ M).Nonempty →
        (∀ e ∈ E \ M, (2 : ℕ) ≤ (G.neighborSet (Fin.castAdd n e.1)).ncard ∧
          (2 : ℕ) ≤ (G.neighborSet (Fin.natAdd m e.2)).ncard) →
        (∀ (a a' : Fin m) (b b' : Fin n), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        (∃ v : Fin (m + n),
          (2 : ℕ) ≤ (G.neighborSet v).ncard ∧
          (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card < (G.neighborSet v).ncard) →
        ∃ e ∈ E, e ∉ M ∧ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size < C.size ∧ rep (E.erase e) D)
    (hExactReaders :
      ∀ (m n : ℕ) (E M : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (G : SimpleGraph (Fin (m + n))),
        have rep : Finset (Fin m × Fin n) → PEqualNP.CircuitLowerBounds.Circuit → Prop :=
          fun E0 C0 => PEqualNP.TopForm.IsAO2 (m + n) C0 ∧
            ∀ z : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C0 z =
              Decidable.decide (∃ (a : Fin m) (b : Fin n), (a, b) ∈ E0 ∧
                z (Fin.castAdd n a) = Bool.true ∧ z (Fin.natAdd m b) = Bool.true);
        (∀ u v : Fin (m + n), G.Adj u v ↔
          ∃ e ∈ E, u = Fin.castAdd n e.1 ∧ v = Fin.natAdd m e.2 ∨
            v = Fin.castAdd n e.1 ∧ u = Fin.natAdd m e.2) →
        ¬G.IsAcyclic →
        rep E C →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1.1 = e2.1 → e1 = e2) →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1.2 = e2.2 → e1 = e2) →
        M ⊆ E →
        (E \ M).Nonempty →
        (∀ e ∈ E \ M, (2 : ℕ) ≤ (G.neighborSet (Fin.castAdd n e.1)).ncard ∧
          (2 : ℕ) ≤ (G.neighborSet (Fin.natAdd m e.2)).ncard) →
        (∀ (a a' : Fin m) (b b' : Fin n), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        (∀ v : Fin (m + n),
          have d : ℕ := (G.neighborSet v).ncard;
          have R : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) C ↑v;
          (2 : ℕ) ≤ d →
          R.card = d ∧
          ∀ g ∈ R,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.TopForm.readers (m + n) C g ⊆ R) →
        ∃ e ∈ E, e ∉ M ∧ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size < C.size ∧ rep (E.erase e) D) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),   have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 → x12 = x14) → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.2 = x15.2 → x13 = x15) → x4 ⊆ x3 → (∀ (x15 x16 : Fin x1) (x17 x18 : Fin x2), x15 ≠ x16 → x17 ≠ x18 → ¬((x15, x17) ∈ x3 ∧ (x15, x18) ∈ x3 ∧ (x16, x17) ∈ x3 ∧ (x16, x18) ∈ x3)) → (∀ x16 ∈ x3, ((∀ x18 ∈ x3, x18.1 = x16.1 → x18 = x16) ∨ ∀ x18 ∈ x3, x18.2 = x16.2 → x18 = x16) → (x3.erase x16).Nonempty → x16 ∈ x4) → ¬x8 → ∃ x18 ∈ x3, x18 ∉ x4 ∧ ∃ (x19 : PEqualNP.CircuitLowerBounds.Circuit), x19.size < x5.size ∧ x7 (x3.erase x18) x19 := by
  classical
  intro m n E M C G rep bad hAdj hCyc hRep hMatchL hMatchR hSub hC4 hDeg1 hNotBad
  have hSepLR : ∀ (a : Fin m) (b : Fin n), Fin.castAdd n a ≠ Fin.natAdd m b := by
    intro a b h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hCastInj : Function.Injective (Fin.castAdd n : Fin m → Fin (m + n)) := by
    intro a1 a2 h
    exact Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val h)
  have hNatInj : Function.Injective (Fin.natAdd m : Fin n → Fin (m + n)) := by
    intro b1 b2 h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    exact Fin.ext (by omega)
  have hSdiffNe : (E \ M).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
    have hEM : E = M := Finset.Subset.antisymm hemp hSub
    apply hCyc
    intro v p hp
    have hge : 3 ≤ p.length := hp.three_le_length
    cases p with
    | nil => simp at hge
    | cons h1 p1 =>
      rename_i u1
      cases p1 with
      | nil => simp at hge
      | cons h2 p2 =>
        rename_i u2
        have hne : v ≠ u2 := by
          have hndE := hp.edges_nodup
          simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons, List.mem_cons] at hndE
          intro hvu
          subst hvu
          exact hndE.1 (Or.inl Sym2.eq_swap)
        have hadj1 : G.Adj u1 v := h1.symm
        have hadj2 : G.Adj u1 u2 := h2
        rw [hAdj] at hadj1 hadj2
        obtain ⟨e1, he1, hor1⟩ := hadj1
        obtain ⟨e2, he2, hor2⟩ := hadj2
        rw [hEM] at he1 he2
        rcases hor1 with ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩ <;> rcases hor2 with ⟨hu2, hv2⟩ | ⟨hv2, hu2⟩
        · have hee : e1 = e2 := hMatchL e1 he1 e2 he2 (hCastInj (hu1.symm.trans hu2))
          exact hne (hv1.trans (by rw [hee, hv2]))
        · exact hSepLR e1.1 e2.2 (hu1.symm.trans hu2)
        · exact hSepLR e2.1 e1.2 (hu2.symm.trans hu1)
        · have hee : e1 = e2 := hMatchR e1 he1 e2 he2 (hNatInj (hu1.symm.trans hu2))
          exact hne (hv1.trans (by rw [hee, hv2]))
  have hE3 : (3 : ℕ) ≤ E.card := by
    obtain ⟨v, p, hp⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp hCyc
    let edge : Fin m × Fin n → Sym2 (Fin (m + n)) :=
      fun e => s(Fin.castAdd n e.1, Fin.natAdd m e.2)
    have hsubG : G.edgeFinset ⊆ E.image edge := by
      intro z hz
      rw [SimpleGraph.mem_edgeFinset] at hz
      refine Sym2.ind (fun i j hij => ?_) z hz
      obtain ⟨e, he, hor⟩ := (hAdj i j).mp hij
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Finset.mem_image_of_mem edge he
      · rw [Sym2.eq_swap]
        exact Finset.mem_image_of_mem edge he
    have h3l : 3 ≤ p.length := hp.three_le_length
    have hle1 : p.length ≤ G.edgeSet.ncard := hp.isTrail.length_le_ncard_edgeSet
    have hle2 : G.edgeSet.ncard = G.edgeFinset.card := by
      simpa only [SimpleGraph.edgeFinset] using Set.ncard_eq_toFinset_card' G.edgeSet
    have hle3 : G.edgeFinset.card ≤ (E.image edge).card := Finset.card_le_card hsubG
    have hle4 : (E.image edge).card ≤ E.card := Finset.card_image_le
    omega
  have hDegGe2 : ∀ e ∈ E \ M, (2 : ℕ) ≤ (G.neighborSet (Fin.castAdd n e.1)).ncard ∧
      (2 : ℕ) ≤ (G.neighborSet (Fin.natAdd m e.2)).ncard := by
    intro e he
    have heE : e ∈ E := (Finset.mem_sdiff.mp he).1
    have heM : e ∉ M := (Finset.mem_sdiff.mp he).2
    have herase : (E.erase e).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem heE]
      omega
    have hnotL : ¬∀ e' ∈ E, e'.1 = e.1 → e' = e := fun h => heM (hDeg1 e heE (Or.inl h) herase)
    have hnotR : ¬∀ e' ∈ E, e'.2 = e.2 → e' = e := fun h => heM (hDeg1 e heE (Or.inr h) herase)
    push Not at hnotL hnotR
    obtain ⟨eL, heLE, heL1, heLne⟩ := hnotL
    obtain ⟨eR, heRE, heR2, heRne⟩ := hnotR
    constructor
    · have hne2 : Fin.natAdd m e.2 ≠ Fin.natAdd m eL.2 := by
        intro h
        exact heLne (Prod.ext heL1 (hNatInj h).symm)
      have hsub2 : ({Fin.natAdd m e.2, Fin.natAdd m eL.2} : Set (Fin (m + n))) ⊆
          G.neighborSet (Fin.castAdd n e.1) := by
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rw [SimpleGraph.mem_neighborSet, hAdj]
        rcases hw with rfl | rfl
        · exact ⟨e, heE, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨eL, heLE, Or.inl ⟨congrArg (Fin.castAdd n) heL1.symm, rfl⟩⟩
      have hle := Set.ncard_le_ncard hsub2 (Set.toFinite _)
      rw [Set.ncard_pair hne2] at hle
      exact hle
    · have hne2 : Fin.castAdd n e.1 ≠ Fin.castAdd n eR.1 := by
        intro h
        exact heRne (Prod.ext (hCastInj h).symm heR2)
      have hsub2 : ({Fin.castAdd n e.1, Fin.castAdd n eR.1} : Set (Fin (m + n))) ⊆
          G.neighborSet (Fin.natAdd m e.2) := by
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rw [SimpleGraph.mem_neighborSet, hAdj]
        rcases hw with rfl | rfl
        · exact ⟨e, heE, Or.inr ⟨rfl, rfl⟩⟩
        · exact ⟨eR, heRE, Or.inr ⟨rfl, congrArg (Fin.natAdd m) heR2.symm⟩⟩
      have hle := Set.ncard_le_ncard hsub2 (Set.toFinite _)
      rw [Set.ncard_pair hne2] at hle
      exact hle
  by_cases hStrict : ∃ v : Fin (m + n),
      (2 : ℕ) ≤ (G.neighborSet v).ncard ∧
      (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card < (G.neighborSet v).ncard
  · exact hStrictReader m n E M C G hAdj hCyc hRep hMatchL hMatchR hSub hSdiffNe hDegGe2 hC4 hStrict
  · refine hExactReaders m n E M C G hAdj hCyc hRep hMatchL hMatchR hSub hSdiffNe hDegGe2 hC4 ?_
    intro v d R hdv
    have hnotlt : ¬ R.card < d :=
      fun h => hStrict ⟨v, hdv, h⟩
    have hnotgt : ¬ d < R.card :=
      fun h => hNotBad ⟨v, hdv, Or.inl h⟩
    have heq : R.card = d := by omega
    refine ⟨heq, ?_⟩
    intro g hg hop
    by_contra hnsub
    exact hNotBad ⟨v, hdv, Or.inr ⟨heq.symm, g, hg, hop, hnsub⟩⟩
