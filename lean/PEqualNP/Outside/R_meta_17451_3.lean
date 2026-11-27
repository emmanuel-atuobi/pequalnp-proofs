import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17451_3
    (hStrictReader :
      ∀ (m n : ℕ) (E M : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (G : SimpleGraph (Fin (m + n))),
        have rep : Finset (Fin m × Fin n) → PEqualNP.CircuitLowerBounds.Circuit → Prop :=
          fun E0 C0 => PEqualNP.TopForm.IsAO2 (m + n) C0 ∧
            ∀ z : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C0 z =
              Decidable.decide (∃ (a : Fin m) (b : Fin n), (a, b) ∈ E0 ∧
                z (Fin.castAdd n a) = Bool.true ∧ z (Fin.natAdd m b) = Bool.true);
        have deg : Fin (m + n) → ℕ := fun v => (G.neighborSet v).ncard;
        (∀ u v : Fin (m + n), G.Adj u v ↔
          ∃ e ∈ E, u = Fin.castAdd n e.1 ∧ v = Fin.natAdd m e.2 ∨
            v = Fin.castAdd n e.1 ∧ u = Fin.natAdd m e.2) →
        ¬G.IsAcyclic →
        rep E C →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1.1 = e2.1 ∨ e1.2 = e2.2 → e1 = e2) →
        M ⊆ E →
        (E \ M).Nonempty →
        (∀ (a a' : Fin m) (b b' : Fin n), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        (∀ e ∈ E \ M,
          (2 : ℕ) ≤ deg (Fin.castAdd n e.1) ∧ (2 : ℕ) ≤ deg (Fin.natAdd m e.2) ∧
          (∃ e' ∈ M, e'.1 = e.1 ∨ e'.2 = e.2) ∧
          ∀ V : Finset (Fin (m + n)),
            (∀ e' ∈ E.erase e, Fin.castAdd n e'.1 ∈ V ∨ Fin.natAdd m e'.2 ∈ V) →
            C.size ≤ (E.erase e).card + V.card - (1 : ℕ)) →
        (∃ v : Fin (m + n),
          (2 : ℕ) ≤ deg v ∧ (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card < deg v) →
        ∃ e ∈ E, e ∉ M ∧ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size < C.size ∧ rep (E.erase e) D)
    (hExactReaders :
      ∀ (m n : ℕ) (E M : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (G : SimpleGraph (Fin (m + n))),
        have rep : Finset (Fin m × Fin n) → PEqualNP.CircuitLowerBounds.Circuit → Prop :=
          fun E0 C0 => PEqualNP.TopForm.IsAO2 (m + n) C0 ∧
            ∀ z : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C0 z =
              Decidable.decide (∃ (a : Fin m) (b : Fin n), (a, b) ∈ E0 ∧
                z (Fin.castAdd n a) = Bool.true ∧ z (Fin.natAdd m b) = Bool.true);
        have deg : Fin (m + n) → ℕ := fun v => (G.neighborSet v).ncard;
        (∀ u v : Fin (m + n), G.Adj u v ↔
          ∃ e ∈ E, u = Fin.castAdd n e.1 ∧ v = Fin.natAdd m e.2 ∨
            v = Fin.castAdd n e.1 ∧ u = Fin.natAdd m e.2) →
        ¬G.IsAcyclic →
        rep E C →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1.1 = e2.1 ∨ e1.2 = e2.2 → e1 = e2) →
        M ⊆ E →
        (E \ M).Nonempty →
        (∀ (a a' : Fin m) (b b' : Fin n), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        (∀ e ∈ E \ M,
          (2 : ℕ) ≤ deg (Fin.castAdd n e.1) ∧ (2 : ℕ) ≤ deg (Fin.natAdd m e.2) ∧
          (∃ e' ∈ M, e'.1 = e.1 ∨ e'.2 = e.2) ∧
          ∀ V : Finset (Fin (m + n)),
            (∀ e' ∈ E.erase e, Fin.castAdd n e'.1 ∈ V ∨ Fin.natAdd m e'.2 ∈ V) →
            C.size ≤ (E.erase e).card + V.card - (1 : ℕ)) →
        (∀ v : Fin (m + n),
          have R : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) C ↑v;
          (2 : ℕ) ≤ deg v →
          R.card = deg v ∧
          ∀ g ∈ R,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.TopForm.readers (m + n) C g ⊆ R) →
        ∃ e ∈ E, e ∉ M ∧ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size < C.size ∧ rep (E.erase e) D) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),   have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 ∨ x12.2 = x14.2 → x12 = x14) → x4 ⊆ x3 → (∀ (x14 x15 : Fin x1) (x16 x17 : Fin x2), x14 ≠ x15 → x16 ≠ x17 → ¬((x14, x16) ∈ x3 ∧ (x14, x17) ∈ x3 ∧ (x15, x16) ∈ x3 ∧ (x15, x17) ∈ x3)) → (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) → ¬x8 → (∀ x17 ∈ x3 \ x4, ∃ x19 ∈ x4, x19.1 = x17.1 ∨ x19.2 = x17.2) → (∀ x18 ∈ x3 \ x4, ∀ (x20 : Finset (Fin (x1 + x2))), (∀ x21 ∈ x3.erase x18, Fin.castAdd x2 x21.1 ∈ x20 ∨ Fin.natAdd x1 x21.2 ∈ x20) → x5.size ≤ (x3.erase x18).card + x20.card - (1 : ℕ)) → ∃ x19 ∈ x3, x19 ∉ x4 ∧ ∃ (x20 : PEqualNP.CircuitLowerBounds.Circuit), x20.size < x5.size ∧ x7 (x3.erase x19) x20 := by
  classical
  intro m n E M C G rep bad hAdj hCyc hRep hMatch hSub hC4 hDeg1 hNotBad hMax hBound
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
          have hnd : p2.support.Nodup → True := fun _ => trivial
          have hsup := hp.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.tail_cons, List.nodup_cons] at hsup
          rcases hp.edges_nodup with hndE
          simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons, List.mem_cons] at hndE
          intro hvu
          subst hvu
          exact hndE.1 (Or.inl (Sym2.eq_swap))
        have hadj1 : G.Adj u1 v := h1.symm
        have hadj2 : G.Adj u1 u2 := h2
        rw [hAdj] at hadj1 hadj2
        obtain ⟨e1, he1, hor1⟩ := hadj1
        obtain ⟨e2, he2, hor2⟩ := hadj2
        rw [hEM] at he1 he2
        rcases hor1 with ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩ <;> rcases hor2 with ⟨hu2, hv2⟩ | ⟨hv2, hu2⟩
        · have heq : e1.1 = e2.1 := hCastInj (hu1.symm.trans hu2)
          have hee : e1 = e2 := hMatch e1 he1 e2 he2 (Or.inl heq)
          exact hne (hv1.trans (by rw [hee, hv2]))
        · exact hSepLR e1.1 e2.2 (hu1.symm.trans hu2)
        · exact hSepLR e2.1 e1.2 (hu2.symm.trans hu1)
        · have heq : e1.2 = e2.2 := hNatInj (hu1.symm.trans hu2)
          have hee : e1 = e2 := hMatch e1 he1 e2 he2 (Or.inr heq)
          exact hne (hv1.trans (by rw [hee, hv2]))
  have hDegGe2 : ∀ e ∈ E \ M, (2 : ℕ) ≤ (G.neighborSet (Fin.castAdd n e.1)).ncard ∧
      (2 : ℕ) ≤ (G.neighborSet (Fin.natAdd m e.2)).ncard := by
    intro e he
    have heE : e ∈ E := (Finset.mem_sdiff.mp he).1
    have heM : e ∉ M := (Finset.mem_sdiff.mp he).2
    obtain ⟨m0, hm0M, _⟩ := hMax e he
    have hm0E : m0 ∈ E := hSub hm0M
    have hm0ne : m0 ≠ e := fun h => heM (h ▸ hm0M)
    have herase : (E.erase e).Nonempty := ⟨m0, Finset.mem_erase.mpr ⟨hm0ne, hm0E⟩⟩
    have hnotL : ¬∀ e' ∈ E, e'.1 = e.1 → e' = e := fun h => heM (hDeg1 e heE (Or.inl h) herase)
    have hnotR : ¬∀ e' ∈ E, e'.2 = e.2 → e' = e := fun h => heM (hDeg1 e heE (Or.inr h) herase)
    push Not at hnotL hnotR
    obtain ⟨eL, heLE, heL1, heLne⟩ := hnotL
    obtain ⟨eR, heRE, heR2, heRne⟩ := hnotR
    constructor
    · have hne2 : Fin.natAdd m e.2 ≠ Fin.natAdd m eL.2 := by
        intro h
        have h2 : e.2 = eL.2 := hNatInj h
        exact heLne (Prod.ext heL1 h2.symm)
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
        have h1 : e.1 = eR.1 := hCastInj h
        exact heRne (Prod.ext h1.symm heR2)
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
  have hNonMatch : ∀ e ∈ E \ M,
      (2 : ℕ) ≤ (G.neighborSet (Fin.castAdd n e.1)).ncard ∧
      (2 : ℕ) ≤ (G.neighborSet (Fin.natAdd m e.2)).ncard ∧
      (∃ e' ∈ M, e'.1 = e.1 ∨ e'.2 = e.2) ∧
      ∀ V : Finset (Fin (m + n)),
        (∀ e' ∈ E.erase e, Fin.castAdd n e'.1 ∈ V ∨ Fin.natAdd m e'.2 ∈ V) →
        C.size ≤ (E.erase e).card + V.card - (1 : ℕ) :=
    fun e he => ⟨(hDegGe2 e he).1, (hDegGe2 e he).2, hMax e he, hBound e he⟩
  by_cases hStrict : ∃ v : Fin (m + n),
      (2 : ℕ) ≤ (G.neighborSet v).ncard ∧
      (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card < (G.neighborSet v).ncard
  · exact hStrictReader m n E M C G hAdj hCyc hRep hMatch hSub hSdiffNe hC4 hNonMatch hStrict
  · refine hExactReaders m n E M C G hAdj hCyc hRep hMatch hSub hSdiffNe hC4 hNonMatch ?_
    intro v R hdv
    have hnotlt : ¬ R.card < (G.neighborSet v).ncard :=
      fun h => hStrict ⟨v, hdv, h⟩
    have hnotgt : ¬ (G.neighborSet v).ncard < R.card :=
      fun h => hNotBad ⟨v, hdv, Or.inl h⟩
    have heq : R.card = (G.neighborSet v).ncard := by omega
    refine ⟨heq, ?_⟩
    intro g hg hop
    by_contra hnsub
    exact hNotBad ⟨v, hdv, Or.inr ⟨heq.symm, g, hg, hop, hnsub⟩⟩
