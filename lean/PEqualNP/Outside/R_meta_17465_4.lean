import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17465_4
    (hStrictReader :
      ∀ (m n : ℕ) (E : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        have G : SimpleGraph (Fin (m + n)) :=
          SimpleGraph.fromRel fun (u v : Fin (m + n)) =>
            ∃ e ∈ E, u = Fin.castAdd n e.1 ∧ v = Fin.natAdd m e.2;
        have rep : Finset (Fin m × Fin n) → PEqualNP.CircuitLowerBounds.Circuit → Prop :=
          fun E0 C0 => PEqualNP.TopForm.IsAO2 (m + n) C0 ∧
            PEqualNP.MetaComplexity.circuitFun (m + n) C0 =
              PEqualNP.ReadTwo.fpl m (fun (a : Fin m) (b : Fin n) => (a, b) ∈ E0);
        have red : Set (Fin m × Fin n) :=
          {e : Fin m × Fin n | e ∈ E ∧ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size < C.size ∧ rep (E.erase e) D};
        (6 : ℕ) ≤ E.card →
        (∀ e ∈ E, (2 : ℕ) ≤ (G.neighborSet (Fin.castAdd n e.1)).ncard ∧
          (2 : ℕ) ≤ (G.neighborSet (Fin.natAdd m e.2)).ncard) →
        C.size + (3 : ℕ) ≤ (2 : ℕ) * E.card →
        rep E C →
        (PEqualNP.ReadTwo.Lin fun (a : Fin m) (b : Fin n) => (a, b) ∈ E) →
        ¬G.IsAcyclic →
        Set.InjOn Prod.fst red →
        Set.InjOn Prod.snd red →
        (∃ v : Fin (m + n),
          have d : ℕ := (G.neighborSet v).ncard;
          (2 : ℕ) ≤ d ∧ (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card < d) →
        False)
    (hExactReaders :
      ∀ (m n : ℕ) (E : Finset (Fin m × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        have G : SimpleGraph (Fin (m + n)) :=
          SimpleGraph.fromRel fun (u v : Fin (m + n)) =>
            ∃ e ∈ E, u = Fin.castAdd n e.1 ∧ v = Fin.natAdd m e.2;
        have rep : Finset (Fin m × Fin n) → PEqualNP.CircuitLowerBounds.Circuit → Prop :=
          fun E0 C0 => PEqualNP.TopForm.IsAO2 (m + n) C0 ∧
            PEqualNP.MetaComplexity.circuitFun (m + n) C0 =
              PEqualNP.ReadTwo.fpl m (fun (a : Fin m) (b : Fin n) => (a, b) ∈ E0);
        have red : Set (Fin m × Fin n) :=
          {e : Fin m × Fin n | e ∈ E ∧ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size < C.size ∧ rep (E.erase e) D};
        (6 : ℕ) ≤ E.card →
        (∀ e ∈ E, (2 : ℕ) ≤ (G.neighborSet (Fin.castAdd n e.1)).ncard ∧
          (2 : ℕ) ≤ (G.neighborSet (Fin.natAdd m e.2)).ncard) →
        C.size + (3 : ℕ) ≤ (2 : ℕ) * E.card →
        rep E C →
        (PEqualNP.ReadTwo.Lin fun (a : Fin m) (b : Fin n) => (a, b) ∈ E) →
        ¬G.IsAcyclic →
        Set.InjOn Prod.fst red →
        Set.InjOn Prod.snd red →
        (∀ v : Fin (m + n),
          have d : ℕ := (G.neighborSet v).ncard;
          have R : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) C ↑v;
          (2 : ℕ) ≤ d →
          R.card = d ∧
          ∀ g ∈ R,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.TopForm.readers (m + n) C g ⊆ R) →
        False) :
    ∀ (x1 x2 : ℕ),   have x3 : Finset (Fin x1 × Fin x2) → SimpleGraph (Fin (x1 + x2)) := fun (x3 : Finset (Fin x1 × Fin x2)) => SimpleGraph.fromRel fun (x4 x5 : Fin (x1 + x2)) => ∃ x6 ∈ x3, x4 = Fin.castAdd x2 x6.1 ∧ x5 = Fin.natAdd x1 x6.2;   have x4 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = PEqualNP.ReadTwo.fpl x1 fun (x6 : Fin x1) (x7 : Fin x2) => (x6, x7) ∈ x4;   have x5 : Finset (Fin x1 × Fin x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Finset (Fin x1 × Fin x2)) (x6 : Fin x1 × Fin x2) => (∀ x7 ∈ x5, x7.1 = x6.1 → x7 = x6) ∨ ∀ x7 ∈ x5, x7.2 = x6.2 → x7 = x6;   have x6 : Finset (Fin x1 × Fin x2) → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) =>     (6 : ℕ) ≤ x6.card ∧       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         have x8 : Set (Fin x1 × Fin x2) := {x8 : Fin x1 × Fin x2 | x8 ∈ x6 ∧ (x5 x6 x8 ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size < x7.size ∧ x4 (x6.erase x8) x9)};         x7.size + (3 : ℕ) ≤ (2 : ℕ) * x6.card ∧           x4 x6 x7 ∧             (PEqualNP.ReadTwo.Lin fun (x9 : Fin x1) (x10 : Fin x2) => (x9, x10) ∈ x6) ∧               ¬(x3 x6).IsAcyclic ∧                 (∀ (x9 : Fin (x1 + x2)),                     have x10 : ℕ := ((x3 x6).neighborSet x9).ncard;                     have x11 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x7 ↑x9;                     (2 : ℕ) ≤ x10 → x11.card ≤ x10 ∧ (x10 = x11.card → ∀ x14 ∈ x11, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (x1 + x2) x7 x14 ⊆ x11)) ∧                   Set.InjOn Prod.fst x8 ∧ Set.InjOn Prod.snd x8;   ∀ (x7 : Finset (Fin x1 × Fin x2)), (∀ x8 ∈ x7, ¬x5 x7 x8) → ¬x6 x7 := by
  classical
  intro m n Gfn rep leaf P E hNoLeaf hP
  obtain ⟨hCard, C, hSz, hRep, hLin, hCyc, hRead, hInj1, hInj2⟩ := hP
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
  have hDegGe2 : ∀ e ∈ E, (2 : ℕ) ≤ ((Gfn E).neighborSet (Fin.castAdd n e.1)).ncard ∧
      (2 : ℕ) ≤ ((Gfn E).neighborSet (Fin.natAdd m e.2)).ncard := by
    intro e he
    have hnl := hNoLeaf e he
    have hnotL : ¬∀ e' ∈ E, e'.1 = e.1 → e' = e := fun h => hnl (Or.inl h)
    have hnotR : ¬∀ e' ∈ E, e'.2 = e.2 → e' = e := fun h => hnl (Or.inr h)
    push Not at hnotL hnotR
    obtain ⟨eL, heLE, heL1, heLne⟩ := hnotL
    obtain ⟨eR, heRE, heR2, heRne⟩ := hnotR
    constructor
    · have hne2 : Fin.natAdd m e.2 ≠ Fin.natAdd m eL.2 := by
        intro h
        exact heLne (Prod.ext heL1 (hNatInj h).symm)
      have hsub2 : ({Fin.natAdd m e.2, Fin.natAdd m eL.2} : Set (Fin (m + n))) ⊆
          (Gfn E).neighborSet (Fin.castAdd n e.1) := by
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rw [SimpleGraph.mem_neighborSet, SimpleGraph.fromRel_adj]
        rcases hw with rfl | rfl
        · exact ⟨hSepLR e.1 e.2, Or.inl ⟨e, he, rfl, rfl⟩⟩
        · exact ⟨hSepLR e.1 eL.2, Or.inl ⟨eL, heLE, congrArg (Fin.castAdd n) heL1.symm, rfl⟩⟩
      have hle := Set.ncard_le_ncard hsub2 (Set.toFinite _)
      rw [Set.ncard_pair hne2] at hle
      exact hle
    · have hne2 : Fin.castAdd n e.1 ≠ Fin.castAdd n eR.1 := by
        intro h
        exact heRne (Prod.ext (hCastInj h).symm heR2)
      have hsub2 : ({Fin.castAdd n e.1, Fin.castAdd n eR.1} : Set (Fin (m + n))) ⊆
          (Gfn E).neighborSet (Fin.natAdd m e.2) := by
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rw [SimpleGraph.mem_neighborSet, SimpleGraph.fromRel_adj]
        rcases hw with rfl | rfl
        · exact ⟨(hSepLR e.1 e.2).symm, Or.inr ⟨e, he, rfl, rfl⟩⟩
        · exact ⟨(hSepLR eR.1 e.2).symm, Or.inr ⟨eR, heRE, rfl, congrArg (Fin.natAdd m) heR2.symm⟩⟩
      have hle := Set.ncard_le_ncard hsub2 (Set.toFinite _)
      rw [Set.ncard_pair hne2] at hle
      exact hle
  have hRedSub : {e : Fin m × Fin n | e ∈ E ∧ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size < C.size ∧ rep (E.erase e) D} ⊆
      {e : Fin m × Fin n | e ∈ E ∧ (leaf E e ∨ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size < C.size ∧ rep (E.erase e) D)} := by
    intro e he
    exact ⟨he.1, Or.inr he.2⟩
  have hInj1' := hInj1.mono hRedSub
  have hInj2' := hInj2.mono hRedSub
  by_cases hStrict : ∃ v : Fin (m + n),
      (2 : ℕ) ≤ ((Gfn E).neighborSet v).ncard ∧
      (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card < ((Gfn E).neighborSet v).ncard
  · exact hStrictReader m n E C hCard hDegGe2 hSz hRep hLin hCyc hInj1' hInj2' hStrict
  · refine hExactReaders m n E C hCard hDegGe2 hSz hRep hLin hCyc hInj1' hInj2' ?_
    intro v d R hdv
    have hr := hRead v hdv
    have hnotlt : ¬ R.card < d :=
      fun h => hStrict ⟨v, hdv, h⟩
    have heq : R.card = d := by
      have hle : R.card ≤ d := hr.1
      omega
    exact ⟨heq, hr.2 heq.symm⟩
