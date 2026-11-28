import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7977_2
    (hHasOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1;
        have A : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →
        (26 : ℕ) ≤ x2 ∧ x2 < (26 : ℕ) + x1.size →
        (26 : ℕ) ≤ x3 ∧ x3 < (26 : ℕ) + x1.size →
        x2 ≠ x3 →
        (ga (x2 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        have x8 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
        have x9 : ℕ → List Bool → Prop := fun (x9 : ℕ) (x10 : List Bool) => ∃ x11 < x1.size, PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x9 x11 ∧ (ga x11).op = A ∧ PEqualNP.CircuitLowerBounds.wireValue x1 x10 ((26 : ℕ) + x11) = Bool.true;
        have x10 : ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x10 : ℕ) (x11 x12 : Fin (13 : ℕ)) => x9 x10 (PEqualNP.GenericRejection.incidenceInput {x11} {x12});
        (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x8 x12 → x10 x2 x11 x12 ∨ x10 x3 x11 x12) →
        (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x8 x12 → ¬(x9 x2 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)) ∨ x9 x3 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)))) →
        (∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x8 x14 ∧ x10 x2 x13 x14 ∧ ¬x10 x3 x13 x14) →
        (∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x8 x15 ∧ x10 x3 x14 x15 ∧ ¬x10 x2 x14 x15) →
        (∃ (x15 : Finset ℕ), x15.card = (3 : ℕ) ∧ ∀ x16 ∈ x15, x16 < x1.size ∧ (ga x16).op = A ∧ ∃ x18 ∈ (ga x16).inputs, (26 : ℕ) ≤ x18 ∧ (ga (x18 - (26 : ℕ))).op = A) →
        (63 : ℕ) ≤ x1.size)
    (hBothAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1;
        have A : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;
        have x8 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
        have wv : ℕ → List Bool → Prop := fun (w : ℕ) (v : List Bool) => PEqualNP.CircuitLowerBounds.wireValue x1 v w = Bool.true;
        have wp : ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (w : ℕ) (p l : Fin (13 : ℕ)) => wv w (PEqualNP.GenericRejection.incidenceInput {p} {l});
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →
        (26 : ℕ) ≤ x2 ∧ x2 < x3 ∧ x3 < (26 : ℕ) + x1.size →
        (ga (x2 - (26 : ℕ))).op = A →
        (ga (x3 - (26 : ℕ))).op = A →
        (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x8 x12 → wp x2 x11 x12 ∨ wp x3 x11 x12) →
        (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x8 x12 → ¬(wv x2 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)) ∨ wv x3 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)))) →
        (∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x8 x14 ∧ wp x2 x13 x14 ∧ ¬wp x3 x13 x14) →
        (∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x8 x15 ∧ wp x3 x14 x15 ∧ ¬wp x2 x14 x15) →
        (∃ (x15 : Finset ℕ), x15.card = (3 : ℕ) ∧ ∀ x16 ∈ x15, x16 < x1.size ∧ (ga x16).op = A ∧ ∃ x18 ∈ (ga x16).inputs, (26 : ℕ) ≤ x18 ∧ (ga (x18 - (26 : ℕ))).op = A) →
        (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;           have x9 : ℕ → List Bool → Prop := fun (x9 : ℕ) (x10 : List Bool) => ∃ x11 < x1.size, PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x9 x11 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.wireValue x1 x10 ((26 : ℕ) + x11) = Bool.true;           have x10 : ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x10 : ℕ) (x11 x12 : Fin (13 : ℕ)) => x9 x10 (PEqualNP.GenericRejection.incidenceInput {x11} {x12});           (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x8 x12 → x10 x2 x11 x12 ∨ x10 x3 x11 x12) → (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x8 x12 → ¬(x9 x2 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)) ∨ x9 x3 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)))) → (∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x8 x14 ∧ x10 x2 x13 x14 ∧ ¬x10 x3 x13 x14) → (∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x8 x15 ∧ x10 x3 x14 x15 ∧ ¬x10 x2 x14 x15) → (∃ (x15 : Finset ℕ), x15.card = (3 : ℕ) ∧ ∀ x16 ∈ x15, x16 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x16).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x16).inputs, (26 : ℕ) ≤ x18 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x18 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x1.size := by
  intro C x2 x3 hMono hRB hx2Lt hx3Lt x8 x9 x10 hCov hQuad hEx2 hEx3 hThree
  have hx2Ge : 26 ≤ x2 := by
    obtain ⟨p, l, _, h2, _⟩ := hEx2
    obtain ⟨j, _, hOr, _, _⟩ := h2
    exact hOr.1
  have hx3Ge : 26 ≤ x3 := by
    obtain ⟨p, l, _, h3, _⟩ := hEx3
    obtain ⟨j, _, hOr, _, _⟩ := h3
    exact hOr.1
  have hNe : x2 ≠ x3 := by
    intro heq
    obtain ⟨p, l, _, h2, h3n⟩ := hEx2
    rw [heq] at h2
    exact h3n h2
  have hOp : ∀ j, j < C.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro j hj
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j]'hj := by
      change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
      exact List.getD_eq_getElem _ _ hj
    rw [hge]
    have hm := (hMono (C.gates[j]'hj) (List.getElem_mem hj)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  have hOrLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List (List ℕ)),
      (gs.foldl (PEqualNP.CleanedNonEdge.orStep 26) acc).length = acc.length + gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro acc; simp
    | append_singleton gs g ih =>
      intro acc
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((gs.foldl (PEqualNP.CleanedNonEdge.orStep 26) acc) ++ [_]).length = acc.length + (gs ++ [g]).length
      rw [List.length_append, List.length_singleton, List.length_append, List.length_singleton, ih acc]
      omega
  have hOrAtAnd : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List (List ℕ)) (k : ℕ) (hk : k < gs.length),
      (gs[k]'hk).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (gs.foldl (PEqualNP.CleanedNonEdge.orStep 26) acc).getD (acc.length + k) [] = [acc.length + k] := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro acc k hk; simp at hk
    | append_singleton gs g ih =>
      intro acc k hk hop
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hk' : k < gs.length
      · have hop' : (gs[k]'hk').op = PEqualNP.CircuitLowerBounds.GateOp.and := by
          rw [List.getElem_append_left hk'] at hop
          exact hop
        have hlen := hOrLen gs acc
        change ((gs.foldl (PEqualNP.CleanedNonEdge.orStep 26) acc) ++ [_]).getD (acc.length + k) [] = [acc.length + k]
        rw [List.getD_append _ _ _ _ (by omega)]
        exact ih acc k hk' hop'
      · have hkeq : k = gs.length := by
          rw [List.length_append, List.length_singleton] at hk
          omega
        have hopg : g.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
          have hget : (gs ++ [g])[k]'hk = g := by
            rw [List.getElem_append_right (by omega)]
            simp [hkeq]
          rw [hget] at hop
          exact hop
        have hlen := hOrLen gs acc
        have hneOr : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or := by
          rw [hopg]
          intro h
          cases h
        dsimp only [PEqualNP.CleanedNonEdge.orStep]
        rw [if_neg hneOr]
        have hidx : acc.length + k = (gs.foldl (PEqualNP.CleanedNonEdge.orStep 26) acc).length := by omega
        rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hidx]
  have hAndIff : ∀ w : ℕ, 26 ≤ w → w < 26 + C.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ v : List Bool, x9 w v ↔ PEqualNP.CircuitLowerBounds.wireValue C v w = Bool.true := by
    intro w hwGe hwLt hAnd v
    have hk : w - 26 < C.gates.length := by change w - 26 < C.size; omega
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (w - 26) = C.gates[w - 26]'hk := by
      change C.gates.getD (w - 26) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
      exact List.getD_eq_getElem _ _ hk
    have hop : (C.gates[w - 26]'hk).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
      rw [← hge]
      exact hAnd
    have hset : (PEqualNP.CleanedNonEdge.orSets 26 C).getD (w - 26) [] = [w - 26] := by
      change (C.gates.foldl (PEqualNP.CleanedNonEdge.orStep 26) []).getD (w - 26) [] = [w - 26]
      have h := hOrAtAnd C.gates [] (w - 26) hk hop
      simpa only [List.length_nil, Nat.zero_add] using h
    constructor
    · intro h
      obtain ⟨j, _, hOr, _, hwv⟩ := h
      have hmem : j ∈ [w - 26] := by
        have hm := hOr.2
        rw [hset] at hm
        exact hm
      have hj : j = w - 26 := by
        simpa only [List.mem_singleton] using hmem
      have hadd : 26 + j = w := by omega
      rw [hadd] at hwv
      exact hwv
    · intro hwv
      refine ⟨w - 26, by omega, ⟨hwGe, ?_⟩, hAnd, ?_⟩
      · rw [hset]
        exact List.mem_singleton.mpr rfl
      · have hadd : 26 + (w - 26) = w := by omega
        rw [hadd]
        exact hwv
  rcases hOp (x2 - 26) (by omega) with h2And | h2Or
  · rcases hOp (x3 - 26) (by omega) with h3And | h3Or
    · have hi2 := hAndIff x2 hx2Ge hx2Lt h2And
      have hi3 := hAndIff x3 hx3Ge hx3Lt h3And
      have hCov' : ∀ (p l : Fin 13), p ∈ x8 l →
          PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) x2 = Bool.true ∨
          PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) x3 = Bool.true := by
        intro p l hpl
        rcases hCov p l hpl with h2 | h3
        · exact Or.inl ((hi2 _).mp h2)
        · exact Or.inr ((hi3 _).mp h3)
      have hQuad' : ∀ (Q : Finset (Fin 13)), PEqualNP.HeptadCover.IsQuadrangle x8 Q →
          ¬(PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines x8 Q)) x2 = Bool.true ∨
            PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines x8 Q)) x3 = Bool.true) := by
        intro Q hQ h
        apply hQuad Q hQ
        rcases h with h2 | h3
        · exact Or.inl ((hi2 _).mpr h2)
        · exact Or.inr ((hi3 _).mpr h3)
      have hEx2' : ∃ (p l : Fin 13), p ∈ x8 l ∧
          PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) x2 = Bool.true ∧
          ¬PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) x3 = Bool.true := by
        obtain ⟨p, l, hpl, h2, h3n⟩ := hEx2
        exact ⟨p, l, hpl, (hi2 _).mp h2, fun h3 => h3n ((hi3 _).mpr h3)⟩
      have hEx3' : ∃ (p l : Fin 13), p ∈ x8 l ∧
          PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) x3 = Bool.true ∧
          ¬PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) x2 = Bool.true := by
        obtain ⟨p, l, hpl, h3, h2n⟩ := hEx3
        exact ⟨p, l, hpl, (hi3 _).mp h3, fun h2 => h2n ((hi2 _).mpr h2)⟩
      rcases Nat.lt_or_gt_of_ne hNe with hlt | hgt
      · exact hBothAnd C x2 x3 hMono hRB ⟨hx2Ge, hlt, hx3Lt⟩ h2And h3And hCov' hQuad' hEx2' hEx3' hThree
      · exact hBothAnd C x3 x2 hMono hRB ⟨hx3Ge, hgt, hx2Lt⟩ h3And h2And
          (fun p l hpl => (hCov' p l hpl).symm)
          (fun Q hQ h => hQuad' Q hQ h.symm)
          hEx3' hEx2' hThree
    · exact hHasOr C x3 x2 hMono hRB ⟨hx3Ge, hx3Lt⟩ ⟨hx2Ge, hx2Lt⟩ hNe.symm h3Or
        (fun p l hpl => (hCov p l hpl).symm)
        (fun Q hQ h => hQuad Q hQ h.symm)
        hEx3 hEx2 hThree
  · exact hHasOr C x2 x3 hMono hRB ⟨hx2Ge, hx2Lt⟩ ⟨hx3Ge, hx3Lt⟩ hNe h2Or hCov hQuad hEx2 hEx3 hThree
