import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7866_5
    (hSingleJunk :
      ∃ (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (M : Finset (Sym2 (Fin n))),
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (PEqualNP.TopForm.junk G C).card = (1 : ℕ) →
        M ⊆ G.edgeFinset →
        M.Nonempty →
        (∀ e ∈ M, ∀ f ∈ M, ∀ v ∈ e, v ∈ f → e = f) →
        (∀ e ∈ G.edgeFinset, ∃ f ∈ M, ∃ v ∈ e, v ∈ f) →
        G.edgeFinset.card + M.card ≤ C.size + (1 : ℕ) + c * (n + (1 : ℕ)).sqrt)
    (hMultiJunk :
      ∃ (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (M : Finset (Sym2 (Fin n))),
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
        M ⊆ G.edgeFinset →
        M.Nonempty →
        (∀ e ∈ M, ∀ f ∈ M, ∀ v ∈ e, v ∈ f → e = f) →
        (∀ e ∈ G.edgeFinset, ∃ f ∈ M, ∃ v ∈ e, v ∈ f) →
        G.edgeFinset.card + M.card ≤ C.size + (1 : ℕ) + c * (n + (1 : ℕ)).sqrt) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Sym2 (Fin x2))), PEqualNP.TopForm.NoFourCycle x3 → (∃ (x8 : Fin x2) (x9 : Fin x2), x3.Adj x8 x9) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → (∀ x12 ∈ x6, x12 ∈ x3.edgeSet) → (∀ x13 ∈ x6, ∀ x15 ∈ x6, ∀ x17 ∈ x13, x17 ∈ x15 → x13 = x15) → x3.edgeSet.ncard + x6.card ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt := by
  classical
  obtain ⟨c1, hc1⟩ := hSingleJunk
  obtain ⟨c2, hc2⟩ := hMultiJunk
  refine ⟨max c1 c2, ?_⟩
  intro n G _ C M hC4 hAdj hLeast hTop hJunk hMsub hMdisj
  obtain ⟨u0, v0, huv0⟩ := hAdj
  have hEne : G.edgeFinset.Nonempty := ⟨s(u0, v0), SimpleGraph.mem_edgeFinset.mpr huv0⟩
  have hMsub' : M ⊆ G.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr (hMsub e he)
  let matchings : Finset (Finset (Sym2 (Fin n))) :=
    G.edgeFinset.powerset.filter (fun M0 => ∀ e ∈ M0, ∀ f ∈ M0, ∀ v ∈ e, v ∈ f → e = f)
  have hMmem : M ∈ matchings :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hMsub', hMdisj⟩
  obtain ⟨M', hM'mem, hM'max⟩ := Finset.exists_max_image matchings Finset.card ⟨M, hMmem⟩
  have hM'sub : M' ⊆ G.edgeFinset := Finset.mem_powerset.mp (Finset.mem_filter.mp hM'mem).1
  have hM'disj : ∀ e ∈ M', ∀ f ∈ M', ∀ v ∈ e, v ∈ f → e = f := (Finset.mem_filter.mp hM'mem).2
  have hMleM' : M.card ≤ M'.card := hM'max M hMmem
  have hSingMem : ({s(u0, v0)} : Finset (Sym2 (Fin n))) ∈ matchings := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro e he
      rw [Finset.mem_singleton.mp he]
      exact SimpleGraph.mem_edgeFinset.mpr huv0
    · intro e he f hf _ _ _
      rw [Finset.mem_singleton.mp he, Finset.mem_singleton.mp hf]
  have hM'ne : M'.Nonempty := by
    have h1 : 1 ≤ M'.card := by
      simpa only [Finset.card_singleton] using hM'max {s(u0, v0)} hSingMem
    exact Finset.card_pos.mp (by omega)
  have hM'maximal : ∀ e ∈ G.edgeFinset, ∃ f ∈ M', ∃ v ∈ e, v ∈ f := by
    intro e he
    by_contra hnone
    push Not at hnone
    have henot : e ∉ M' := by
      intro heM
      have hex : ∃ a : Fin n, a ∈ e := Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left a b⟩) e
      obtain ⟨a, ha⟩ := hex
      exact hnone e heM a ha ha
    have hinsMem : insert e M' ∈ matchings := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxM
        · exact he
        · exact hM'sub hxM
      · intro x hx y hy v hvx hvy
        rcases Finset.mem_insert.mp hx with rfl | hxM <;> rcases Finset.mem_insert.mp hy with rfl | hyM
        · rfl
        · exact False.elim (hnone y hyM v hvx hvy)
        · exact False.elim (hnone x hxM v hvy hvx)
        · exact hM'disj x hxM y hyM v hvx hvy
    have hle := hM'max (insert e M') hinsMem
    rw [Finset.card_insert_of_notMem henot] at hle
    omega
  have hjpos : 0 < (PEqualNP.TopForm.junk G C).card := Finset.card_pos.mpr hJunk
  have hbd : G.edgeFinset.card + M'.card ≤ C.size + (1 : ℕ) + max c1 c2 * (n + (1 : ℕ)).sqrt := by
    by_cases hj1 : (PEqualNP.TopForm.junk G C).card = 1
    · have h1 := hc1 n G C M' hC4 hEne hLeast hTop hj1 hM'sub hM'ne hM'disj hM'maximal
      have hmul : c1 * (n + 1).sqrt ≤ max c1 c2 * (n + 1).sqrt :=
        Nat.mul_le_mul_right _ (le_max_left c1 c2)
      omega
    · have hj2 : 2 ≤ (PEqualNP.TopForm.junk G C).card := by omega
      have h2 := hc2 n G C M' hC4 hEne hLeast hTop hj2 hM'sub hM'ne hM'disj hM'maximal
      have hmul : c2 * (n + 1).sqrt ≤ max c1 c2 * (n + 1).sqrt :=
        Nat.mul_le_mul_right _ (le_max_right c1 c2)
      omega
  have hncard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset]
    exact Set.ncard_coe_finset G.edgeFinset
  rw [hncard]
  omega
