import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17440_5
    (hRestrict :
      ∀ (m n m' n' : ℕ) (fL : Fin m' → Fin m) (fR : Fin n' → Fin n)
        (E : Finset (Fin m × Fin n)) (E' : Finset (Fin m' × Fin n'))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        Function.Injective fL →
        Function.Injective fR →
        E'.Nonempty →
        (∀ p : Fin m' × Fin n', p ∈ E' ↔ (fL p.1, fR p.2) ∈ E) →
        (∀ e ∈ E, (∃ a : Fin m', fL a = e.1) ∧ (∃ b : Fin n', fR b = e.2)) →
        PEqualNP.TopForm.IsAO2 (m + n) C →
        (∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C x =
          Decidable.decide (∃ e ∈ E, x (Fin.castAdd n e.1) = Bool.true ∧ x (Fin.natAdd m e.2) = Bool.true)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ C.size ∧
          PEqualNP.TopForm.IsAO2 (m' + n') D ∧
          (∀ x : Fin (m' + n') → Bool, PEqualNP.MetaComplexity.circuitFun (m' + n') D x =
            Decidable.decide (∃ p ∈ E', x (Fin.castAdd n' p.1) = Bool.true ∧ x (Fin.natAdd m' p.2) = Bool.true)) ∧
          (∀ g ∈ D.gates, g.inputs.Nodup) ∧
          (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (m' + n') → Bool,
            (D.wires (List.ofFn x)).getD (m' + n' + i.val) Bool.false ≠
            (D.wires (List.ofFn x)).getD (m' + n' + j.val) Bool.false))
    (hCore :
      ∀ (m' n' : ℕ) (E' : Finset (Fin m' × Fin n')) (D : PEqualNP.CircuitLowerBounds.Circuit),
        E'.Nonempty →
        (∀ a : Fin m', ∃ b : Fin n', (a, b) ∈ E') →
        (∀ b : Fin n', ∃ a : Fin m', (a, b) ∈ E') →
        (∀ (a a' : Fin m') (b b' : Fin n'), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E' ∧ (a, b') ∈ E' ∧ (a', b) ∈ E' ∧ (a', b') ∈ E')) →
        PEqualNP.TopForm.IsAO2 (m' + n') D →
        (∀ x : Fin (m' + n') → Bool, PEqualNP.MetaComplexity.circuitFun (m' + n') D x =
          Decidable.decide (∃ p ∈ E', x (Fin.castAdd n' p.1) = Bool.true ∧ x (Fin.natAdd m' p.2) = Bool.true)) →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (m' + n') → Bool,
          (D.wires (List.ofFn x)).getD (m' + n' + i.val) Bool.false ≠
          (D.wires (List.ofFn x)).getD (m' + n' + j.val) Bool.false) →
        ∃ (L' : Finset (Fin m')) (R' : Finset (Fin n')),
          (∀ p ∈ E', p.1 ∈ L' ∨ p.2 ∈ R') ∧ E'.card + L'.card + R'.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x2)), (∀ x10 ∈ x3, x10.1 ∈ x8 ∨ x10.2 ∈ x9) ∧ x3.card + x8.card + x9.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro m n E C hc4 hAO hfun0
  have hfun : ∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C x =
      Decidable.decide (∃ e ∈ E, x (Fin.castAdd n e.1) = Bool.true ∧ x (Fin.natAdd m e.2) = Bool.true) := by
    intro x
    rw [hfun0 x]
    simp only [decide_eq_decide]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩; exact ⟨(a, b), hab, ha, hb⟩
    · rintro ⟨e, he, ha, hb⟩; exact ⟨e.1, e.2, he, ha, hb⟩
  by_cases hEemp : E = ∅
  · subst hEemp
    exact ⟨∅, ∅, by simp, Nat.zero_le _⟩
  have hEne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEemp
  let L0 : Finset (Fin m) := E.image Prod.fst
  let R0 : Finset (Fin n) := E.image Prod.snd
  let m' : ℕ := L0.card
  let n' : ℕ := R0.card
  let eL : ↥L0 ≃ Fin m' := L0.equivFin
  let eR : ↥R0 ≃ Fin n' := R0.equivFin
  let fL : Fin m' → Fin m := fun a => (eL.symm a).1
  let fR : Fin n' → Fin n := fun b => (eR.symm b).1
  have hfL_inj : Function.Injective fL := by
    intro a1 a2 h
    exact eL.symm.injective (Subtype.ext h)
  have hfR_inj : Function.Injective fR := by
    intro b1 b2 h
    exact eR.symm.injective (Subtype.ext h)
  let φ : Fin m' × Fin n' → Fin m × Fin n := fun p => (fL p.1, fR p.2)
  have hφ_inj : Function.Injective φ := by
    intro p1 p2 h
    exact Prod.ext (hfL_inj (Prod.mk.inj h).1) (hfR_inj (Prod.mk.inj h).2)
  let E' : Finset (Fin m' × Fin n') := Finset.univ.filter (fun p => φ p ∈ E)
  have hE'_mem : ∀ p : Fin m' × Fin n', p ∈ E' ↔ (fL p.1, fR p.2) ∈ E := by
    intro p
    simp only [E', φ, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcover_f : ∀ e ∈ E, (∃ a : Fin m', fL a = e.1) ∧ (∃ b : Fin n', fR b = e.2) := by
    intro e he
    have he1 : e.1 ∈ L0 := Finset.mem_image.mpr ⟨e, he, rfl⟩
    have he2 : e.2 ∈ R0 := Finset.mem_image.mpr ⟨e, he, rfl⟩
    refine ⟨⟨eL ⟨e.1, he1⟩, ?_⟩, ⟨eR ⟨e.2, he2⟩, ?_⟩⟩
    · simp only [fL, Equiv.symm_apply_apply]
    · simp only [fR, Equiv.symm_apply_apply]
  have hE'_image : E'.image φ = E := by
    ext e
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hE'_mem p).mp hp
    · intro he
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcover_f e he
      refine ⟨(a, b), (hE'_mem (a, b)).mpr ?_, ?_⟩
      · simpa only [ha, hb] using he
      · exact Prod.ext ha hb
  have hE'_card : E'.card = E.card := by
    rw [← hE'_image]
    exact (Finset.card_image_of_injective E' hφ_inj).symm
  have hE'_ne : E'.Nonempty := by
    obtain ⟨e, he⟩ := hEne
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcover_f e he
    exact ⟨(a, b), (hE'_mem (a, b)).mpr (by simpa only [ha, hb] using he)⟩
  have hdegL : ∀ a : Fin m', ∃ b : Fin n', (a, b) ∈ E' := by
    intro a
    have haL : fL a ∈ L0 := (eL.symm a).2
    obtain ⟨e, he, hfst⟩ := Finset.mem_image.mp haL
    obtain ⟨_, ⟨b, hb⟩⟩ := hcover_f e he
    refine ⟨b, (hE'_mem (a, b)).mpr ?_⟩
    rw [← hfst, hb]
    exact he
  have hdegR : ∀ b : Fin n', ∃ a : Fin m', (a, b) ∈ E' := by
    intro b
    have hbR : fR b ∈ R0 := (eR.symm b).2
    obtain ⟨e, he, hsnd⟩ := Finset.mem_image.mp hbR
    obtain ⟨⟨a, ha⟩, _⟩ := hcover_f e he
    refine ⟨a, (hE'_mem (a, b)).mpr ?_⟩
    rw [ha, ← hsnd]
    exact he
  have hc4' : ∀ (a a' : Fin m') (b b' : Fin n'), a ≠ a' → b ≠ b' →
      ¬((a, b) ∈ E' ∧ (a, b') ∈ E' ∧ (a', b) ∈ E' ∧ (a', b') ∈ E') := by
    intro a a' b b' ha hb h
    exact hc4 (fL a) (fL a') (fR b) (fR b')
      (fun h' => ha (hfL_inj h')) (fun h' => hb (hfR_inj h'))
      ⟨(hE'_mem _).mp h.1, (hE'_mem _).mp h.2.1, (hE'_mem _).mp h.2.2.1, (hE'_mem _).mp h.2.2.2⟩
  obtain ⟨D, hDle, hDAO, hDfun, hDnd, hDdist⟩ :=
    hRestrict m n m' n' fL fR E E' C hfL_inj hfR_inj hE'_ne hE'_mem hcover_f hAO hfun
  obtain ⟨L', R', hcov', hcard'⟩ :=
    hCore m' n' E' D hE'_ne hdegL hdegR hc4' hDAO hDfun hDnd hDdist
  refine ⟨L'.image fL, R'.image fR, ?_, ?_⟩
  · intro e he
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcover_f e he
    have hp : (a, b) ∈ E' := (hE'_mem (a, b)).mpr (by simpa only [ha, hb] using he)
    rcases hcov' (a, b) hp with hL | hR
    · exact Or.inl (Finset.mem_image.mpr ⟨a, hL, ha⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨b, hR, hb⟩)
  · have hLc : (L'.image fL).card = L'.card := Finset.card_image_of_injective L' hfL_inj
    have hRc : (R'.image fR).card = R'.card := Finset.card_image_of_injective R' hfR_inj
    rw [hLc, hRc, ← hE'_card]
    omega
