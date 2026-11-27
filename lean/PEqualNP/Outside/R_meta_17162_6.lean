import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17162_6
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
        (2 : ℕ) ≤ m' →
        (2 : ℕ) ≤ n' →
        (3 : ℕ) ≤ E'.card →
        (∀ a : Fin m', ∃ b : Fin n', (a, b) ∈ E') →
        (∀ b : Fin n', ∃ a : Fin m', (a, b) ∈ E') →
        (∀ (a a' : Fin m') (b b' : Fin n'), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E' ∧ (a, b') ∈ E' ∧ (a', b) ∈ E' ∧ (a', b') ∈ E')) →
        (¬∃ (A B : Finset (Fin m' × Fin n')) (v : Fin (m' + n')),
          A.Nonempty ∧ A ∪ B = E' ∧
          Disjoint (A.biUnion fun e => {Fin.castAdd n' e.1, Fin.natAdd m' e.2})
            (B.biUnion fun e => {Fin.castAdd n' e.1, Fin.natAdd m' e.2}) ∧
          ∀ e ∈ A, Fin.castAdd n' e.1 = v ∨ Fin.natAdd m' e.2 = v) →
        PEqualNP.TopForm.IsAO2 (m' + n') D →
        (∀ x : Fin (m' + n') → Bool, PEqualNP.MetaComplexity.circuitFun (m' + n') D x =
          Decidable.decide (∃ p ∈ E', x (Fin.castAdd n' p.1) = Bool.true ∧ x (Fin.natAdd m' p.2) = Bool.true)) →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (m' + n') → Bool,
          (D.wires (List.ofFn x)).getD (m' + n' + i.val) Bool.false ≠
          (D.wires (List.ofFn x)).getD (m' + n' + j.val) Bool.false) →
        ∃ (L' : Finset (Fin m')) (R' : Finset (Fin n')),
          (∀ p ∈ E', p.1 ∈ L' ∨ p.2 ∈ R') ∧ E'.card + L'.card + R'.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   ¬(x1 = (3 : ℕ) ∧ ∀ (x6 : Fin x1), ∃ (x7 : Fin x2), ∀ (x8 : Fin x1), (x8, x7) ∈ x3 ↔ x8 ≠ x6) → (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x9 = Decidable.decide (∃ x10 ∈ x3, x9 (Fin.castAdd x2 x10.1) = Bool.true ∧ x9 (Fin.natAdd x1 x10.2) = Bool.true)) → (¬∃ (x10 : Finset (Fin x1 × Fin x2)) (x11 : Finset (Fin x1 × Fin x2)) (x12 : Fin (x1 + x2)), x10.Nonempty ∧ x10 ∪ x11 = x3 ∧ Disjoint (x5 x10) (x5 x11) ∧ ∀ x13 ∈ x10, Fin.castAdd x2 x13.1 = x12 ∨ Fin.natAdd x1 x13.2 = x12) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro m n E C supp _hNot3 hc4 hAO hfun hsep
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
  let ψ : Fin (m' + n') → Fin (m + n) :=
    Fin.addCases (fun a => Fin.castAdd n (fL a)) (fun b => Fin.natAdd m (fR b))
  have hψ_cast : ∀ a : Fin m', ψ (Fin.castAdd n' a) = Fin.castAdd n (fL a) := by
    intro a
    simp only [ψ, Fin.addCases_left]
  have hψ_nat : ∀ b : Fin n', ψ (Fin.natAdd m' b) = Fin.natAdd m (fR b) := by
    intro b
    simp only [ψ, Fin.addCases_right]
  have hψ_inj : Function.Injective ψ := by
    intro u v huv
    refine Fin.addCases (motive := fun u => ψ u = ψ v → u = v) ?_ ?_ u huv
    · intro a
      refine Fin.addCases (motive := fun v => ψ (Fin.castAdd n' a) = ψ v → Fin.castAdd n' a = v) ?_ ?_ v
      · intro a' h
        rw [hψ_cast, hψ_cast] at h
        have hv : (fL a).val = (fL a').val := by
          have := congrArg Fin.val h
          simpa only [Fin.val_castAdd] using this
        have ha : a = a' := hfL_inj (Fin.ext hv)
        rw [ha]
      · intro b' h
        rw [hψ_cast, hψ_nat] at h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
    · intro b
      refine Fin.addCases (motive := fun v => ψ (Fin.natAdd m' b) = ψ v → Fin.natAdd m' b = v) ?_ ?_ v
      · intro a' h
        rw [hψ_nat, hψ_cast] at h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      · intro b' h
        rw [hψ_nat, hψ_nat] at h
        have hv : (fR b).val = (fR b').val := by
          have := congrArg Fin.val h
          simp only [Fin.val_natAdd] at this
          omega
        have hb : b = b' := hfR_inj (Fin.ext hv)
        rw [hb]
  let supp' : Finset (Fin m' × Fin n') → Finset (Fin (m' + n')) :=
    fun S => S.biUnion fun e => {Fin.castAdd n' e.1, Fin.natAdd m' e.2}
  have hsupp_img : ∀ S : Finset (Fin m' × Fin n'), supp (S.image φ) = (supp' S).image ψ := by
    intro S
    ext w
    simp only [supp, supp', Finset.mem_biUnion, Finset.mem_image, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨e, ⟨p, hp, rfl⟩, hw | hw⟩
      · exact ⟨Fin.castAdd n' p.1, ⟨p, hp, Or.inl rfl⟩, by rw [hψ_cast]; exact hw.symm⟩
      · exact ⟨Fin.natAdd m' p.2, ⟨p, hp, Or.inr rfl⟩, by rw [hψ_nat]; exact hw.symm⟩
    · rintro ⟨u, ⟨p, hp, hu | hu⟩, rfl⟩
      · refine ⟨φ p, ⟨p, hp, rfl⟩, Or.inl ?_⟩
        rw [hu, hψ_cast]
      · refine ⟨φ p, ⟨p, hp, rfl⟩, Or.inr ?_⟩
        rw [hu, hψ_nat]
  have hsep' : ¬∃ (A B : Finset (Fin m' × Fin n')) (v : Fin (m' + n')),
      A.Nonempty ∧ A ∪ B = E' ∧ Disjoint (supp' A) (supp' B) ∧
      ∀ e ∈ A, Fin.castAdd n' e.1 = v ∨ Fin.natAdd m' e.2 = v := by
    rintro ⟨A, B, v, hAne, hAB, hdisj, hstar⟩
    apply hsep
    refine ⟨A.image φ, B.image φ, ψ v, hAne.image φ, ?_, ?_, ?_⟩
    · rw [← Finset.image_union, hAB, hE'_image]
    · rw [hsupp_img A, hsupp_img B, Finset.disjoint_left]
      intro w hwA hwB
      obtain ⟨u, huA, rfl⟩ := Finset.mem_image.mp hwA
      obtain ⟨u', huB, huEq⟩ := Finset.mem_image.mp hwB
      have huu : u' = u := hψ_inj huEq
      rw [huu] at huB
      exact Finset.disjoint_left.mp hdisj huA huB
    · intro e he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      rcases hstar p hp with h1 | h2
      · left
        rw [← hψ_cast, h1]
      · right
        rw [← hψ_nat, h2]
  have hcard3 : (3 : ℕ) ≤ E'.card := by
    by_contra hlt
    have hpos : 0 < E'.card := Finset.card_pos.mpr hE'_ne
    have h12 : E'.card = 1 ∨ E'.card = 2 := by omega
    rcases h12 with h1 | h2
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
      apply hsep'
      refine ⟨{p}, ∅, Fin.castAdd n' p.1, Finset.singleton_nonempty p, ?_, ?_, ?_⟩
      · simp only [Finset.union_empty, hp]
      · simp only [supp', Finset.biUnion_empty, Finset.disjoint_empty_right]
      · intro e he
        rw [Finset.mem_singleton.mp he]
        exact Or.inl rfl
    · obtain ⟨p, q, hpq, hE2⟩ := Finset.card_eq_two.mp h2
      by_cases h1eq : p.1 = q.1
      · apply hsep'
        refine ⟨E', ∅, Fin.castAdd n' p.1, hE'_ne, Finset.union_empty E', ?_, ?_⟩
        · simp only [supp', Finset.biUnion_empty, Finset.disjoint_empty_right]
        · intro e he
          rw [hE2, Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inl (congrArg (Fin.castAdd n') h1eq.symm)
      · by_cases h2eq : p.2 = q.2
        · apply hsep'
          refine ⟨E', ∅, Fin.natAdd m' p.2, hE'_ne, Finset.union_empty E', ?_, ?_⟩
          · simp only [supp', Finset.biUnion_empty, Finset.disjoint_empty_right]
          · intro e he
            rw [hE2, Finset.mem_insert, Finset.mem_singleton] at he
            rcases he with rfl | rfl
            · exact Or.inr rfl
            · exact Or.inr (congrArg (Fin.natAdd m') h2eq.symm)
        · apply hsep'
          refine ⟨{p}, {q}, Fin.castAdd n' p.1, Finset.singleton_nonempty p, ?_, ?_, ?_⟩
          · rw [hE2]
            ext e
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          · rw [Finset.disjoint_left]
            intro w hw1 hw2
            simp only [supp', Finset.mem_biUnion, Finset.mem_insert,
              Finset.mem_singleton] at hw1 hw2
            obtain ⟨e1, he1, h1⟩ := hw1
            obtain ⟨e2, he2, h2⟩ := hw2
            rw [he1] at h1
            rw [he2] at h2
            rcases h1 with rfl | rfl <;> rcases h2 with h | h
            · have hv : p.1.val = q.1.val := by
                have := congrArg Fin.val h
                simpa only [Fin.val_castAdd] using this
              exact h1eq (Fin.ext hv)
            · have hv := congrArg Fin.val h
              simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
              omega
            · have hv := congrArg Fin.val h
              simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
              omega
            · have hv : p.2.val = q.2.val := by
                have := congrArg Fin.val h
                simp only [Fin.val_natAdd] at this
                omega
              exact h2eq (Fin.ext hv)
          · intro e he
            rw [Finset.mem_singleton.mp he]
            exact Or.inl rfl
  have hm'2 : (2 : ℕ) ≤ m' := by
    by_contra hlt
    let p0 : Fin m' × Fin n' := hE'_ne.choose
    have hm1 : m' = 1 := by
      have := p0.1.isLt
      omega
    apply hsep'
    refine ⟨E', ∅, Fin.castAdd n' p0.1, hE'_ne, Finset.union_empty E', ?_, ?_⟩
    · simp only [supp', Finset.biUnion_empty, Finset.disjoint_empty_right]
    · intro e _
      left
      exact congrArg (Fin.castAdd n') (Fin.ext (by have := e.1.isLt; have := p0.1.isLt; omega))
  have hn'2 : (2 : ℕ) ≤ n' := by
    by_contra hlt
    let p0 : Fin m' × Fin n' := hE'_ne.choose
    have hn1 : n' = 1 := by
      have := p0.2.isLt
      omega
    apply hsep'
    refine ⟨E', ∅, Fin.natAdd m' p0.2, hE'_ne, Finset.union_empty E', ?_, ?_⟩
    · simp only [supp', Finset.biUnion_empty, Finset.disjoint_empty_right]
    · intro e _
      right
      exact congrArg (Fin.natAdd m') (Fin.ext (by have := e.2.isLt; have := p0.2.isLt; omega))
  obtain ⟨D, hDle, hDAO, hDfun, hDnd, hDdist⟩ :=
    hRestrict m n m' n' fL fR E E' C hfL_inj hfR_inj hE'_ne hE'_mem hcover_f hAO hfun
  obtain ⟨L', R', hcov', hcard'⟩ :=
    hCore m' n' E' D hm'2 hn'2 hcard3 hdegL hdegR hc4' hsep' hDAO hDfun hDnd hDdist
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
