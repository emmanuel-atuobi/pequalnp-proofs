import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8499_5
    (hIsol :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (fL fR : Fin n ↪ Fin (n + n))
        (C : PEqualNP.CircuitLowerBounds.Circuit) (u0 : Fin n),
        have comp : Finset (Fin n × Fin n) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun F D =>
          ∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x =
            Decidable.decide (∃ a b : Fin n, (a, b) ∈ F ∧ x (fL a) = Bool.true ∧ x (fR b) = Bool.true);
        have E' : Finset (Fin n × Fin n) := E.filter fun e => e.1 ≠ u0 ∧ e.2 ≠ u0;
        (3 : ℕ) ≤ n →
        (∀ a b : Fin n, fL a ≠ fR b) →
        (∀ a b : Fin n, (a, b) ∈ E → (a, a) ∈ E ∧ (b, b) ∈ E) →
        (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        (u0, u0) ∈ E →
        (∃ a b : Fin n, a ≠ b ∧ (a, a) ∈ E' ∧ (b, b) ∈ E') →
        (∀ b : Fin n, (u0, b) ∈ E → b = u0) →
        (∀ a : Fin n, (a, u0) ∈ E → a = u0) →
        PEqualNP.TopForm.IsAO2 (n + n) C →
        comp E C →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 (n + n) D ∧ comp E' D ∧ D.size + (2 : ℕ) ≤ C.size)
    (hNonemptyN :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (fL fR : Fin n ↪ Fin (n + n))
        (C : PEqualNP.CircuitLowerBounds.Circuit) (u0 : Fin n),
        have comp : Finset (Fin n × Fin n) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun F D =>
          ∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x =
            Decidable.decide (∃ a b : Fin n, (a, b) ∈ F ∧ x (fL a) = Bool.true ∧ x (fR b) = Bool.true);
        have N : Finset (Fin n) := (E.filter fun e => e.1 ≠ u0 ∧ e.2 = u0).image Prod.fst;
        have E' : Finset (Fin n × Fin n) := E.filter fun e => e.1 ≠ u0 ∧ e.2 ≠ u0;
        (3 : ℕ) ≤ n →
        (∀ a b : Fin n, fL a ≠ fR b) →
        (∀ a b : Fin n, (a, b) ∈ E → (a, a) ∈ E ∧ (b, b) ∈ E) →
        (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        (u0, u0) ∈ E →
        (∃ a b : Fin n, a ≠ b ∧ (a, a) ∈ E' ∧ (b, b) ∈ E') →
        (∀ b : Fin n, (u0, b) ∈ E → b = u0) →
        N.Nonempty →
        (∀ a ∈ N, ∀ b ∈ N, (a, b) ∈ E ↔ a = b) →
        (∀ a ∈ N, ∀ b ∈ N, a ≠ b → ∀ c : Fin n, c ≠ u0 → ¬((a, c) ∈ E ∧ (b, c) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + n) C →
        comp E C →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 (n + n) D ∧ comp E' D ∧ D.size + N.card + (2 : ℕ) ≤ C.size) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x1) (x7 : Bool),   have x8 : Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : Finset (Fin x1 × Fin x1)) (x9 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x8 ∧ x10 (x3 x11) = Bool.true ∧ x10 (x4 x12) = Bool.true);   let x9 : Fin x1 → Fin x1 → Prop := fun (x9 x10 : Fin x1) => if x7 = Bool.true then (x10, x9) ∈ x2 else (x9, x10) ∈ x2;   have x10 : Finset (Fin x1) := {x10 : Fin x1 | x10 ≠ x6 ∧ x9 x10 x6};   have x11 : Finset (Fin x1 × Fin x1) := {x11 ∈ x2 | x11.1 ≠ x6 ∧ x11.2 ≠ x6};   (∀ (x12 x13 : Fin x1), x3 x12 ≠ x4 x13) → (∀ (x13 x14 : Fin x1), (x13, x14) ∈ x2 → (x13, x13) ∈ x2 ∧ (x14, x14) ∈ x2) → (∀ (x14 x15 x16 x17 : Fin x1), x14 ≠ x15 → x16 ≠ x17 → ¬((x14, x16) ∈ x2 ∧ (x14, x17) ∈ x2 ∧ (x15, x16) ∈ x2 ∧ (x15, x17) ∈ x2)) → (x6, x6) ∈ x2 → (∃ (x16 : Fin x1) (x17 : Fin x1), x16 ≠ x17 ∧ (x16, x16) ∈ x11 ∧ (x17, x17) ∈ x11) → (∀ (x17 : Fin x1), x9 x6 x17 → x17 = x6) → (∀ x18 ∈ x10, ∀ x20 ∈ x10, x9 x18 x20 ↔ x18 = x20) → (∀ x19 ∈ x10, ∀ x21 ∈ x10, x19 ≠ x21 → ∀ (x24 : Fin x1), x24 ≠ x6 → ¬(x9 x19 x24 ∧ x9 x21 x24)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x5 → x8 x2 x5 → ∃ (x22 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x22 ∧ x8 x11 x22 ∧ x22.size + x10.card + (2 : ℕ) ≤ x5.size := by
  classical
  intro n E fL fR C u0 x7 comp rel Norig Eorig hDisj hDiag hC4 hu0 hTwo hDeg1 hInd hDisjN hAO hFun
  have hn3 : (3 : ℕ) ≤ n := by
    obtain ⟨a, b, hab, ha, hb⟩ := hTwo
    have ha_ne : a ≠ u0 := (Finset.mem_filter.mp ha).2.1
    have hb_ne : b ≠ u0 := (Finset.mem_filter.mp hb).2.1
    have hsub : ({u0, a, b} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    have hc3 : ({u0, a, b} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]
        exact hab
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨ha_ne.symm, hb_ne.symm⟩
    omega
  have hSolve : ∀ (E1 : Finset (Fin n × Fin n)) (gL gR : Fin n ↪ Fin (n + n)),
      (∀ a b : Fin n, gL a ≠ gR b) →
      (∀ a b : Fin n, (a, b) ∈ E1 → (a, a) ∈ E1 ∧ (b, b) ∈ E1) →
      (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E1 ∧ (a, d) ∈ E1 ∧ (b, c) ∈ E1 ∧ (b, d) ∈ E1)) →
      (u0, u0) ∈ E1 →
      (∃ a b : Fin n, a ≠ b ∧ (a, a) ∈ (E1.filter fun e => e.1 ≠ u0 ∧ e.2 ≠ u0) ∧ (b, b) ∈ (E1.filter fun e => e.1 ≠ u0 ∧ e.2 ≠ u0)) →
      (∀ b : Fin n, (u0, b) ∈ E1 → b = u0) →
      (∀ a ∈ (E1.filter fun e => e.1 ≠ u0 ∧ e.2 = u0).image Prod.fst,
        ∀ b ∈ (E1.filter fun e => e.1 ≠ u0 ∧ e.2 = u0).image Prod.fst, (a, b) ∈ E1 ↔ a = b) →
      (∀ a ∈ (E1.filter fun e => e.1 ≠ u0 ∧ e.2 = u0).image Prod.fst,
        ∀ b ∈ (E1.filter fun e => e.1 ≠ u0 ∧ e.2 = u0).image Prod.fst,
        a ≠ b → ∀ c : Fin n, c ≠ u0 → ¬((a, c) ∈ E1 ∧ (b, c) ∈ E1)) →
      (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C x =
        Decidable.decide (∃ a b : Fin n, (a, b) ∈ E1 ∧ x (gL a) = Bool.true ∧ x (gR b) = Bool.true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (n + n) D ∧
        (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x =
          Decidable.decide (∃ a b : Fin n, (a, b) ∈ (E1.filter fun e => e.1 ≠ u0 ∧ e.2 ≠ u0) ∧ x (gL a) = Bool.true ∧ x (gR b) = Bool.true)) ∧
        D.size + ((E1.filter fun e => e.1 ≠ u0 ∧ e.2 = u0).image Prod.fst).card + (2 : ℕ) ≤ C.size := by
    intro E1 gL gR hD1 hDg1 hC41 hu01 hTwo1 hDeg11 hInd1 hDisjN1 hFun1
    let N1 : Finset (Fin n) := (E1.filter fun e => e.1 ≠ u0 ∧ e.2 = u0).image Prod.fst
    by_cases hNemp : N1 = ∅
    · have hIn0 : ∀ a : Fin n, (a, u0) ∈ E1 → a = u0 := by
        intro a ha
        by_contra hne
        have hmem : a ∈ N1 := Finset.mem_image.mpr ⟨(a, u0), Finset.mem_filter.mpr ⟨ha, hne, rfl⟩, rfl⟩
        rw [hNemp] at hmem
        exact Finset.notMem_empty a hmem
      obtain ⟨D, hDAO, hDfun, hDsz⟩ := hIsol n E1 gL gR C u0 hn3 hD1 hDg1 hC41 hu01 hTwo1 hDeg11 hIn0 hAO hFun1
      refine ⟨D, hDAO, hDfun, ?_⟩
      change D.size + N1.card + 2 ≤ C.size
      rw [hNemp, Finset.card_empty]
      omega
    · exact hNonemptyN n E1 gL gR C u0 hn3 hD1 hDg1 hC41 hu01 hTwo1 hDeg11
        (Finset.nonempty_iff_ne_empty.mpr hNemp) hInd1 hDisjN1 hAO hFun1
  by_cases hflag : x7 = Bool.true
  · let E1 : Finset (Fin n × Fin n) := E.image Prod.swap
    have hE1_mem : ∀ a b : Fin n, (a, b) ∈ E1 ↔ (b, a) ∈ E := by
      intro a b
      simp only [E1, Finset.mem_image]
      constructor
      · rintro ⟨⟨x, y⟩, hxy, heq⟩
        have h1 : y = a := (Prod.mk.inj heq).1
        have h2 : x = b := (Prod.mk.inj heq).2
        rw [← h1, ← h2]
        exact hxy
      · intro h
        exact ⟨(b, a), h, rfl⟩
    have hrel_iff : ∀ a b : Fin n, rel a b ↔ (a, b) ∈ E1 := by
      intro a b
      change (if x7 = Bool.true then (b, a) ∈ E else (a, b) ∈ E) ↔ (a, b) ∈ E1
      rw [if_pos hflag, hE1_mem]
    have hN_eq : (E1.filter fun e => e.1 ≠ u0 ∧ e.2 = u0).image Prod.fst = Norig := by
      ext a
      simp only [Finset.mem_image, Finset.mem_filter, Norig, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨x, y⟩, ⟨hxy, hne, hy⟩, rfl⟩
        dsimp only at hne hy ⊢
        rw [hy] at hxy
        exact ⟨hne, (hrel_iff x u0).mpr hxy⟩
      · rintro ⟨hne, hrel⟩
        exact ⟨(a, u0), ⟨(hrel_iff a u0).mp hrel, hne, rfl⟩, rfl⟩
    have hE'_eq : ∀ a b : Fin n, (a, b) ∈ (E1.filter fun e => e.1 ≠ u0 ∧ e.2 ≠ u0) ↔ (b, a) ∈ Eorig := by
      intro a b
      simp only [Finset.mem_filter, Eorig, hE1_mem]
      tauto
    have hFun1 : ∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C x =
        Decidable.decide (∃ a b : Fin n, (a, b) ∈ E1 ∧ x (fR a) = Bool.true ∧ x (fL b) = Bool.true) := by
      intro x
      rw [hFun x, Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        exact ⟨b, a, (hE1_mem b a).mpr hab, hb, ha⟩
      · rintro ⟨a, b, hab, ha, hb⟩
        exact ⟨b, a, (hE1_mem a b).mp hab, hb, ha⟩
    obtain ⟨D, hDAO, hDfun, hDsz⟩ := hSolve E1 fR fL
      (fun a b => (hDisj b a).symm)
      (fun a b h => let hh := hDiag b a ((hE1_mem a b).mp h); ⟨(hE1_mem a a).mpr hh.2, (hE1_mem b b).mpr hh.1⟩)
      (fun a b c d hab hcd h => hC4 c d a b hcd hab
        ⟨(hE1_mem a c).mp h.1, (hE1_mem b c).mp h.2.2.1, (hE1_mem a d).mp h.2.1, (hE1_mem b d).mp h.2.2.2⟩)
      ((hE1_mem u0 u0).mpr hu0)
      (by obtain ⟨a, b, hab, ha, hb⟩ := hTwo; exact ⟨a, b, hab, (hE'_eq a a).mpr ha, (hE'_eq b b).mpr hb⟩)
      (fun b hb => hDeg1 b ((hrel_iff u0 b).mpr hb))
      (fun a ha b hb => by
        rw [hN_eq] at ha hb
        simpa only [hrel_iff] using hInd a ha b hb)
      (fun a ha b hb hab c hc => by
        rw [hN_eq] at ha hb
        simpa only [hrel_iff] using hDisjN a ha b hb hab c hc)
      hFun1
    refine ⟨D, hDAO, ?_, ?_⟩
    · intro x
      rw [hDfun x, Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        exact ⟨b, a, (hE'_eq a b).mp hab, hb, ha⟩
      · rintro ⟨a, b, hab, ha, hb⟩
        exact ⟨b, a, (hE'_eq b a).mpr hab, hb, ha⟩
    · rwa [hN_eq] at hDsz
  · have hrel_iff : ∀ a b : Fin n, rel a b ↔ (a, b) ∈ E := by
      intro a b
      change (if x7 = Bool.true then (b, a) ∈ E else (a, b) ∈ E) ↔ (a, b) ∈ E
      rw [if_neg hflag]
    have hN_eq : (E.filter fun e => e.1 ≠ u0 ∧ e.2 = u0).image Prod.fst = Norig := by
      ext a
      simp only [Finset.mem_image, Finset.mem_filter, Norig, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨x, y⟩, ⟨hxy, hne, hy⟩, rfl⟩
        dsimp only at hne hy ⊢
        rw [hy] at hxy
        exact ⟨hne, (hrel_iff x u0).mpr hxy⟩
      · rintro ⟨hne, hrel⟩
        exact ⟨(a, u0), ⟨(hrel_iff a u0).mp hrel, hne, rfl⟩, rfl⟩
    obtain ⟨D, hDAO, hDfun, hDsz⟩ := hSolve E fL fR hDisj hDiag hC4 hu0 hTwo
      (fun b hb => hDeg1 b ((hrel_iff u0 b).mpr hb))
      (fun a ha b hb => by
        rw [hN_eq] at ha hb
        simpa only [hrel_iff] using hInd a ha b hb)
      (fun a ha b hb hab c hc => by
        rw [hN_eq] at ha hb
        simpa only [hrel_iff] using hDisjN a ha b hb hab c hc)
      hFun
    refine ⟨D, hDAO, hDfun, ?_⟩
    rwa [hN_eq] at hDsz
