import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8501_5
    (hRestrict :
      ∀ (N k : ℕ) (gL gR : Fin k → Fin N)
        (E' : Finset (Fin k × Fin k)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        Function.Injective gL →
        Function.Injective gR →
        (∀ a b : Fin k, gL a ≠ gR b) →
        E'.Nonempty →
        PEqualNP.TopForm.IsAO2 N C →
        (∀ x : Fin N → Bool, PEqualNP.MetaComplexity.circuitFun N C x =
          Decidable.decide (∃ a b : Fin k, (a, b) ∈ E' ∧ x (gL a) = Bool.true ∧ x (gR b) = Bool.true)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ C.size ∧
          PEqualNP.TopForm.IsAO2 (k + k) D ∧
          (∀ x : Fin (k + k) → Bool, PEqualNP.MetaComplexity.circuitFun (k + k) D x =
            Decidable.decide (∃ a b : Fin k, (a, b) ∈ E' ∧ x (Fin.castAdd k a) = Bool.true ∧ x (Fin.natAdd k b) = Bool.true)) ∧
          (∀ g ∈ D.gates, g.inputs.Nodup) ∧
          (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (k + k) → Bool,
            PEqualNP.EdgeOwnership.gateVal (k + k) D i.val x ≠
            PEqualNP.EdgeOwnership.gateVal (k + k) D j.val x))
    (hCover :
      ∀ (k : ℕ) (E' : Finset (Fin k × Fin k)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        (3 : ℕ) ≤ k →
        (∀ u : Fin k, (u, u) ∈ E') →
        (∀ u : Fin k, (∃ v : Fin k, v ≠ u ∧ (u, v) ∈ E') ∧ (∃ v : Fin k, v ≠ u ∧ (v, u) ∈ E')) →
        (∀ a b c d : Fin k, a ≠ b → c ≠ d → ¬((a, c) ∈ E' ∧ (a, d) ∈ E' ∧ (b, c) ∈ E' ∧ (b, d) ∈ E')) →
        PEqualNP.TopForm.IsAO2 (k + k) D →
        (∀ x : Fin (k + k) → Bool, PEqualNP.MetaComplexity.circuitFun (k + k) D x =
          Decidable.decide (∃ a b : Fin k, (a, b) ∈ E' ∧ x (Fin.castAdd k a) = Bool.true ∧ x (Fin.natAdd k b) = Bool.true)) →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (k + k) → Bool,
          PEqualNP.EdgeOwnership.gateVal (k + k) D i.val x ≠
          PEqualNP.EdgeOwnership.gateVal (k + k) D j.val x) →
        ∃ (L R : Finset (Fin k)), (∀ e ∈ E', e.1 ∈ L ∨ e.2 ∈ R) ∧ E'.card + L.card + R.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x1)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x7 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x6 ∧ x8 (x3 x9) = Bool.true ∧ x8 (x4 x10) = Bool.true);   (∀ (x7 x8 : Fin x1), x3 x7 ≠ x4 x8) →     (∀ (x8 x9 : Fin x1), (x8, x9) ∈ x2 → (x8, x8) ∈ x2 ∧ (x9, x9) ∈ x2) →       (∀ (x9 x10 x11 x12 : Fin x1), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x2 ∧ (x9, x12) ∈ x2 ∧ (x10, x11) ∈ x2 ∧ (x10, x12) ∈ x2)) →         have x10 : Finset (Fin x1) := {x10 : Fin x1 | (x10, x10) ∈ x2};         (3 : ℕ) ≤ x10.card → x10.card < x1 → (2 : ℕ) * x10.card ≤ x2.card → (∀ (x14 : Fin x1), (x14, x14) ∈ x2 → (∃ (x16 : Fin x1), x16 ≠ x14 ∧ (x14, x16) ∈ x2) ∧ ∃ (x16 : Fin x1), x16 ≠ x14 ∧ (x16, x14) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x5 → x6 x2 x5 → x2.card + x10.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n E fL0 fR0 C _hfunDef hDisj hDiagSub hC4 diag hGe3 _hLt _h2k hDeg2 hAO hFun
  let k : ℕ := diag.card
  let eD : ↥diag ≃ Fin k := diag.equivFin
  let emb : Fin k → Fin n := fun a => (eD.symm a).1
  have hemb_inj : Function.Injective emb := by
    intro a1 a2 h
    exact eD.symm.injective (Subtype.ext h)
  have hemb_mem : ∀ a : Fin k, (emb a, emb a) ∈ E := by
    intro a
    exact (Finset.mem_filter.mp (eD.symm a).2).2
  let gL : Fin k → Fin (n + n) := fun a => fL0 (emb a)
  let gR : Fin k → Fin (n + n) := fun b => fR0 (emb b)
  have hgL_inj : Function.Injective gL := fL0.injective.comp hemb_inj
  have hgR_inj : Function.Injective gR := fR0.injective.comp hemb_inj
  have hgDisj : ∀ a b : Fin k, gL a ≠ gR b := fun a b => hDisj (emb a) (emb b)
  let φ : Fin k × Fin k → Fin n × Fin n := fun p => (emb p.1, emb p.2)
  have hφ_inj : Function.Injective φ := by
    intro p1 p2 h
    exact Prod.ext (hemb_inj (Prod.mk.inj h).1) (hemb_inj (Prod.mk.inj h).2)
  let E' : Finset (Fin k × Fin k) := Finset.univ.filter fun p => φ p ∈ E
  have hE'_mem : ∀ a b : Fin k, (a, b) ∈ E' ↔ (emb a, emb b) ∈ E := by
    intro a b
    simp only [E', φ, Finset.mem_filter, Finset.mem_univ, true_and]
  have hE'_img : E'.image φ = E := by
    ext ⟨u, v⟩
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨⟨a, b⟩, hab, heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact (hE'_mem a b).mp hab
    · intro huv
      have huD : u ∈ diag := Finset.mem_filter.mpr ⟨Finset.mem_univ u, (hDiagSub u v huv).1⟩
      have hvD : v ∈ diag := Finset.mem_filter.mpr ⟨Finset.mem_univ v, (hDiagSub u v huv).2⟩
      let a : Fin k := eD ⟨u, huD⟩
      let b : Fin k := eD ⟨v, hvD⟩
      have ha : emb a = u := by simp only [emb, a, Equiv.symm_apply_apply]
      have hb : emb b = v := by simp only [emb, b, Equiv.symm_apply_apply]
      refine ⟨(a, b), (hE'_mem a b).mpr (by rw [ha, hb]; exact huv), Prod.ext ha hb⟩
  have hE'_card : E'.card = E.card := by
    rw [← hE'_img]
    exact (Finset.card_image_of_injective E' hφ_inj).symm
  have hmatch' : ∀ u : Fin k, (u, u) ∈ E' := fun u => (hE'_mem u u).mpr (hemb_mem u)
  have hE'_ne : E'.Nonempty := by
    let u0 : Fin k := ⟨0, by omega⟩
    exact ⟨(u0, u0), hmatch' u0⟩
  have hDeg2' : ∀ u : Fin k, (∃ v : Fin k, v ≠ u ∧ (u, v) ∈ E') ∧ (∃ v : Fin k, v ≠ u ∧ (v, u) ∈ E') := by
    intro u
    obtain ⟨⟨v1, hv1ne, hv1e⟩, ⟨v2, hv2ne, hv2e⟩⟩ := hDeg2 (emb u) (hemb_mem u)
    have hv1D : v1 ∈ diag := Finset.mem_filter.mpr ⟨Finset.mem_univ v1, (hDiagSub _ _ hv1e).2⟩
    have hv2D : v2 ∈ diag := Finset.mem_filter.mpr ⟨Finset.mem_univ v2, (hDiagSub _ _ hv2e).1⟩
    let w1 : Fin k := eD ⟨v1, hv1D⟩
    let w2 : Fin k := eD ⟨v2, hv2D⟩
    have hw1 : emb w1 = v1 := by simp only [emb, w1, Equiv.symm_apply_apply]
    have hw2 : emb w2 = v2 := by simp only [emb, w2, Equiv.symm_apply_apply]
    refine ⟨⟨w1, fun heq => hv1ne (hw1.symm.trans (congrArg emb heq)), (hE'_mem u w1).mpr (by rw [hw1]; exact hv1e)⟩,
            ⟨w2, fun heq => hv2ne (hw2.symm.trans (congrArg emb heq)), (hE'_mem w2 u).mpr (by rw [hw2]; exact hv2e)⟩⟩
  have hc4' : ∀ a b c d : Fin k, a ≠ b → c ≠ d →
      ¬((a, c) ∈ E' ∧ (a, d) ∈ E' ∧ (b, c) ∈ E' ∧ (b, d) ∈ E') := by
    intro a b c d hab hcd h
    exact hC4 (emb a) (emb b) (emb c) (emb d)
      (fun h' => hab (hemb_inj h')) (fun h' => hcd (hemb_inj h'))
      ⟨(hE'_mem _ _).mp h.1, (hE'_mem _ _).mp h.2.1, (hE'_mem _ _).mp h.2.2.1, (hE'_mem _ _).mp h.2.2.2⟩
  have hFun' : ∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C x =
      Decidable.decide (∃ a b : Fin k, (a, b) ∈ E' ∧ x (gL a) = Bool.true ∧ x (gR b) = Bool.true) := by
    intro x
    rw [hFun x, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      have huD : u ∈ diag := Finset.mem_filter.mpr ⟨Finset.mem_univ u, (hDiagSub u v huv).1⟩
      have hvD : v ∈ diag := Finset.mem_filter.mpr ⟨Finset.mem_univ v, (hDiagSub u v huv).2⟩
      let a : Fin k := eD ⟨u, huD⟩
      let b : Fin k := eD ⟨v, hvD⟩
      have ha : emb a = u := by simp only [emb, a, Equiv.symm_apply_apply]
      have hb : emb b = v := by simp only [emb, b, Equiv.symm_apply_apply]
      exact ⟨a, b, (hE'_mem a b).mpr (by rw [ha, hb]; exact huv), by simpa only [gL, ha] using hu, by simpa only [gR, hb] using hv⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨emb a, emb b, (hE'_mem a b).mp hab, ha, hb⟩
  obtain ⟨D, hDle, hDAO, hDfun, hDnd, hDdist⟩ :=
    hRestrict (n + n) k gL gR E' C hgL_inj hgR_inj hgDisj hE'_ne hAO hFun'
  obtain ⟨L, R, hCov, hBd⟩ := hCover k E' D hGe3 hmatch' hDeg2' hc4' hDAO hDfun hDnd hDdist
  have hKonig : k ≤ L.card + R.card := by
    have hsub : (Finset.univ : Finset (Fin k)) ⊆ L ∪ R := by
      intro u _
      exact Finset.mem_union.mpr (hCov (u, u) (hmatch' u))
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact le_trans h1 (Finset.card_union_le L R)
  change E.card + k ≤ C.size + (1 : ℕ)
  omega
