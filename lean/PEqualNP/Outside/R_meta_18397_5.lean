import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18397_5
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
        PEqualNP.TopForm.IsAO2 (m' + n') D →
        (∀ x : Fin (m' + n') → Bool, PEqualNP.MetaComplexity.circuitFun (m' + n') D x =
          Decidable.decide (∃ p ∈ E', x (Fin.castAdd n' p.1) = Bool.true ∧ x (Fin.natAdd m' p.2) = Bool.true)) →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (m' + n') → Bool,
          (D.wires (List.ofFn x)).getD (m' + n' + i.val) Bool.false ≠
          (D.wires (List.ofFn x)).getD (m' + n' + j.val) Bool.false) →
        ∃ (L' : Finset (Fin m')) (R' : Finset (Fin n')),
          (∀ p ∈ E', p.1 ∈ L' ∨ p.2 ∈ R') ∧ E'.card + L'.card + R'.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro m n E C hc4 hAO hfun0 _hAnd
  have hfun : ∀ x : Fin (m + n) → Bool, PEqualNP.MetaComplexity.circuitFun (m + n) C x =
      Decidable.decide (∃ e ∈ E, x (Fin.castAdd n e.1) = Bool.true ∧ x (Fin.natAdd m e.2) = Bool.true) := by
    intro x
    rw [hfun0 x, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨(a, b), hab, ha, hb⟩
    · rintro ⟨⟨a, b⟩, hab, ha, hb⟩
      exact ⟨a, b, hab, ha, hb⟩
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
      (fun hEq => ha (hfL_inj hEq)) (fun hEq => hb (hfR_inj hEq))
      ⟨(hE'_mem (a, b)).mp h.1, (hE'_mem (a, b')).mp h.2.1,
       (hE'_mem (a', b)).mp h.2.2.1, (hE'_mem (a', b')).mp h.2.2.2⟩
  obtain ⟨D, hDsize, hDAO, hDfun, hDnodup, hDdist⟩ :=
    hRestrict m n m' n' fL fR E E' C hfL_inj hfR_inj hE'_ne hE'_mem hcover_f hAO hfun
  have hLift : ∀ (L' : Finset (Fin m')) (R' : Finset (Fin n')),
      (∀ p ∈ E', p.1 ∈ L' ∨ p.2 ∈ R') → E'.card + L'.card + R'.card ≤ D.size + (1 : ℕ) →
      ∃ (L : Finset (Fin m)) (R : Finset (Fin n)),
        (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ C.size + (1 : ℕ) := by
    intro L' R' hcov' hbd'
    refine ⟨L'.image fL, R'.image fR, ?_, ?_⟩
    · intro e he
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcover_f e he
      have hab : (a, b) ∈ E' := (hE'_mem (a, b)).mpr (by simpa only [ha, hb] using he)
      rcases hcov' (a, b) hab with hL | hR
      · left
        exact Finset.mem_image.mpr ⟨a, hL, ha⟩
      · right
        exact Finset.mem_image.mpr ⟨b, hR, hb⟩
    · rw [Finset.card_image_of_injective L' hfL_inj,
          Finset.card_image_of_injective R' hfR_inj, ← hE'_card]
      omega
  have hReachBound : ∀ (N : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs, i < N + j) →
      (∀ g ∈ gs, g.inputs.length ≤ 2) →
      ∀ (S : Finset ℕ), (∀ w ∈ S, w < N + gs.length) →
      ∃ R : Finset ℕ,
        (∀ w ∈ R, w < N) ∧
        R.card ≤ S.card + gs.length ∧
        ∀ (x y : List Bool), x.length = N → y.length = N →
          (∀ w ∈ R, x.getD w false = y.getD w false) →
          ∀ w ∈ S,
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD w false =
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD w false := by
    intro N gs
    refine List.reverseRecOn gs ?_ ?_
    · intro _ _ S hS
      refine ⟨S, by simpa using hS, by simp, ?_⟩
      intro x y _ _ hxy w hw
      simpa using hxy w hw
    · intro gs g ih hrb hlen S hS
      have hrb_gs : ∀ j < gs.length,
          ∀ i ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs, i < N + j := by
        intro j hj i hi
        have hlt : j < (gs ++ [g]).length := by simp; omega
        have hget : (gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ =
            gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
        rw [← hget] at hi
        exact hrb j hlt i hi
      have hrb_g : ∀ i ∈ g.inputs, i < N + gs.length := by
        intro i hi
        have hlt : gs.length < (gs ++ [g]).length := by simp
        have hget : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [← hget] at hi
        exact hrb gs.length hlt i hi
      have hlen_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' =>
        hlen g' (List.mem_append_left [g] hg')
      have hlen_g : g.inputs.length ≤ 2 := hlen g (List.mem_append_right gs (by simp))
      let S' : Finset ℕ :=
        if N + gs.length ∈ S then (S.erase (N + gs.length)) ∪ g.inputs.toFinset else S
      have hS'_lt : ∀ w ∈ S', w < N + gs.length := by
        intro w hw
        by_cases hmem : N + gs.length ∈ S
        · simp only [S', if_pos hmem, Finset.mem_union, Finset.mem_erase, List.mem_toFinset] at hw
          rcases hw with ⟨hne, hwS⟩ | hwg
          · have hlt := hS w hwS
            simp only [List.length_append, List.length_singleton] at hlt
            omega
          · exact hrb_g w hwg
        · simp only [S', if_neg hmem] at hw
          have hlt := hS w hw
          simp only [List.length_append, List.length_singleton] at hlt
          have hne : w ≠ N + gs.length := fun heq => hmem (heq ▸ hw)
          omega
      have hS'_card : S'.card ≤ S.card + 1 := by
        by_cases hmem : N + gs.length ∈ S
        · simp only [S', if_pos hmem]
          have h1 : ((S.erase (N + gs.length)) ∪ g.inputs.toFinset).card ≤
              (S.erase (N + gs.length)).card + g.inputs.toFinset.card := Finset.card_union_le _ _
          have h2 : (S.erase (N + gs.length)).card = S.card - 1 := Finset.card_erase_of_mem hmem
          have h3 : g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le g.inputs
          have h4 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨N + gs.length, hmem⟩
          omega
        · simp only [S', if_neg hmem]
          omega
      obtain ⟨R, hRlt, hRcard, hRagree⟩ := ih hrb_gs hlen_gs S' hS'_lt
      refine ⟨R, hRlt, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro x y hxlen hylen hxy w hw
        have hfold_len : ∀ (xs : List Bool) (hs : List PEqualNP.CircuitLowerBounds.Gate),
            (hs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length =
            xs.length + hs.length := by
          intro xs hs
          induction hs generalizing xs with
          | nil => simp
          | cons hd tl ihtl =>
            simp only [List.foldl_cons, List.length_cons]
            rw [ihtl]
            simp only [List.length_append, List.length_singleton]
            omega
        let wx := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
        let wy := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y
        have hwxlen : wx.length = N + gs.length := by
          simpa only [wx, hxlen] using hfold_len x gs
        have hwylen : wy.length = N + gs.length := by
          simpa only [wy, hylen] using hfold_len y gs
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        change (wx ++ [g.op.eval (g.inputs.map fun i => wx.getD i false)]).getD w false =
          (wy ++ [g.op.eval (g.inputs.map fun i => wy.getD i false)]).getD w false
        by_cases hweq : w = N + gs.length
        · subst hweq
          have hmap : (g.inputs.map fun i => wx.getD i false) = (g.inputs.map fun i => wy.getD i false) := by
            apply List.map_congr_left
            intro i hi
            have hiS' : i ∈ S' := by
              simp only [S', if_pos hw, Finset.mem_union, List.mem_toFinset]
              right
              exact hi
            exact hRagree x y hxlen hylen hxy i hiS'
          rw [hmap]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
          simp only [hwxlen, hwylen, Nat.sub_self]
        · have hwlt : w < N + gs.length := by
            have hlt := hS w hw
            simp only [List.length_append, List.length_singleton] at hlt
            omega
          have hwS' : w ∈ S' := by
            by_cases hmem : N + gs.length ∈ S
            · simp only [S', if_pos hmem, Finset.mem_union, Finset.mem_erase]
              left
              exact ⟨hweq, hw⟩
            · simp only [S', if_neg hmem]
              exact hw
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact hRagree x y hxlen hylen hxy w hwS'
  have hDout_lt : D.output < m' + n' + D.gates.length := by
    by_contra hge
    push Not at hge
    obtain ⟨⟨a0, b0⟩, hab0⟩ := hE'_ne
    let x1 : Fin (m' + n') → Bool := fun _ => true
    have h1 := hDfun x1
    have htrue : Decidable.decide (∃ p ∈ E', x1 (Fin.castAdd n' p.1) = Bool.true ∧ x1 (Fin.natAdd m' p.2) = Bool.true) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨(a0, b0), hab0, rfl, rfl⟩
    rw [htrue] at h1
    have hlen_w : (D.wires (List.ofFn x1)).length = m' + n' + D.gates.length := by
      have hfold_len : ∀ (xs : List Bool) (hs : List PEqualNP.CircuitLowerBounds.Gate),
          (hs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length =
          xs.length + hs.length := by
        intro xs hs
        induction hs generalizing xs with
        | nil => simp
        | cons hd tl ihtl =>
          simp only [List.foldl_cons, List.length_cons]
          rw [ihtl]
          simp only [List.length_append, List.length_singleton]
          omega
      exact (hfold_len (List.ofFn x1) D.gates).trans (by rw [List.length_ofFn])
    have hfalse : PEqualNP.MetaComplexity.circuitFun (m' + n') D x1 = false := by
      change (D.wires (List.ofFn x1)).getD D.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hfalse] at h1
    exact Bool.false_ne_true h1
  have hMN_le : m' + n' ≤ D.size + 1 := by
    have hrbD : ∀ j < D.gates.length,
        ∀ i ∈ (D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs, i < m' + n' + j := by
      intro j hj i hi
      have h := hDAO.2.1 j hj i
      have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt D j =
          D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ := by
        change D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
          D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      rw [hgate] at h
      exact h hi
    have hlenD : ∀ g ∈ D.gates, g.inputs.length ≤ 2 := fun g hg => le_of_eq (hDAO.2.2 g hg)
    obtain ⟨R, hRlt, hRcard, hRagree⟩ := hReachBound (m' + n') D.gates hrbD hlenD {D.output}
      (by intro w hw; simp only [Finset.mem_singleton] at hw; subst hw; exact hDout_lt)
    have hall : Finset.range (m' + n') ⊆ R := by
      intro w hw
      have hwlt : w < m' + n' := Finset.mem_range.mp hw
      by_contra hwR
      by_cases hleft : w < m'
      · let a : Fin m' := ⟨w, hleft⟩
        obtain ⟨b, hab⟩ := hdegL a
        let x : Fin (m' + n') → Bool := fun v => decide (v = Fin.natAdd m' b)
        let y : Fin (m' + n') → Bool := fun v => decide (v = Fin.castAdd n' a ∨ v = Fin.natAdd m' b)
        have hxy : ∀ u ∈ R, (List.ofFn x).getD u false = (List.ofFn y).getD u false := by
          intro u hu
          have hult := hRlt u hu
          have hune : u ≠ w := fun heq => hwR (heq ▸ hu)
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hult, Option.getD_some, x, y]
          have hne_a : (⟨u, hult⟩ : Fin (m' + n')) ≠ Fin.castAdd n' a := by
            intro heq
            exact hune (congrArg Fin.val heq)
          simp only [hne_a, false_or]
        have heq_out := hRagree (List.ofFn x) (List.ofFn y) (List.length_ofFn) (List.length_ofFn)
          hxy D.output (Finset.mem_singleton_self D.output)
        have hcf : PEqualNP.MetaComplexity.circuitFun (m' + n') D x =
            PEqualNP.MetaComplexity.circuitFun (m' + n') D y := heq_out
        rw [hDfun x, hDfun y] at hcf
        have hxF : Decidable.decide (∃ p ∈ E', x (Fin.castAdd n' p.1) = Bool.true ∧ x (Fin.natAdd m' p.2) = Bool.true) = false := by
          simp only [decide_eq_false_iff_not, not_exists, not_and]
          intro p _ hpx
          simp only [x, decide_eq_true_eq] at hpx
          have hv := congrArg Fin.val hpx
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        have hyT : Decidable.decide (∃ p ∈ E', y (Fin.castAdd n' p.1) = Bool.true ∧ y (Fin.natAdd m' p.2) = Bool.true) = true := by
          simp only [decide_eq_true_eq]
          exact ⟨(a, b), hab, by simp [y], by simp [y]⟩
        rw [hxF, hyT] at hcf
        exact Bool.false_ne_true hcf
      · let b : Fin n' := ⟨w - m', by omega⟩
        obtain ⟨a, hab⟩ := hdegR b
        let x : Fin (m' + n') → Bool := fun v => decide (v = Fin.castAdd n' a)
        let y : Fin (m' + n') → Bool := fun v => decide (v = Fin.castAdd n' a ∨ v = Fin.natAdd m' b)
        have hxy : ∀ u ∈ R, (List.ofFn x).getD u false = (List.ofFn y).getD u false := by
          intro u hu
          have hult := hRlt u hu
          have hune : u ≠ w := fun heq => hwR (heq ▸ hu)
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hult, Option.getD_some, x, y]
          have hne_b : (⟨u, hult⟩ : Fin (m' + n')) ≠ Fin.natAdd m' b := by
            intro heq
            have hv := congrArg Fin.val heq
            simp only [Fin.val_natAdd, b] at hv
            omega
          simp only [hne_b, or_false]
        have heq_out := hRagree (List.ofFn x) (List.ofFn y) (List.length_ofFn) (List.length_ofFn)
          hxy D.output (Finset.mem_singleton_self D.output)
        have hcf : PEqualNP.MetaComplexity.circuitFun (m' + n') D x =
            PEqualNP.MetaComplexity.circuitFun (m' + n') D y := heq_out
        rw [hDfun x, hDfun y] at hcf
        have hxF : Decidable.decide (∃ p ∈ E', x (Fin.castAdd n' p.1) = Bool.true ∧ x (Fin.natAdd m' p.2) = Bool.true) = false := by
          simp only [decide_eq_false_iff_not, not_exists, not_and]
          intro p _ _ hpx
          simp only [x, decide_eq_true_eq] at hpx
          have hv := congrArg Fin.val hpx
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        have hyT : Decidable.decide (∃ p ∈ E', y (Fin.castAdd n' p.1) = Bool.true ∧ y (Fin.natAdd m' p.2) = Bool.true) = true := by
          simp only [decide_eq_true_eq]
          exact ⟨(a, b), hab, by simp [y], by simp [y]⟩
        rw [hxF, hyT] at hcf
        exact Bool.false_ne_true hcf
    have hcard_le := Finset.card_le_card hall
    rw [Finset.card_range] at hcard_le
    simp only [Finset.card_singleton] at hRcard
    change m' + n' ≤ D.gates.length + 1
    omega
  have hm'_pos : 0 < m' := by
    obtain ⟨p, _⟩ := hE'_ne
    exact Nat.pos_of_ne_zero (fun h => Fin.elim0 (h ▸ p.1))
  have hn'_pos : 0 < n' := by
    obtain ⟨p, _⟩ := hE'_ne
    exact Nat.pos_of_ne_zero (fun h => Fin.elim0 (h ▸ p.2))
  by_cases hm1 : m' ≤ 1
  · have hm'_eq : m' = 1 := by omega
    have hE'le : E'.card ≤ n' := by
      have h1 : E'.card ≤ (Finset.univ : Finset (Fin m' × Fin n')).card := Finset.card_le_univ E'
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
      have hmul : m' * n' = n' := by rw [hm'_eq, one_mul]
      omega
    apply hLift Finset.univ ∅
    · intro p _
      left
      exact Finset.mem_univ p.1
    · simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty]
      omega
  by_cases hn1 : n' ≤ 1
  · have hn'_eq : n' = 1 := by omega
    have hE'le : E'.card ≤ m' := by
      have h1 : E'.card ≤ (Finset.univ : Finset (Fin m' × Fin n')).card := Finset.card_le_univ E'
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
      have hmul : m' * n' = m' := by rw [hn'_eq, mul_one]
      omega
    apply hLift ∅ Finset.univ
    · intro p _
      right
      exact Finset.mem_univ p.2
    · simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty]
      omega
  by_cases hE2 : E'.card ≤ 2
  · have hm'_le_E : m' ≤ E'.card := by
      have hsub : (Finset.univ : Finset (Fin m')) ⊆ E'.image Prod.fst := by
        intro a _
        obtain ⟨b, hab⟩ := hdegL a
        exact Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩
      have h1 := Finset.card_le_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      exact le_trans h1 Finset.card_image_le
    have hn'_le_E : n' ≤ E'.card := by
      have hsub : (Finset.univ : Finset (Fin n')) ⊆ E'.image Prod.snd := by
        intro b _
        obtain ⟨a, hab⟩ := hdegR b
        exact Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩
      have h1 := Finset.card_le_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      exact le_trans h1 Finset.card_image_le
    apply hLift Finset.univ ∅
    · intro p _
      left
      exact Finset.mem_univ p.1
    · simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty]
      omega
  obtain ⟨L', R', hcov', hbd'⟩ := hCore m' n' E' D (by omega) (by omega) (by omega)
    hdegL hdegR hc4' hDAO hDfun hDnodup hDdist
  exact hLift L' R' hcov' hbd'
