import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4678_41
    (h_one :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]);
      have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]];
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ x5, PEqualNP.TopForm.IsAO2 (27 : ℕ) x6 → PEqualNP.TopForm.andPairs (27 : ℕ) x6 = (1 : ℕ) → x3 x6 x7 → (63 : ℕ) ≤ x6.size)
    (h_ge_two :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]);
      have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]];
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ x5, PEqualNP.TopForm.IsAO2 (27 : ℕ) x6 → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x6 → x3 x6 x7 → (63 : ℕ) ≤ x6.size) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → (63 : ℕ) ≤ x6.size) := by
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let inD : Fin 13 → Bool := fun x => x == 0 || x == 1 || x == 3 || x == 9
  let incPG : Fin 13 → Fin 13 → Bool := fun p l => inD (p - l)
  let adj : Fin 26 → Fin 26 → Bool := fun u v =>
    if hu : u.val < 13 then
      if hv : 13 ≤ v.val then incPG ⟨u.val, hu⟩ ⟨v.val - 13, by omega⟩ else false
    else
      if hv : v.val < 13 then incPG ⟨v.val, hv⟩ ⟨u.val - 13, by omega⟩ else false
  let isQuadL : List (Fin 13) → Bool := fun xs =>
    decide (xs.length = 4 ∧ xs.Nodup ∧ (List.finRange 13).all (fun l => (xs.countP fun p => inD (p - l)) ≤ 2))
  let qPPL : Fin 13 → List (Fin 13) := fun d =>
    if d = 3 then [0, 2, 3, 4]
    else if d = 4 then [0, 1, 4, 6]
    else if d = 6 then [0, 1, 2, 6]
    else if d = 7 then [0, 1, 2, 7]
    else if d = 8 then [0, 1, 4, 8]
    else if d = 9 then [0, 2, 4, 9]
    else if d = 10 then [0, 1, 5, 10]
    else if d = 11 then [0, 1, 2, 11]
    else if d = 12 then [0, 1, 4, 12]
    else [0, 1, 2, 5]
  let qLLL : Fin 13 → List (Fin 13) := fun d =>
    if d = 1 then [5, 6, 7, 11]
    else if d = 2 then [4, 6, 7, 8]
    else if d = 3 then [2, 5, 7, 8]
    else if d = 4 then [2, 6, 8, 10]
    else if d = 5 then [2, 4, 7, 11]
    else if d = 6 then [4, 5, 8, 10]
    else if d = 8 then [2, 5, 6, 10]
    else if d = 9 then [2, 4, 6, 8]
    else if d = 10 then [2, 4, 5, 8]
    else if d = 12 then [4, 5, 6, 10]
    else [2, 4, 5, 6]
  let qPLL : Fin 13 → List (Fin 13) := fun d =>
    if d = 1 then [0, 3, 5, 6]
    else if d = 2 then [0, 1, 4, 6]
    else if d = 5 then [0, 2, 3, 4]
    else if d = 6 then [0, 1, 4, 8]
    else if d = 9 then [0, 1, 2, 6]
    else if d = 11 then [0, 2, 3, 4]
    else [0, 1, 2, 5]
  let masks : List (List ℕ) :=
    [[], [0], [13], [0, 1], [0, 2], [0, 13], [0, 14], [0, 15], [0, 17], [0, 20], [13, 14], [13, 15]]
  let maskSet : List ℕ → Finset (Fin 26) := fun ms =>
    Finset.univ.filter fun u : Fin 26 => u.val ∈ ms
  have hInD : ∀ x : Fin 13, x ∈ D ↔ inD x = true := by decide +kernel
  have hAdj013 : adj 0 13 = true := by decide +kernel
  have hAdjSymm : ∀ u v : Fin 26, adj u v = adj v u := by decide +kernel
  have hAdjIrrefl : ∀ u : Fin 26, adj u u = false := by decide +kernel
  have hDeg4 : ∀ u : Fin 26, (Finset.univ.filter fun v : Fin 26 => adj u v = true).card = 4 := by
    decide +kernel
  have hCommonPt : ∀ p1 p2 : Fin 13, p1 ≠ p2 →
      (Finset.univ.filter fun l : Fin 13 => incPG p1 l = true ∧ incPG p2 l = true).card ≤ 1 := by
    decide +kernel
  have hCommonLn : ∀ l1 l2 : Fin 13, l1 ≠ l2 →
      (Finset.univ.filter fun p : Fin 13 => incPG p l1 = true ∧ incPG p l2 = true).card ≤ 1 := by
    decide +kernel
  have hEdgeCard : ((Finset.univ : Finset (Fin 26 × Fin 26)).filter
      fun p => p.1 < p.2 ∧ adj p.1 p.2 = true).card = 52 := by decide +kernel
  have hQPPL : ∀ d : Fin 13, isQuadL (qPPL d) = true ∧ (0 : Fin 13) ∈ qPPL d ∧ d ∈ qPPL d := by
    decide +kernel
  have hQLLL : ∀ d : Fin 13, isQuadL (qLLL d) = true ∧
      (∀ r ∈ qLLL d, inD (r - (0 : Fin 13)) = false) ∧ (∀ r ∈ qLLL d, inD (r - d) = false) := by
    decide +kernel
  have hQPLL : ∀ d : Fin 13, inD ((0 : Fin 13) - d) = false →
      isQuadL (qPLL d) = true ∧ (0 : Fin 13) ∈ qPLL d ∧ (∀ r ∈ qPLL d, inD (r - d) = false) := by
    decide +kernel
  have hMasksLt : ∀ ms ∈ masks, ∀ a ∈ ms, a < 26 := by decide +kernel
  have hMasksLen : ∀ ms ∈ masks, ms.length ≤ 2 := by decide +kernel
  let fitFn : (List Bool → Bool) → Prop := fun f =>
    (∀ (x3 x4 : Fin 13), x3 - x4 ∈ D →
      f ((List.ofFn fun x6 : Fin 13 => Decidable.decide (x6 = x3)) ++
         List.ofFn fun x6 : Fin 13 => Decidable.decide (x6 = x4)) = true) ∧
    ∀ (x3 : Finset (Fin 13)), x3.card = 4 →
      (∀ (x5 : Fin 13), {x6 ∈ x3 | x6 - x5 ∈ D}.card ≤ 2) →
      f ((List.ofFn fun x6 : Fin 13 => Decidable.decide (x6 ∈ x3)) ++
         List.ofFn fun x6 : Fin 13 => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ D)) = false
  let fitC : Circuit → List ℕ → Prop := fun C ms =>
    fitFn fun xs => C.eval (xs ++ [ms.any fun i => xs.getD i false])
  classical
  let qPP : Fin 13 → Finset (Fin 13) := fun d => (qPPL d).toFinset
  let qLL : Fin 13 → Finset (Fin 13) := fun d => (qLLL d).toFinset
  let qPL : Fin 13 → Finset (Fin 13) := fun d => (qPLL d).toFinset
  have hQuadL : ∀ xs : List (Fin 13), isQuadL xs = true →
      xs.toFinset.card = 4 ∧ ∀ l : Fin 13, (xs.toFinset.filter fun p => p - l ∈ D).card ≤ 2 := by
    intro xs hq
    obtain ⟨hlen, hnd, hall⟩ := of_decide_eq_true hq
    refine ⟨by rw [List.toFinset_card_of_nodup hnd, hlen], ?_⟩
    intro l
    have hcnt := of_decide_eq_true (List.all_eq_true.mp hall l (List.mem_finRange l))
    have hSub : xs.toFinset.filter (fun p => p - l ∈ D) ⊆ (xs.filter fun p => inD (p - l)).toFinset := by
      intro p hp
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter] at hp ⊢
      exact ⟨hp.1, (hInD (p - l)).mp hp.2⟩
    calc (xs.toFinset.filter fun p => p - l ∈ D).card
        ≤ (xs.filter fun p => inD (p - l)).toFinset.card := Finset.card_le_card hSub
      _ ≤ (xs.filter fun p => inD (p - l)).length := List.toFinset_card_le _
      _ = xs.countP (fun p => inD (p - l)) := (List.countP_eq_length_filter ..).symm
      _ ≤ 2 := hcnt
  have hNoC4 : ∀ u1 u2 v1 v2 : Fin 26, u1 ≠ u2 → v1 ≠ v2 →
      adj u1 v1 = true → adj u1 v2 = true → adj u2 v1 = true → adj u2 v2 = true → False := by
    intro u1 u2 v1 v2 hune hvne h11 h12 h21 h22
    by_cases hu1 : u1.val < 13
    · have hv1 : 13 ≤ v1.val := by
        by_contra hlt
        have : adj u1 v1 = false := by dsimp only [adj]; rw [dif_pos hu1, dif_neg hlt]
        rw [this] at h11; exact Bool.false_ne_true h11
      have hv2 : 13 ≤ v2.val := by
        by_contra hlt
        have : adj u1 v2 = false := by dsimp only [adj]; rw [dif_pos hu1, dif_neg hlt]
        rw [this] at h12; exact Bool.false_ne_true h12
      have hu2 : u2.val < 13 := by
        by_contra hge
        have : adj u2 v1 = false := by dsimp only [adj]; rw [dif_neg hge, dif_neg (by omega)]
        rw [this] at h21; exact Bool.false_ne_true h21
      let p1 : Fin 13 := ⟨u1.val, hu1⟩
      let p2 : Fin 13 := ⟨u2.val, hu2⟩
      let l1 : Fin 13 := ⟨v1.val - 13, by omega⟩
      let l2 : Fin 13 := ⟨v2.val - 13, by omega⟩
      have hpne : p1 ≠ p2 := fun h => hune (Fin.ext (by have := congrArg Fin.val h; exact this))
      have hlne : l1 ≠ l2 := fun h => hvne (Fin.ext (by have := congrArg Fin.val h; dsimp [l1, l2] at this; omega))
      have hi11 : incPG p1 l1 = true := by dsimp only [adj] at h11; rw [dif_pos hu1, dif_pos hv1] at h11; exact h11
      have hi12 : incPG p1 l2 = true := by dsimp only [adj] at h12; rw [dif_pos hu1, dif_pos hv2] at h12; exact h12
      have hi21 : incPG p2 l1 = true := by dsimp only [adj] at h21; rw [dif_pos hu2, dif_pos hv1] at h21; exact h21
      have hi22 : incPG p2 l2 = true := by dsimp only [adj] at h22; rw [dif_pos hu2, dif_pos hv2] at h22; exact h22
      have hsub : ({l1, l2} : Finset (Fin 13)) ⊆
          Finset.univ.filter fun l : Fin 13 => incPG p1 l = true ∧ incPG p2 l = true := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases Finset.mem_insert.mp hl with rfl | hl2
        · exact ⟨hi11, hi21⟩
        · rw [Finset.mem_singleton.mp hl2]; exact ⟨hi12, hi22⟩
      have hc2 : ({l1, l2} : Finset (Fin 13)).card = 2 := Finset.card_pair hlne
      have hle := Finset.card_le_card hsub
      have h1 := hCommonPt p1 p2 hpne
      omega
    · have hv1 : v1.val < 13 := by
        by_contra hge
        have : adj u1 v1 = false := by dsimp only [adj]; rw [dif_neg hu1, dif_neg hge]
        rw [this] at h11; exact Bool.false_ne_true h11
      have hv2 : v2.val < 13 := by
        by_contra hge
        have : adj u1 v2 = false := by dsimp only [adj]; rw [dif_neg hu1, dif_neg hge]
        rw [this] at h12; exact Bool.false_ne_true h12
      have hu2 : ¬ u2.val < 13 := by
        intro hlt
        have : adj u2 v1 = false := by dsimp only [adj]; rw [dif_pos hlt, dif_neg (by omega)]
        rw [this] at h21; exact Bool.false_ne_true h21
      let l1 : Fin 13 := ⟨u1.val - 13, by omega⟩
      let l2 : Fin 13 := ⟨u2.val - 13, by omega⟩
      let p1 : Fin 13 := ⟨v1.val, hv1⟩
      let p2 : Fin 13 := ⟨v2.val, hv2⟩
      have hlne : l1 ≠ l2 := fun h => hune (Fin.ext (by have := congrArg Fin.val h; dsimp [l1, l2] at this; omega))
      have hpne : p1 ≠ p2 := fun h => hvne (Fin.ext (by have := congrArg Fin.val h; exact this))
      have hi11 : incPG p1 l1 = true := by dsimp only [adj] at h11; rw [dif_neg hu1, dif_pos hv1] at h11; exact h11
      have hi12 : incPG p2 l1 = true := by dsimp only [adj] at h12; rw [dif_neg hu1, dif_pos hv2] at h12; exact h12
      have hi21 : incPG p1 l2 = true := by dsimp only [adj] at h21; rw [dif_neg hu2, dif_pos hv1] at h21; exact h21
      have hi22 : incPG p2 l2 = true := by dsimp only [adj] at h22; rw [dif_neg hu2, dif_pos hv2] at h22; exact h22
      have hsub : ({p1, p2} : Finset (Fin 13)) ⊆
          Finset.univ.filter fun p : Fin 13 => incPG p l1 = true ∧ incPG p l2 = true := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases Finset.mem_insert.mp hp with rfl | hp2
        · exact ⟨hi11, hi21⟩
        · rw [Finset.mem_singleton.mp hp2]; exact ⟨hi12, hi22⟩
      have hc2 : ({p1, p2} : Finset (Fin 13)).card = 2 := Finset.card_pair hpne
      have hle := Finset.card_le_card hsub
      have h1 := hCommonLn l1 l2 hlne
      omega
  have hShiftQuad : ∀ (s : Fin 13) (xs : List (Fin 13)), isQuadL xs = true →
      (xs.toFinset.image (· + s)).card = 4 ∧
      (∀ l : Fin 13, ((xs.toFinset.image (· + s)).filter fun p => p - l ∈ D).card ≤ 2) := by
    intro s xs hQ
    obtain ⟨hQ1, hQ2⟩ := hQuadL xs hQ
    have hinj : Function.Injective (fun p : Fin 13 => p + s) := fun a b h => add_right_cancel h
    refine ⟨by rw [Finset.card_image_of_injective _ hinj]; exact hQ1, ?_⟩
    intro l
    have hEq : (xs.toFinset.image (· + s)).filter (fun p => p - l ∈ D) =
        (xs.toFinset.filter (fun p => p - (l - s) ∈ D)).image (· + s) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hmem⟩
        exact ⟨p, ⟨hp, by rwa [show p - (l - s) = (p + s) - l by abel]⟩, rfl⟩
      · rintro ⟨p, ⟨hp, hmem⟩, rfl⟩
        exact ⟨⟨p, hp, rfl⟩, by rwa [show (p + s) - l = p - (l - s) by abel]⟩
    rw [hEq, Finset.card_image_of_injective _ hinj]
    exact hQ2 (l - s)
  dsimp only
  intro C0 mask hMask hM0 hRB0' hFit0
  have hMaskLt : ∀ a ∈ mask, a < 26 := hMasksLt mask hMask
  have hMaskCard : (maskSet mask).card ≤ 2 := by
    have hSub : (maskSet mask).image Fin.val ⊆ mask.toFinset := by
      intro a ha
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp hu).2
    calc (maskSet mask).card = ((maskSet mask).image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ mask.toFinset.card := Finset.card_le_card hSub
      _ ≤ mask.length := List.toFinset_card_le _
      _ ≤ 2 := hMasksLen mask hMask
  let inpL : List Bool → List Bool := fun xs => xs ++ [mask.any fun i => xs.getD i false]
  let inp : (Fin 26 → Bool) → List Bool := fun x => inpL (List.ofFn x)
  have hInpLen : ∀ x : Fin 26 → Bool, (inp x).length = 27 := by
    intro x; simp [inp, inpL]
  have hInpGet : ∀ (x : Fin 26 → Bool) (u : Fin 26), (inp x).getD u.val false = x u := by
    intro x u
    dsimp only [inp, inpL]
    rw [List.getD_append _ _ false u.val (by rw [List.length_ofFn]; exact u.isLt)]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact u.isLt), List.getElem_ofFn]
  have hInp26 : ∀ x : Fin 26 → Bool,
      (inp x).getD 26 false = decide (∃ u ∈ maskSet mask, x u = true) := by
    intro x
    dsimp only [inp, inpL]
    rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn])]
    rw [List.length_ofFn, Nat.sub_self]
    change (mask.any fun i => (List.ofFn x).getD i false) = _
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, decide_eq_true_eq, maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, hxt⟩
      have hiLt : i < 26 := hMaskLt i hi
      refine ⟨⟨i, hiLt⟩, hi, ?_⟩
      rwa [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hiLt), List.getElem_ofFn] at hxt
    · rintro ⟨u, hu, hxu⟩
      refine ⟨u.val, hu, ?_⟩
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact u.isLt), List.getElem_ofFn]
      exact hxu
  let stepW : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wF : List Gate → List Bool → List Bool := fun gs w => gs.foldl stepW w
  have hEvalAnd : ∀ ls : List Bool, GateOp.and.eval ls = ls.all id := fun _ => rfl
  have hEvalOr : ∀ ls : List Bool, GateOp.or.eval ls = ls.any id := fun _ => rfl
  have hGateAt : ∀ (C : Circuit) (j : ℕ), gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := fun _ _ => rfl
  have hGateAtEq : ∀ (C : Circuit) (j : ℕ) (hj : j < C.gates.length), gateAt C j = C.gates[j] := by
    intro C j hj
    rw [hGateAt, List.getD_eq_getElem C.gates _ hj]
  have hLenWF : ∀ (gs : List Gate) (w : List Bool), (wF gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [wF]
    | cons g gs ih =>
      intro w
      change (wF gs (stepW w g)).length = w.length + (gs.length + 1)
      rw [ih]; simp [stepW]; omega
  have hWFAppend : ∀ (gs1 gs2 : List Gate) (w : List Bool),
      wF (gs1 ++ gs2) w = wF gs2 (wF gs1 w) := fun _ _ _ => List.foldl_append
  have hWFLt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (wF gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      change (wF gs (stepW w g)).getD i false = w.getD i false
      rw [ih (stepW w g) i (by simp [stepW]; omega)]
      exact List.getD_append w _ false i hi
  have hMonoOps : ∀ (C : Circuit), Monotone2 C →
      ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro C hM g hg
    rcases (hM g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hMonoWF : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i < w1.length, w1.getD i false = true → w2.getD i false = true) →
      ∀ i < (wF gs w1).length, (wF gs w1).getD i false = true → (wF gs w2).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro _ w1 w2 _ hrel i hi h1; exact hrel i hi h1
    | cons g gs ih =>
      intro hops w1 w2 hlen hrel
      apply ih (fun g' hg' => hops g' (List.mem_cons_of_mem g hg'))
      · simp [stepW, hlen]
      · intro i hi h1
        have hReadMono : ∀ k, w1.getD k false = true → w2.getD k false = true := by
          intro k hk
          by_cases hklt : k < w1.length
          · exact hrel k hklt hk
          · have : w1[k]? = none := List.getElem?_eq_none (by omega)
            rw [List.getD_eq_getElem?_getD, this] at hk; exact absurd hk (by decide)
        by_cases hilt : i < w1.length
        · rw [List.getD_append _ _ false i hilt] at h1
          rw [List.getD_append _ _ false i (by omega)]
          exact hrel i hilt h1
        · have hiEq : i = w1.length := by simp [stepW] at hi; omega
          subst hiEq
          dsimp only [stepW] at h1 ⊢
          rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self] at h1
          rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
          change g.op.eval (g.inputs.map fun k => w1.getD k false) = true at h1
          change g.op.eval (g.inputs.map fun k => w2.getD k false) = true
          rcases hops g (List.mem_cons_self ..) with hand | hor
          · rw [hand, hEvalAnd] at h1 ⊢
            simp only [List.all_map, Function.comp_def, List.all_eq_true, id_eq] at h1 ⊢
            intro k hk; exact hReadMono k (h1 k hk)
          · rw [hor, hEvalOr] at h1 ⊢
            simp only [List.any_map, Function.comp_def, List.any_eq_true, id_eq] at h1 ⊢
            obtain ⟨k, hk, h1k⟩ := h1
            exact ⟨k, hk, hReadMono k h1k⟩
  have hWireGate : ∀ (C : Circuit) (x : List Bool) (j : ℕ),
      ReadsBack x.length C → j < C.gates.length →
      (C.wires x).getD (x.length + j) false =
        (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
    intro C x j hRB hj
    have hSplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hTakeLen : (C.gates.take j).length = j := List.length_take_of_le (le_of_lt hj)
    have hPreLen : (wF (C.gates.take j) x).length = x.length + j := by
      rw [hLenWF, hTakeLen]
    have hWires : C.wires x = wF (C.gates.drop (j + 1)) (stepW (wF (C.gates.take j) x) C.gates[j]) := by
      change wF C.gates x = _
      conv_lhs => rw [hSplit]
      rw [hWFAppend]; rfl
    have hStepVal : (C.wires x).getD (x.length + j) false =
        C.gates[j].op.eval (C.gates[j].inputs.map fun i => (wF (C.gates.take j) x).getD i false) := by
      rw [hWires, hWFLt _ _ (x.length + j) (by dsimp only [stepW]; rw [List.length_append, hPreLen]; simp)]
      dsimp only [stepW]
      rw [List.getD_append_right _ _ _ _ (by omega), hPreLen, Nat.sub_self]
      rfl
    rw [hStepVal, hGateAtEq C j hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hiLt : i < x.length + j := hRB j hj i (by rw [hGateAtEq C j hj]; exact hi)
    rw [hWires]
    symm
    rw [hWFLt _ _ i (by dsimp only [stepW]; rw [List.length_append, hPreLen]; simp; omega)]
    exact List.getD_append _ _ false i (by omega)
  have hOfFnEq : ∀ (xs : List Bool), xs.length = 26 →
      List.ofFn (fun i : Fin 26 => xs.getD i.val false) = xs := by
    intro xs hlen
    apply List.ext_getElem
    · rw [List.length_ofFn, hlen]
    · intro i h1 h2
      rw [List.getElem_ofFn, List.getD_eq_getElem xs false h2]
  have hFits : ∀ (C : Circuit), fitC C mask →
      ∀ (C' : Circuit), (∀ x : Fin 26 → Bool, C'.eval (inp x) = C.eval (inp x)) →
      fitC C' mask := by
    intro C hF C' heq
    have hEq26 : ∀ xs : List Bool, xs.length = 26 → C'.eval (inpL xs) = C.eval (inpL xs) := by
      intro xs hlen
      rw [← hOfFnEq xs hlen]
      exact heq (fun i => xs.getD i.val false)
    refine ⟨fun p l hpl => ?_, fun Q hQ1 hQ2 => ?_⟩
    · change C'.eval (inpL _) = true; rw [hEq26 _ (by simp)]; exact hF.1 p l hpl
    · change C'.eval (inpL _) = false; rw [hEq26 _ (by simp)]; exact hF.2 Q hQ1 hQ2
  let Good : Circuit → Prop := fun C => Monotone2 C ∧ ReadsBack 27 C ∧ fitC C mask
  have hGoodEvalPair : ∀ (C : Circuit), Good C → ∀ u v : Fin 26,
      C.eval (inp (fun w => decide (w = u ∨ w = v))) = adj u v := by
    intro C hG u v
    obtain ⟨hM, _, hPos, hNeg⟩ := hG
    have hMonoC : ∀ (x y : Fin 26 → Bool), (∀ i : Fin 26, x i = true → y i = true) →
        C.eval (inp x) = true → C.eval (inp y) = true := by
      intro x y hxy hx
      have hInpMono : ∀ i < (inp x).length, (inp x).getD i false = true → (inp y).getD i false = true := by
        intro i hi hxi
        rw [hInpLen x] at hi
        by_cases h26 : i < 26
        · rw [show i = (⟨i, h26⟩ : Fin 26).val from rfl, hInpGet x] at hxi
          rw [show i = (⟨i, h26⟩ : Fin 26).val from rfl, hInpGet y]
          exact hxy ⟨i, h26⟩ hxi
        · have hi26 : i = 26 := by omega
          subst hi26
          rw [hInp26 x, decide_eq_true_eq] at hxi
          rw [hInp26 y, decide_eq_true_eq]
          obtain ⟨a, ha, hxa⟩ := hxi
          exact ⟨a, ha, hxy a hxa⟩
      have hlenW : (C.wires (inp x)).length = 27 + C.gates.length := by
        change (wF C.gates (inp x)).length = _; rw [hLenWF, hInpLen]
      by_cases hout : C.output < 27 + C.gates.length
      · exact hMonoWF C.gates (hMonoOps C hM) (inp x) (inp y) (by rw [hInpLen, hInpLen]) hInpMono
          C.output (by rw [hLenWF, hInpLen]; exact hout) hx
      · have hnone : (C.wires (inp x))[C.output]? = none := List.getElem?_eq_none (by omega)
        change (C.wires (inp x)).getD C.output false = true at hx
        rw [List.getD_eq_getElem?_getD, hnone] at hx
        exact absurd hx (by decide)
    cases hadj : adj u v with
    | true =>
      by_cases hu : u.val < 13
      · have hv : 13 ≤ v.val := by
          by_contra hlt
          have : adj u v = false := by dsimp only [adj]; rw [dif_pos hu, dif_neg hlt]
          rw [this] at hadj; exact Bool.false_ne_true hadj
        dsimp only [adj] at hadj; rw [dif_pos hu, dif_pos hv] at hadj
        let p : Fin 13 := ⟨u.val, hu⟩
        let l : Fin 13 := ⟨v.val - 13, by omega⟩
        have hpl : p - l ∈ D := (hInD (p - l)).mpr hadj
        have hEqL : List.ofFn (fun w : Fin 26 => decide (w = u ∨ w = v)) =
            (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun j : Fin 13 => decide (j = l) := by
          apply List.ext_getElem
          · simp
          · intro i h1 h2
            rw [List.getElem_ofFn]
            by_cases hi13 : i < 13
            · rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
              apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
              constructor
              · rintro (h | h)
                · exact Fin.ext (by have := congrArg Fin.val h; exact this)
                · exfalso; have := congrArg Fin.val h; dsimp at this; omega
              · intro h; left; exact Fin.ext (by have := congrArg Fin.val h; exact this)
            · rw [List.getElem_append_right (by simp; omega)]
              simp only [List.length_ofFn, List.getElem_ofFn]
              apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
              constructor
              · rintro (h | h)
                · exfalso; have := congrArg Fin.val h; dsimp at this; omega
                · exact Fin.ext (by dsimp only; have := congrArg Fin.val h; dsimp [l] at *; omega)
              · intro h; right; exact Fin.ext (by dsimp only; have := congrArg Fin.val h; dsimp [l] at this; omega)
        dsimp only [inp]; rw [hEqL]; convert hPos p l hpl using 2
      · have hv : v.val < 13 := by
          by_contra hlt
          have : adj u v = false := by dsimp only [adj]; rw [dif_neg hu, dif_neg hlt]
          rw [this] at hadj; exact Bool.false_ne_true hadj
        dsimp only [adj] at hadj; rw [dif_neg hu, dif_pos hv] at hadj
        let p : Fin 13 := ⟨v.val, hv⟩
        let l : Fin 13 := ⟨u.val - 13, by omega⟩
        have hpl : p - l ∈ D := (hInD (p - l)).mpr hadj
        have hEqL : List.ofFn (fun w : Fin 26 => decide (w = u ∨ w = v)) =
            (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun j : Fin 13 => decide (j = l) := by
          apply List.ext_getElem
          · simp
          · intro i h1 h2
            rw [List.getElem_ofFn]
            by_cases hi13 : i < 13
            · rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
              apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
              constructor
              · rintro (h | h)
                · exfalso; have := congrArg Fin.val h; dsimp at this; omega
                · exact Fin.ext (by have := congrArg Fin.val h; exact this)
              · intro h; right; exact Fin.ext (by have := congrArg Fin.val h; exact this)
            · rw [List.getElem_append_right (by simp; omega)]
              simp only [List.length_ofFn, List.getElem_ofFn]
              apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
              constructor
              · rintro (h | h)
                · exact Fin.ext (by dsimp only; have := congrArg Fin.val h; dsimp [l] at *; omega)
                · exfalso; have := congrArg Fin.val h; dsimp at this; omega
              · intro h; left; exact Fin.ext (by dsimp only; have := congrArg Fin.val h; dsimp [l] at this; omega)
        dsimp only [inp]; rw [hEqL]; convert hPos p l hpl using 2
    | false =>
      have hExQ : ∃ Q : Finset (Fin 13), Q.card = 4 ∧
          (∀ l : Fin 13, (Q.filter fun p => p - l ∈ D).card ≤ 2) ∧
          (if hu : u.val < 13 then ⟨u.val, hu⟩ ∈ Q else ∀ r ∈ Q, r - ⟨u.val - 13, by omega⟩ ∉ D) ∧
          (if hv : v.val < 13 then ⟨v.val, hv⟩ ∈ Q else ∀ r ∈ Q, r - ⟨v.val - 13, by omega⟩ ∉ D) := by
        by_cases hu : u.val < 13
        · by_cases hv : v.val < 13
          · let s : Fin 13 := ⟨u.val, hu⟩
            let d : Fin 13 := ⟨v.val, hv⟩ - s
            obtain ⟨hQ, h0, hd⟩ := hQPPL d
            obtain ⟨hc, hl⟩ := hShiftQuad s (qPPL d) hQ
            refine ⟨(qPP d).image (· + s), hc, hl, ?_, ?_⟩
            · rw [dif_pos hu]; exact Finset.mem_image.mpr ⟨0, List.mem_toFinset.mpr h0, by simp [s]⟩
            · rw [dif_pos hv]; exact Finset.mem_image.mpr ⟨d, List.mem_toFinset.mpr hd, by simp [d]⟩
          · let s : Fin 13 := ⟨u.val, hu⟩
            let l : Fin 13 := ⟨v.val - 13, by omega⟩
            have hnot : inD ((0 : Fin 13) - (l - s)) = false := by
              dsimp only [adj] at hadj; rw [dif_pos hu, dif_pos (by omega : 13 ≤ v.val)] at hadj
              rwa [show (0 : Fin 13) - (l - s) = s - l by abel]
            obtain ⟨hQ, h0, hld⟩ := hQPLL (l - s) hnot
            obtain ⟨hc, hl⟩ := hShiftQuad s (qPLL (l - s)) hQ
            refine ⟨(qPL (l - s)).image (· + s), hc, hl, ?_, ?_⟩
            · rw [dif_pos hu]; exact Finset.mem_image.mpr ⟨0, List.mem_toFinset.mpr h0, by simp [s]⟩
            · rw [dif_neg hv]
              intro r hr hm
              obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
              have h1 := hld p (List.mem_toFinset.mp hp)
              have h2 := (hInD _).mp hm
              rw [show (p + s) - l = p - (l - s) by abel] at h2
              rw [h1] at h2; exact Bool.false_ne_true h2
        · by_cases hv : v.val < 13
          · let s : Fin 13 := ⟨v.val, hv⟩
            let l : Fin 13 := ⟨u.val - 13, by omega⟩
            have hnot : inD ((0 : Fin 13) - (l - s)) = false := by
              dsimp only [adj] at hadj; rw [dif_neg hu, dif_pos hv] at hadj
              rwa [show (0 : Fin 13) - (l - s) = s - l by abel]
            obtain ⟨hQ, h0, hld⟩ := hQPLL (l - s) hnot
            obtain ⟨hc, hl⟩ := hShiftQuad s (qPLL (l - s)) hQ
            refine ⟨(qPL (l - s)).image (· + s), hc, hl, ?_, ?_⟩
            · rw [dif_neg hu]
              intro r hr hm
              obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
              have h1 := hld p (List.mem_toFinset.mp hp)
              have h2 := (hInD _).mp hm
              rw [show (p + s) - l = p - (l - s) by abel] at h2
              rw [h1] at h2; exact Bool.false_ne_true h2
            · rw [dif_pos hv]; exact Finset.mem_image.mpr ⟨0, List.mem_toFinset.mpr h0, by simp [s]⟩
          · let s : Fin 13 := ⟨u.val - 13, by omega⟩
            let d : Fin 13 := ⟨v.val - 13, by omega⟩ - s
            obtain ⟨hQ, h0, hd⟩ := hQLLL d
            obtain ⟨hc, hl⟩ := hShiftQuad s (qLLL d) hQ
            refine ⟨(qLL d).image (· + s), hc, hl, ?_, ?_⟩
            · rw [dif_neg hu]
              intro r hr hm
              obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
              have h1 := h0 p (List.mem_toFinset.mp hp)
              have h2 := (hInD _).mp hm
              rw [show (p + s) - s = p - 0 by abel] at h2
              rw [h1] at h2; exact Bool.false_ne_true h2
            · rw [dif_neg hv]
              intro r hr hm
              obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
              have h1 := hd p (List.mem_toFinset.mp hp)
              have h2 := (hInD _).mp hm
              rw [show (p + s) - ⟨v.val - 13, by omega⟩ = p - d by dsimp only [d]; abel] at h2
              rw [h1] at h2; exact Bool.false_ne_true h2
      obtain ⟨Q, hQ1, hQ2, huQ, hvQ⟩ := hExQ
      let y : Fin 26 → Bool := fun w =>
        if hw : w.val < 13 then decide (⟨w.val, hw⟩ ∈ Q)
        else decide (∀ r ∈ Q, r - ⟨w.val - 13, by omega⟩ ∉ D)
      have hyEq : List.ofFn y =
          (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
          List.ofFn fun l : Fin 13 => decide (∀ r ∈ Q, r - l ∉ D) := by
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          rw [List.getElem_ofFn]
          by_cases hi13 : i < 13
          · rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
            dsimp only [y]; rw [dif_pos hi13]
          · rw [List.getElem_append_right (by simp; omega)]
            simp only [List.length_ofFn, List.getElem_ofFn]
            dsimp only [y]; rw [dif_neg hi13]
      have hyF : C.eval (inp y) = false := by
        dsimp only [inp]; rw [hyEq]
        convert hNeg Q hQ1 (by intro l; convert hQ2 l) using 2
      cases hc : C.eval (inp (fun w => decide (w = u ∨ w = v))) with
      | false => rfl
      | true =>
        exfalso
        have hle : ∀ i : Fin 26, decide (i = u ∨ i = v) = true → y i = true := by
          intro i hi
          rw [decide_eq_true_eq] at hi
          rcases hi with rfl | rfl
          · dsimp only [y]
            by_cases hu : i.val < 13
            · rw [dif_pos hu] at huQ ⊢; exact decide_eq_true huQ
            · rw [dif_neg hu] at huQ ⊢; exact decide_eq_true huQ
          · dsimp only [y]
            by_cases hv : i.val < 13
            · rw [dif_pos hv] at hvQ ⊢; exact decide_eq_true hvQ
            · rw [dif_neg hv] at hvQ ⊢; exact decide_eq_true hvQ
        have hyT := hMonoC _ y hle hc
        rw [hyF] at hyT; exact Bool.false_ne_true hyT
  have hGoodEvalSingle : ∀ (C : Circuit), Good C → ∀ u : Fin 26,
      C.eval (inp (fun w => decide (w = u))) = false := by
    intro C hG u
    have h1 := hGoodEvalPair C hG u u
    rw [hAdjIrrefl u] at h1
    simpa only [or_self] using h1
  have hGoodOutBounds : ∀ (C : Circuit), Good C → 27 ≤ C.output ∧ C.output < 27 + C.gates.length := by
    intro C hG
    have hOutHi : C.output < 27 + C.gates.length := by
      have h00 : C.eval (inp (fun w => decide (w = (0 : Fin 26) ∨ w = (13 : Fin 26)))) = true := by
        rw [hGoodEvalPair C hG 0 13]; exact hAdj013
      by_contra hge
      have hlen : (C.wires (inp (fun w => decide (w = (0 : Fin 26) ∨ w = (13 : Fin 26))))).length =
          27 + C.gates.length := by
        change (wF C.gates _).length = _; rw [hLenWF, hInpLen]
      have hnone : (C.wires (inp (fun w => decide (w = (0 : Fin 26) ∨ w = (13 : Fin 26)))))[C.output]? = none :=
        List.getElem?_eq_none (by omega)
      change (C.wires _).getD C.output false = true at h00
      rw [List.getD_eq_getElem?_getD, hnone] at h00
      exact Bool.false_ne_true h00
    have hOutLo : 27 ≤ C.output := by
      by_contra hlt
      by_cases h26 : C.output < 26
      · let u : Fin 26 := ⟨C.output, h26⟩
        have h1 := hGoodEvalSingle C hG u
        change (wF C.gates (inp (fun w => decide (w = u)))).getD u.val false = false at h1
        rw [hWFLt _ _ u.val (by rw [hInpLen]; omega), hInpGet] at h1
        simp at h1
      · have h26eq : C.output = 26 := by omega
        by_cases hne : (maskSet mask).Nonempty
        · obtain ⟨u, hu⟩ := hne
          have h1 := hGoodEvalSingle C hG u
          change (wF C.gates (inp (fun w => decide (w = u)))).getD C.output false = false at h1
          rw [h26eq, hWFLt _ _ 26 (by rw [hInpLen]; omega), hInp26] at h1
          have hT : decide (∃ v ∈ maskSet mask, decide (v = u) = true) = true :=
            decide_eq_true ⟨u, hu, by simp⟩
          rw [hT] at h1; exact Bool.false_ne_true h1.symm
        · have h00 : C.eval (inp (fun w => decide (w = (0 : Fin 26) ∨ w = (13 : Fin 26)))) = true := by
            rw [hGoodEvalPair C hG 0 13]; exact hAdj013
          change (wF C.gates _).getD C.output false = true at h00
          rw [h26eq, hWFLt _ _ 26 (by rw [hInpLen]; omega), hInp26] at h00
          rw [decide_eq_true_eq] at h00
          obtain ⟨u, hu, _⟩ := h00
          exact hne ⟨u, hu⟩
    exact ⟨hOutLo, hOutHi⟩
  clear hQPPL hQLLL hQPLL hQuadL hShiftQuad hCommonPt hCommonLn hInD hMasksLt hMasksLen hMonoWF qPP qLL qPL qPPL qLLL qPLL isQuadL
  have hErase : ∀ (C : Circuit), Good C → ∀ (d r : ℕ), d < C.gates.length → r < 27 + d →
      (∀ x : Fin 26 → Bool, (C.wires (inp x)).getD (27 + d) false = (C.wires (inp x)).getD r false) →
      ∃ C' : Circuit, Good C' ∧ C'.size < C.size := by
    intro C hG d r hd hr hEq
    obtain ⟨hM, hRB, hPos, hNeg⟩ := hG
    let rn : ℕ → ℕ := fun w => if w < 27 + d then w else if w = 27 + d then r else w - 1
    let rnG : Gate → Gate := fun g => ⟨g.op, g.inputs.map rn⟩
    let pre : List Gate := C.gates.take d
    let gd : Gate := C.gates[d]
    let post : List Gate := C.gates.drop (d + 1)
    have hPreLen : pre.length = d := List.length_take_of_le (le_of_lt hd)
    have hPostLen : post.length = C.gates.length - d - 1 := by simp [post]; omega
    have hSplit : C.gates = pre ++ gd :: post := by
      have h1 := (List.take_append_drop d C.gates).symm
      have h2 : C.gates.drop d = gd :: post := List.drop_eq_getElem_cons hd
      rw [h2] at h1; exact h1
    let gs' : List Gate := pre ++ post.map rnG
    let C' : Circuit := ⟨gs', rn C.output⟩
    have hGsLen : gs'.length = C.gates.length - 1 := by
      simp only [gs', List.length_append, List.length_map, hPreLen, hPostLen]; omega
    have hM' : Monotone2 C' := by
      intro g hg
      change g ∈ pre ++ post.map rnG at hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hM g (List.mem_of_mem_take h1)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h2
        have hm := hM g0 (List.mem_of_mem_drop hg0)
        exact ⟨hm.1, by simp [rnG, hm.2]⟩
    have hRB' : ReadsBack 27 C' := by
      intro j hj w hw
      have hgat : gateAt C' j = C'.gates[j] := hGateAtEq C' j hj
      rw [hgat] at hw
      change w ∈ gs'[j].inputs at hw
      by_cases hjd : j < d
      · have hget : gs'[j] = C.gates[j] := by
          dsimp only [gs']
          rw [List.getElem_append_left (by omega)]
          exact List.getElem_take
        rw [hget] at hw
        exact hRB j (by omega) w (by rw [hGateAtEq C j (by omega)]; exact hw)
      · have hj' : j < gs'.length := hj
        have hjIdx : j - d < post.length := by omega
        have hget : gs'[j] = rnG post[j - d] := by
          dsimp only [gs']
          rw [List.getElem_append_right (by omega), List.getElem_map]
          simp [hPreLen]
        rw [hget] at hw
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
        have hpostEl : post[j - d] = C.gates[j + 1]'(by omega) := by
          dsimp only [post]
          rw [List.getElem_drop]
          congr 1; omega
        rw [hpostEl] at hu
        have huLt : u < 27 + (j + 1) := hRB (j + 1) (by omega) u (by rw [hGateAtEq C (j + 1) (by omega)]; exact hu)
        dsimp only [rn]
        split_ifs <;> omega
    have hEvalEq : ∀ x : Fin 26 → Bool, C'.eval (inp x) = C.eval (inp x) := by
      intro x
      let A : List Bool := wF pre (inp x)
      have hAlen : A.length = 27 + d := by rw [hLenWF, hInpLen, hPreLen]
      let bd : Bool := gd.op.eval (gd.inputs.map fun i => A.getD i false)
      have hPreWires : wF (pre ++ [gd]) (inp x) = A ++ [bd] := by rw [hWFAppend]; rfl
      have hOldWires : C.wires (inp x) = wF post (A ++ [bd]) := by
        change wF C.gates (inp x) = _
        conv_lhs => rw [hSplit]
        rw [hWFAppend]; rfl
      have hNewWires : C'.wires (inp x) = wF (post.map rnG) A := by
        change wF (pre ++ post.map rnG) (inp x) = _
        rw [hWFAppend]
      have hbdEq : bd = A.getD r false := by
        have h1 := hEq x
        rw [hOldWires] at h1
        rw [hWFLt post (A ++ [bd]) (27 + d) (by simp [hAlen])] at h1
        rw [List.getD_append_right A [bd] false (27 + d) (by omega), hAlen, Nat.sub_self] at h1
        rw [hWFLt post (A ++ [bd]) r (by simp [hAlen]; omega)] at h1
        rw [List.getD_append A [bd] false r (by omega)] at h1
        exact h1
      have hGetRn : ∀ (E : List Bool) (i : ℕ),
          (A ++ E).getD (rn i) false = (A ++ [bd] ++ E).getD i false := by
        intro E i
        dsimp only [rn]
        by_cases h1 : i < 27 + d
        · rw [if_pos h1, List.getD_append A E false i (by omega), List.append_assoc,
            List.getD_append A ([bd] ++ E) false i (by omega)]
        · rw [if_neg h1]
          by_cases h2 : i = 27 + d
          · rw [if_pos h2, List.getD_append A E false r (by omega), h2, List.append_assoc,
              List.getD_append_right A ([bd] ++ E) false (27 + d) (by omega), hAlen, Nat.sub_self]
            exact hbdEq.symm
          · rw [if_neg h2]
            rw [List.getD_append_right A E false (i - 1) (by omega)]
            rw [List.append_assoc, List.getD_append_right A ([bd] ++ E) false i (by omega), hAlen]
            have hsub : i - (27 + d) = (i - 1 - (27 + d)) + 1 := by omega
            rw [hsub]; rfl
      have hFold : ∀ (gs : List Gate) (E : List Bool),
          ∃ E' : List Bool, wF (gs.map rnG) (A ++ E) = A ++ E' ∧ wF gs (A ++ [bd] ++ E) = A ++ [bd] ++ E' := by
        intro gs
        induction gs with
        | nil => intro E; exact ⟨E, rfl, rfl⟩
        | cons h gs ih =>
          intro E
          have hstep : stepW (A ++ E) (rnG h) = A ++ (E ++ [h.op.eval (h.inputs.map fun i => (A ++ [bd] ++ E).getD i false)]) := by
            dsimp only [stepW, rnG]
            rw [List.append_assoc, List.map_map]
            congr 4
            apply List.map_congr_left
            intro i _; exact hGetRn E i
          change ∃ E', wF (gs.map rnG) (stepW (A ++ E) (rnG h)) = A ++ E' ∧ wF gs (stepW (A ++ [bd] ++ E) h) = A ++ [bd] ++ E'
          rw [hstep]
          have hstep2 : stepW (A ++ [bd] ++ E) h = A ++ [bd] ++ (E ++ [h.op.eval (h.inputs.map fun i => (A ++ [bd] ++ E).getD i false)]) := by
            dsimp only [stepW]; rw [List.append_assoc]
          rw [hstep2]
          exact ih _
      obtain ⟨E', hNewE, hOldE⟩ := hFold post []
      simp only [List.append_nil] at hNewE hOldE
      change (C'.wires (inp x)).getD (rn C.output) false = (C.wires (inp x)).getD C.output false
      rw [hNewWires, hOldWires, hNewE, hOldE]
      exact hGetRn E' C.output
    have hFit' := hFits C ⟨hPos, hNeg⟩ C' hEvalEq
    exact ⟨C', ⟨hM', hRB', hFit'.1, hFit'.2⟩, by change gs'.length < C.gates.length; omega⟩
  have hEraseConst : ∀ (C : Circuit), Good C → ∀ d < C.gates.length,
      (gateAt C d).inputs = [] → ∃ C' : Circuit, Good C' ∧ C'.size < C.size := by
    intro C hG d hd hEmpty
    obtain ⟨hM, hRB, hPos, hNeg⟩ := hG
    let gd : Gate := C.gates[d]
    have hgdEmpty : gd.inputs = [] := by
      change C.gates[d].inputs = []
      rw [← hGateAtEq C d hd]
      exact hEmpty
    let b : Bool := gd.op.eval []
    let sk : ℕ → ℕ := fun w => if w < 27 + d then w else w - 1
    let simpG : Gate → Gate := fun h =>
      if 27 + d ∈ h.inputs then
        if h.op = GateOp.and then
          if b = false then ⟨GateOp.or, []⟩
          else ⟨GateOp.and, (h.inputs.filter fun i => i != 27 + d).map sk⟩
        else
          if b = true then ⟨GateOp.and, []⟩
          else ⟨GateOp.or, (h.inputs.filter fun i => i != 27 + d).map sk⟩
      else ⟨h.op, h.inputs.map sk⟩
    let pre : List Gate := C.gates.take d
    let post : List Gate := C.gates.drop (d + 1)
    have hPreLen : pre.length = d := List.length_take_of_le (le_of_lt hd)
    have hPostLen : post.length = C.gates.length - d - 1 := by simp [post]; omega
    have hSplit : C.gates = pre ++ gd :: post := by
      have h1 := (List.take_append_drop d C.gates).symm
      have h2 : C.gates.drop d = gd :: post := List.drop_eq_getElem_cons hd
      rw [h2] at h1; exact h1
    let gs' : List Gate := pre ++ post.map simpG
    let C' : Circuit := ⟨gs', sk C.output⟩
    have hGsLen : gs'.length = C.gates.length - 1 := by
      simp only [gs', List.length_append, List.length_map, hPreLen, hPostLen]; omega
    have hM' : Monotone2 C' := by
      intro g hg
      change g ∈ pre ++ post.map simpG at hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hM g (List.mem_of_mem_take h1)
      · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp h2
        have hm := hM h (List.mem_of_mem_drop hh)
        dsimp only [simpG]
        split_ifs
        · exact ⟨Or.inr rfl, by simp⟩
        · exact ⟨Or.inl rfl, by rw [List.length_map]; exact (List.length_filter_le _ _).trans hm.2⟩
        · exact ⟨Or.inl rfl, by simp⟩
        · exact ⟨Or.inr rfl, by rw [List.length_map]; exact (List.length_filter_le _ _).trans hm.2⟩
        · exact ⟨hm.1, by simp [hm.2]⟩
    have hRB' : ReadsBack 27 C' := by
      intro j hj w hw
      rw [hGateAtEq C' j hj] at hw
      change w ∈ gs'[j].inputs at hw
      by_cases hjd : j < d
      · have hget : gs'[j] = C.gates[j] := by
          dsimp only [gs']; rw [List.getElem_append_left (by omega)]; exact List.getElem_take
        rw [hget] at hw
        exact hRB j (by omega) w (by rw [hGateAtEq C j (by omega)]; exact hw)
      · have hj' : j < gs'.length := hj
        have hjIdx : j - d < post.length := by omega
        have hget : gs'[j] = simpG post[j - d] := by
          dsimp only [gs']; rw [List.getElem_append_right (by omega), List.getElem_map]; simp [hPreLen]
        rw [hget] at hw
        have hpostEl : post[j - d] = C.gates[j + 1]'(by omega) := by
          dsimp only [post]; rw [List.getElem_drop]; congr 1; omega
        rw [hpostEl] at hw
        have hSkLt : ∀ u ∈ (C.gates[j + 1]'(by omega)).inputs, u ≠ 27 + d → sk u < 27 + j := by
          intro u hu hne
          have huLt : u < 27 + (j + 1) := hRB (j + 1) (by omega) u (by rw [hGateAtEq C (j + 1) (by omega)]; exact hu)
          dsimp only [sk]; split_ifs <;> omega
        dsimp only [simpG] at hw
        split_ifs at hw
        · simp at hw
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
          obtain ⟨huin, hune⟩ := List.mem_filter.mp hu
          exact hSkLt u huin (by simpa using hune)
        · simp at hw
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
          obtain ⟨huin, hune⟩ := List.mem_filter.mp hu
          exact hSkLt u huin (by simpa using hune)
        · rename_i hnot
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
          exact hSkLt u hu (fun heq => hnot (heq ▸ hu))
    have hGetSk : ∀ (A E : List Bool), A.length = 27 + d → ∀ i, i ≠ 27 + d →
        (A ++ E).getD (sk i) false = (A ++ [b] ++ E).getD i false := by
      intro A E hAlen i hne
      dsimp only [sk]
      by_cases h1 : i < 27 + d
      · rw [if_pos h1, List.getD_append A E false i (by omega), List.append_assoc,
          List.getD_append A ([b] ++ E) false i (by omega)]
      · rw [if_neg h1, List.getD_append_right A E false (i - 1) (by omega),
          List.append_assoc, List.getD_append_right A ([b] ++ E) false i (by omega), hAlen]
        have hsub : i - (27 + d) = (i - 1 - (27 + d)) + 1 := by omega
        rw [hsub]; rfl
    have hGetMid : ∀ (A E : List Bool), A.length = 27 + d →
        (A ++ [b] ++ E).getD (27 + d) false = b := by
      intro A E hAlen
      rw [List.append_assoc, List.getD_append_right A ([b] ++ E) false (27 + d) (by omega), hAlen, Nat.sub_self]
      rfl
    have hSimpEval : ∀ (A E : List Bool), A.length = 27 + d → ∀ (h : Gate),
        (h.op = GateOp.and ∨ h.op = GateOp.or) →
        h.op.eval (h.inputs.map fun i => (A ++ [b] ++ E).getD i false) =
        (simpG h).op.eval ((simpG h).inputs.map fun i => (A ++ E).getD i false) := by
      intro A E hAlen h hop
      dsimp only [simpG]
      by_cases hmem : 27 + d ∈ h.inputs
      · rw [if_pos hmem]
        rcases hop with hand | hor
        · rw [hand, if_pos rfl]
          cases hb : b with
          | false =>
            rw [if_pos rfl]
            simp only [hEvalAnd, hEvalOr, List.map_nil, List.any_nil]
            rw [List.all_eq_false]
            exact ⟨false, List.mem_map.mpr ⟨27 + d, hmem, by
              have hm := hGetMid A E hAlen; rw [hb] at hm; exact hm⟩, by simp⟩
          | true =>
            rw [if_neg (by decide)]
            simp only [hEvalAnd]
            apply Bool.eq_iff_iff.mpr
            simp only [List.all_eq_true, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq, id_eq]
            constructor
            · intro h1 v hv
              obtain ⟨w, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩ := hv
              have hsk := hGetSk A E hAlen i hne
              rw [hb] at hsk; rw [hsk]; exact h1 _ ⟨i, hi, rfl⟩
            · intro h2 v hv
              obtain ⟨i, hi, rfl⟩ := hv
              by_cases hne : i = 27 + d
              · have hm := hGetMid A E hAlen; rw [hb] at hm; rw [hne, hm]
              · have hsk := hGetSk A E hAlen i hne; rw [hb] at hsk; rw [← hsk]
                exact h2 _ ⟨sk i, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩
        · rw [hor, if_neg (fun heq => GateOp.noConfusion heq)]
          cases hb : b with
          | true =>
            rw [if_pos rfl]
            simp only [hEvalAnd, hEvalOr, List.map_nil, List.all_nil]
            rw [List.any_eq_true]
            exact ⟨true, List.mem_map.mpr ⟨27 + d, hmem, by
              have hm := hGetMid A E hAlen; rw [hb] at hm; exact hm⟩, by simp⟩
          | false =>
            rw [if_neg (by decide)]
            simp only [hEvalOr]
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq, id_eq]
            constructor
            · rintro ⟨_, ⟨i, hi, rfl⟩, ht⟩
              by_cases hne : i = 27 + d
              · have hm := hGetMid A E hAlen; rw [hb] at hm; rw [hne, hm] at ht; exact absurd ht (by decide)
              · have hsk := hGetSk A E hAlen i hne; rw [hb] at hsk
                exact ⟨_, ⟨sk i, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩, by rw [hsk]; exact ht⟩
            · rintro ⟨_, ⟨_, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩, ht⟩
              have hsk := hGetSk A E hAlen i hne; rw [hb] at hsk
              exact ⟨_, ⟨i, hi, rfl⟩, by rw [← hsk]; exact ht⟩
      · rw [if_neg hmem]
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro i hi
        exact (hGetSk A E hAlen i (fun heq => hmem (heq ▸ hi))).symm
    have hOutNe : C.output ≠ 27 + d := by
      intro heq
      have hConst : ∀ x : Fin 26 → Bool, C.eval (inp x) = b := by
        intro x
        let A : List Bool := wF pre (inp x)
        have hAlen : A.length = 27 + d := by rw [hLenWF, hInpLen, hPreLen]
        have hOldWires : C.wires (inp x) = wF post (A ++ [b]) := by
          change wF C.gates (inp x) = _
          conv_lhs => rw [hSplit]
          rw [hWFAppend]
          change wF post (A ++ [gd.op.eval (gd.inputs.map _)]) = _
          rw [hgdEmpty]; rfl
        change (C.wires (inp x)).getD C.output false = b
        rw [heq, hOldWires, hWFLt post (A ++ [b]) (27 + d) (by simp [hAlen]),
          List.getD_append_right A [b] false (27 + d) (by omega), hAlen, Nat.sub_self]
        rfl
      have hT : C.eval (inp (fun w => decide (w = (0 : Fin 26) ∨ w = (13 : Fin 26)))) = true := by
        rw [hGoodEvalPair C ⟨hM, hRB, hPos, hNeg⟩ 0 13]; exact hAdj013
      have hF : C.eval (inp (fun w => decide (w = (0 : Fin 26)))) = false :=
        hGoodEvalSingle C ⟨hM, hRB, hPos, hNeg⟩ 0
      rw [hConst] at hT hF
      rw [hT] at hF
      exact Bool.false_ne_true hF.symm
    have hEvalEq : ∀ x : Fin 26 → Bool, C'.eval (inp x) = C.eval (inp x) := by
      intro x
      let A : List Bool := wF pre (inp x)
      have hAlen : A.length = 27 + d := by rw [hLenWF, hInpLen, hPreLen]
      have hOldWires : C.wires (inp x) = wF post (A ++ [b]) := by
        change wF C.gates (inp x) = _
        conv_lhs => rw [hSplit]
        rw [hWFAppend]
        change wF post (A ++ [gd.op.eval (gd.inputs.map _)]) = _
        rw [hgdEmpty]; rfl
      have hNewWires : C'.wires (inp x) = wF (post.map simpG) A := by
        change wF (pre ++ post.map simpG) (inp x) = _
        rw [hWFAppend]
      have hFold : ∀ (gs : List Gate), (∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or) →
          ∀ (E : List Bool), ∃ E' : List Bool,
            wF (gs.map simpG) (A ++ E) = A ++ E' ∧ wF gs (A ++ [b] ++ E) = A ++ [b] ++ E' := by
        intro gs
        induction gs with
        | nil => intro _ E; exact ⟨E, rfl, rfl⟩
        | cons h gs ih =>
          intro hops E
          have h1 := hSimpEval A E hAlen h (hops h (List.mem_cons_self ..))
          have hstep1 : stepW (A ++ E) (simpG h) = A ++ (E ++ [h.op.eval (h.inputs.map fun i => (A ++ [b] ++ E).getD i false)]) := by
            dsimp only [stepW]; rw [List.append_assoc, ← h1]
          have hstep2 : stepW (A ++ [b] ++ E) h = A ++ [b] ++ (E ++ [h.op.eval (h.inputs.map fun i => (A ++ [b] ++ E).getD i false)]) := by
            dsimp only [stepW]; rw [List.append_assoc]
          change ∃ E', wF (gs.map simpG) (stepW (A ++ E) (simpG h)) = A ++ E' ∧ wF gs (stepW (A ++ [b] ++ E) h) = A ++ [b] ++ E'
          rw [hstep1, hstep2]
          exact ih (fun g' hg' => hops g' (List.mem_cons_of_mem h hg')) _
      obtain ⟨E', hNewE, hOldE⟩ := hFold post (fun h hh => hMonoOps C hM h (List.mem_of_mem_drop hh)) []
      simp only [List.append_nil] at hNewE hOldE
      change (C'.wires (inp x)).getD (sk C.output) false = (C.wires (inp x)).getD C.output false
      rw [hNewWires, hOldWires, hNewE, hOldE]
      exact hGetSk A E' hAlen C.output hOutNe
    have hFit' := hFits C ⟨hPos, hNeg⟩ C' hEvalEq
    exact ⟨C', ⟨hM', hRB', hFit'.1, hFit'.2⟩, by change gs'.length < C.gates.length; omega⟩
  have hRB0 : ReadsBack 27 C0 := by
    intro j hj w hw
    rw [hGateAtEq C0 j hj] at hw
    exact hRB0' ⟨j, hj⟩ w (by rwa [List.get_eq_getElem])
  have hFit0' : fitC C0 mask := by
    refine ⟨fun p l hpl => ?_, fun Q hQ1 hQ2 => ?_⟩
    · convert hFit0.1 p l hpl using 2
    · convert hFit0.2 Q hQ1 (by intro l; convert hQ2 l) using 2
  have hEx : ∃ k : ℕ, ∃ C : Circuit, Good C ∧ C.size = k :=
    ⟨C0.size, C0, ⟨hM0, hRB0, hFit0'⟩, rfl⟩
  let m := Nat.find hEx
  have hmLe : m ≤ C0.size := Nat.find_min' hEx ⟨C0, ⟨hM0, hRB0, hFit0'⟩, rfl⟩
  obtain ⟨C, hGood, hCsz⟩ := Nat.find_spec hEx
  have hMin : ∀ C' : Circuit, Good C' → m ≤ C'.size := fun C' hG' => Nat.find_min' hEx ⟨C', hG', rfl⟩
  obtain ⟨hM, hRB, hPos, hNeg⟩ := hGood
  obtain ⟨hOutLo, hOutHi⟩ := hGoodOutBounds C ⟨hM, hRB, hPos, hNeg⟩
  have hLen2 : ∀ g ∈ C.gates, g.inputs.length = 2 := by
    intro g hg
    obtain ⟨d, hd, hgd⟩ := List.mem_iff_getElem.mp hg
    have hle := (hM g hg).2
    rcases hlen : g.inputs.length with _ | _ | k
    · have hemp : (gateAt C d).inputs = [] := by
        rw [hGateAtEq C d hd, hgd]; exact List.eq_nil_of_length_eq_zero hlen
      obtain ⟨C', hG', hlt⟩ := hEraseConst C ⟨hM, hRB, hPos, hNeg⟩ d hd hemp
      exact absurd (hMin C' hG') (by omega)
    · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
      have hga : (gateAt C d).inputs = [a] := by rw [hGateAtEq C d hd, hgd, ha]
      have haLt : a < 27 + d := hRB d hd a (by rw [hga]; simp)
      have heq : ∀ x : Fin 26 → Bool, (C.wires (inp x)).getD (27 + d) false = (C.wires (inp x)).getD a false := by
        intro x
        rw [show (27 : ℕ) = (inp x).length from (hInpLen x).symm]
        rw [hWireGate C (inp x) d (by rw [hInpLen]; exact hRB) hd, hga]
        rcases hMonoOps C hM (gateAt C d) (by rw [hGateAtEq C d hd]; exact List.getElem_mem hd) with hop | hop
        · rw [hop, hEvalAnd]; simp
        · rw [hop, hEvalOr]; simp
      obtain ⟨C', hG', hlt⟩ := hErase C ⟨hM, hRB, hPos, hNeg⟩ d a hd haLt heq
      exact absurd (hMin C' hG') (by omega)
    · omega
  have hAO2 : IsAO2 27 C := ⟨hMonoOps C hM, hRB, hLen2⟩
  have hGoalMin : 63 ≤ C.size → 63 ≤ C0.size := by omega
  apply hGoalMin
  clear hGoalMin hmLe hEraseConst hFits hOfFnEq hGoodOutBounds hRB0 hRB0' hM0 hFit0 hFit0'
  by_cases hAP0 : andPairs 27 C = 0
  · have hConeStep : ∀ (cs : List (List ℕ)) (g : Gate), coneStep 27 cs g =
        cs ++ [(g.inputs.filter (fun w => decide (27 ≤ w ∧ w < 27 + cs.length))).flatMap
          (fun w => (w - 27) :: cs.getD (w - 27) [])] := fun _ _ => rfl
    have hConesLen : ∀ gs : List Gate, ∀ cs : List (List ℕ),
        (gs.foldl (coneStep 27) cs).length = cs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro cs; simp
      | cons g gs ih =>
        intro cs
        rw [List.foldl_cons, ih, hConeStep]
        simp; omega
    have hConesLt : ∀ gs : List Gate, ∀ cs : List (List ℕ), ∀ i < cs.length,
        (gs.foldl (coneStep 27) cs).getD i [] = cs.getD i [] := by
      intro gs
      induction gs with
      | nil => intro cs i _; rfl
      | cons g gs ih =>
        intro cs i hi
        rw [List.foldl_cons, ih _ i (by rw [hConeStep]; simp; omega), hConeStep]
        exact List.getD_append cs _ [] i hi
    have hConeMem : ∀ (j : ℕ) (hj : j < C.gates.length) (w : ℕ),
        w ∈ (gateAt C j).inputs → 27 ≤ w →
        InCone 27 C (w - 27) j ∧ ∀ i : ℕ, InCone 27 C i (w - 27) → InCone 27 C i j := by
      intro j hj w hw hw27
      have hwLt : w < 27 + j := hRB j hj w hw
      have hSplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
        rw [List.cons_getElem_drop_succ, List.take_append_drop]
      let cs := (C.gates.take j).foldl (coneStep 27) []
      have hcsLen : cs.length = j := by
        rw [hConesLen, List.length_nil, Nat.zero_add, List.length_take_of_le (le_of_lt hj)]
      have hConesEq : cones 27 C = (C.gates.drop (j + 1)).foldl (coneStep 27) (coneStep 27 cs C.gates[j]) := by
        change C.gates.foldl (coneStep 27) [] = _
        conv_lhs => rw [hSplit]
        rw [List.foldl_append, List.foldl_cons]
      have hGetJ : (cones 27 C).getD j [] =
          (C.gates[j].inputs.filter (fun u => decide (27 ≤ u ∧ u < 27 + j))).flatMap
            (fun u => (u - 27) :: cs.getD (u - 27) []) := by
        rw [hConesEq, hConesLt _ _ j (by rw [hConeStep]; simp [hcsLen]), hConeStep]
        rw [List.getD_append_right _ _ _ _ (by omega), hcsLen, Nat.sub_self]
        rfl
      have hGetW : cs.getD (w - 27) [] = (cones 27 C).getD (w - 27) [] := by
        rw [hConesEq]
        symm
        rw [hConesLt _ _ (w - 27) (by rw [hConeStep]; simp [hcsLen]; omega), hConeStep]
        exact List.getD_append cs _ [] (w - 27) (by omega)
      have hwFilt : w ∈ C.gates[j].inputs.filter (fun u => decide (27 ≤ u ∧ u < 27 + j)) := by
        rw [List.mem_filter]
        exact ⟨by rw [← hGateAtEq C j hj]; exact hw, by simp [hw27, hwLt]⟩
      constructor
      · change w - 27 ∈ (cones 27 C).getD j []
        rw [hGetJ, List.mem_flatMap]
        exact ⟨w, hwFilt, by simp⟩
      · intro i hi
        change i ∈ (cones 27 C).getD (w - 27) [] at hi
        change i ∈ (cones 27 C).getD j []
        rw [hGetJ, List.mem_flatMap]
        exact ⟨w, hwFilt, List.mem_cons_of_mem _ (by rw [hGetW]; exact hi)⟩
    let in0 : ℕ → ℕ := fun j => (gateAt C j).inputs.getD 0 0
    let in1 : ℕ → ℕ := fun j => (gateAt C j).inputs.getD 1 0
    have hInsEq : ∀ j < C.gates.length, (gateAt C j).inputs = [in0 j, in1 j] := by
      intro j hj
      have hl := hLen2 (gateAt C j) (by rw [hGateAtEq C j hj]; exact List.getElem_mem hj)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
      simp only [in0, in1, hab, List.getD_cons_zero, List.getD_cons_succ]
    have hInLt : ∀ j < C.gates.length, in0 j < 27 + j ∧ in1 j < 27 + j := by
      intro j hj
      exact ⟨hRB j hj (in0 j) (by rw [hInsEq j hj]; simp), hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)⟩
    let andFree : ℕ → Prop := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h27 : w < 27 then True
      else if hlt : w < 27 + C.gates.length then
        (gateAt C (w - 27)).op = GateOp.or ∧
          ih (in0 (w - 27)) (by
            have hj : w - 27 < C.gates.length := by omega
            have := (hInLt (w - 27) hj).1; change _ < w; omega) ∧
          ih (in1 (w - 27)) (by
            have hj : w - 27 < C.gates.length := by omega
            have := (hInLt (w - 27) hj).2; change _ < w; omega)
      else False
    have hAF_lt27 : ∀ w < 27, andFree w := by
      intro w hw; dsimp only [andFree]; rw [WellFounded.fix_eq, dif_pos hw]; trivial
    have hAF_gate : ∀ j < C.gates.length, andFree (27 + j) ↔
        (gateAt C j).op = GateOp.or ∧ andFree (in0 j) ∧ andFree (in1 j) := by
      intro j hj
      conv_lhs =>
        dsimp only [andFree]
        rw [WellFounded.fix_eq, dif_neg (Nat.not_lt.mpr (Nat.le_add_right 27 j)),
          dif_pos (Nat.add_lt_add_left hj 27)]
      dsimp only
      rw [Nat.add_sub_cancel_left]
    have hNoAndInCone : ∀ w < 27 + C.gates.length, ¬ andFree w →
        27 ≤ w ∧ ∃ i < C.gates.length, (gateAt C i).op = GateOp.and ∧
          (i = w - 27 ∨ InCone 27 C i (w - 27)) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt hnaf
        have hw27 : 27 ≤ w := by
          by_contra hlt; exact hnaf (hAF_lt27 w (by omega))
        refine ⟨hw27, ?_⟩
        let j := w - 27
        have hj : j < C.gates.length := by omega
        have hwj : w = 27 + j := by omega
        rw [hwj] at hnaf
        rcases hMonoOps C hM (gateAt C j) (by rw [hGateAtEq C j hj]; exact List.getElem_mem hj) with hop | hop
        · exact ⟨j, hj, hop, Or.inl rfl⟩
        · have hnotboth : ¬ andFree (in0 j) ∨ ¬ andFree (in1 j) := by
            by_contra hboth
            push Not at hboth
            exact hnaf ((hAF_gate j hj).mpr ⟨hop, hboth.1, hboth.2⟩)
          have hlt0 : in0 j < 27 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
          have hlt1 : in1 j < 27 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
          rcases hnotboth with h0 | h1
          · obtain ⟨h27, i, hi, hiop, hic⟩ := ih (in0 j) (by omega) (by omega) h0
            obtain ⟨hm1, hm2⟩ := hConeMem j hj (in0 j) (by rw [hInsEq j hj]; simp) h27
            rcases hic with rfl | hic
            · exact ⟨in0 j - 27, hi, hiop, Or.inr hm1⟩
            · exact ⟨i, hi, hiop, Or.inr (hm2 i hic)⟩
          · obtain ⟨h27, i, hi, hiop, hic⟩ := ih (in1 j) (by omega) (by omega) h1
            obtain ⟨hm1, hm2⟩ := hConeMem j hj (in1 j) (by rw [hInsEq j hj]; simp) h27
            rcases hic with rfl | hic
            · exact ⟨in1 j - 27, hi, hiop, Or.inr hm1⟩
            · exact ⟨i, hi, hiop, Or.inr (hm2 i hic)⟩
    have hAndChildAF : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        andFree (in0 j) ∧ andFree (in1 j) := by
      intro j hj hop
      have hOne : ∀ w ∈ (gateAt C j).inputs, andFree w := by
        intro w hw
        by_contra hnaf
        have hwLt : w < 27 + j := hRB j hj w hw
        obtain ⟨hw27, i, hi, hiop, hic⟩ := hNoAndInCone w (by omega) hnaf
        obtain ⟨hm1, hm2⟩ := hConeMem j hj w hw hw27
        have hinc : InCone 27 C i j := by
          rcases hic with rfl | hic
          · exact hm1
          · exact hm2 i hic
        have hpos : 0 < andPairs 27 C := by
          refine Finset.card_pos.mpr ⟨(i, j), ?_⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨hi, hj⟩, hiop, hop, hinc⟩
        omega
      exact ⟨hOne _ (by rw [hInsEq j hj]; simp), hOne _ (by rw [hInsEq j hj]; simp)⟩
    let orVars : ℕ → Finset (Fin 26) := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h26 : w < 26 then {⟨w, h26⟩}
      else if hw26 : w = 26 then maskSet mask
      else if hlt : w < 27 + C.gates.length then
        if (gateAt C (w - 27)).op = GateOp.or then
          ih (in0 (w - 27)) (by
            have hj : w - 27 < C.gates.length := by omega
            have := (hInLt (w - 27) hj).1; change _ < w; omega) ∪
          ih (in1 (w - 27)) (by
            have hj : w - 27 < C.gates.length := by omega
            have := (hInLt (w - 27) hj).2; change _ < w; omega)
        else ∅
      else ∅
    have hOV_lt26 : ∀ u : Fin 26, orVars u.val = {u} := by
      intro u; dsimp only [orVars]; rw [WellFounded.fix_eq, dif_pos u.isLt]
    have hOV_26 : orVars 26 = maskSet mask := by
      dsimp only [orVars]; rw [WellFounded.fix_eq, dif_neg (Nat.lt_irrefl 26), dif_pos rfl]
    have hOV_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        orVars (27 + j) = orVars (in0 j) ∪ orVars (in1 j) := by
      intro j hj hop
      have h1 : ¬ 27 + j < 26 := by omega
      have h2 : 27 + j ≠ 26 := by omega
      have h3 : 27 + j < 27 + C.gates.length := Nat.add_lt_add_left hj 27
      conv_lhs =>
        dsimp only [orVars]
        rw [WellFounded.fix_eq, dif_neg h1, dif_neg h2, dif_pos h3]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, ite_true]
      rfl
    have hAF_eval : ∀ w < 27 + C.gates.length, andFree w →
        ∀ x : Fin 26 → Bool, (C.wires (inp x)).getD w false = decide (∃ u ∈ orVars w, x u = true) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf x
        by_cases h26 : w < 26
        · rw [show w = (⟨w, h26⟩ : Fin 26).val from rfl, hOV_lt26]
          change (wF C.gates (inp x)).getD w false = _
          rw [hWFLt _ _ w (by rw [hInpLen]; omega), hInpGet x ⟨w, h26⟩]
          simp
        · by_cases hw26 : w = 26
          · subst hw26
            rw [hOV_26]
            change (wF C.gates (inp x)).getD 26 false = _
            rw [hWFLt _ _ 26 (by rw [hInpLen]; omega), hInp26 x]
          · let j := w - 27
            have hj : j < C.gates.length := by omega
            have hwj : w = 27 + j := by omega
            rw [hwj] at haf ⊢
            obtain ⟨hop, haf0, haf1⟩ := (hAF_gate j hj).mp haf
            rw [hOV_or j hj hop]
            rw [show (27 : ℕ) = (inp x).length from (hInpLen x).symm]
            rw [hWireGate C (inp x) j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj]
            have hlt0 : in0 j < 27 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
            have hlt1 : in1 j < 27 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
            have ih0 := ih (in0 j) (by omega) (by omega) haf0 x
            have ih1 := ih (in1 j) (by omega) (by omega) haf1 x
            simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, ih0, ih1]
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union]
            constructor
            · rintro (⟨u, hu, hx⟩ | ⟨u, hu, hx⟩)
              · exact ⟨u, Or.inl hu, hx⟩
              · exact ⟨u, Or.inr hu, hx⟩
            · rintro ⟨u, hu | hu, hx⟩
              · exact Or.inl ⟨u, hu, hx⟩
              · exact Or.inr ⟨u, hu, hx⟩
    have hOV_empty_imp : ∀ w < 27 + C.gates.length, andFree w → orVars w = ∅ → maskSet mask = ∅ := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf hemp
        by_cases h26 : w < 26
        · rw [show w = (⟨w, h26⟩ : Fin 26).val from rfl, hOV_lt26] at hemp
          exact absurd hemp (Finset.singleton_ne_empty _)
        · by_cases hw26 : w = 26
          · subst hw26; rwa [hOV_26] at hemp
          · let j := w - 27
            have hj : j < C.gates.length := by omega
            have hwj : w = 27 + j := by omega
            rw [hwj] at haf hemp
            obtain ⟨hop, haf0, _⟩ := (hAF_gate j hj).mp haf
            rw [hOV_or j hj hop] at hemp
            have hlt0 : in0 j < 27 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
            exact ih (in0 j) (by omega) (by omega) haf0 (Finset.union_eq_empty.mp hemp).1
    have hAF_card_ge_2 : ∀ j < C.gates.length, andFree (27 + j) → 2 ≤ (orVars (27 + j)).card := by
      intro j hj haf
      by_contra hlt
      have hc : (orVars (27 + j)).card = 0 ∨ (orVars (27 + j)).card = 1 := by omega
      rcases hc with h0 | h1
      · have hemp : orVars (27 + j) = ∅ := Finset.card_eq_zero.mp h0
        have hm0 : maskSet mask = ∅ := hOV_empty_imp (27 + j) (by omega) haf hemp
        have heq : ∀ x : Fin 26 → Bool, (C.wires (inp x)).getD (27 + j) false = (C.wires (inp x)).getD 26 false := by
          intro x
          rw [hAF_eval (27 + j) (by omega) haf x, hemp]
          change _ = (wF C.gates (inp x)).getD 26 false
          rw [hWFLt _ _ 26 (by rw [hInpLen]; omega), hInp26 x, hm0]
        obtain ⟨C', hG', hlt'⟩ := hErase C ⟨hM, hRB, hPos, hNeg⟩ j 26 hj (by omega) heq
        exact absurd (hMin C' hG') (by omega)
      · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
        have heq : ∀ x : Fin 26 → Bool, (C.wires (inp x)).getD (27 + j) false = (C.wires (inp x)).getD u.val false := by
          intro x
          rw [hAF_eval (27 + j) (by omega) haf x, hu]
          change _ = (wF C.gates (inp x)).getD u.val false
          rw [hWFLt _ _ u.val (by rw [hInpLen]; omega), hInpGet x u]
          simp
        obtain ⟨C', hG', hlt'⟩ := hErase C ⟨hM, hRB, hPos, hNeg⟩ j u.val hj (by omega) heq
        exact absurd (hMin C' hG') (by omega)
    let topAndsOf : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h27 : w < 27 then ∅
      else if hlt : w < 27 + C.gates.length then
        if (gateAt C (w - 27)).op = GateOp.and then {w - 27}
        else
          ih (in0 (w - 27)) (by
            have hj : w - 27 < C.gates.length := by omega
            have := (hInLt (w - 27) hj).1; change _ < w; omega) ∪
          ih (in1 (w - 27)) (by
            have hj : w - 27 < C.gates.length := by omega
            have := (hInLt (w - 27) hj).2; change _ < w; omega)
      else ∅
    let topOrsOf : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h27 : w < 27 then ∅
      else if hlt : w < 27 + C.gates.length then
        if (gateAt C (w - 27)).op = GateOp.and then ∅
        else
          insert (w - 27) (
            ih (in0 (w - 27)) (by
              have hj : w - 27 < C.gates.length := by omega
              have := (hInLt (w - 27) hj).1; change _ < w; omega) ∪
            ih (in1 (w - 27)) (by
              have hj : w - 27 < C.gates.length := by omega
              have := (hInLt (w - 27) hj).2; change _ < w; omega))
      else ∅
    let reachesInp : ℕ → Prop := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h26 : w < 26 then True
      else if hw26 : w = 26 then (maskSet mask).Nonempty
      else if hlt : w < 27 + C.gates.length then
        if (gateAt C (w - 27)).op = GateOp.and then False
        else
          ih (in0 (w - 27)) (by
            have hj : w - 27 < C.gates.length := by omega
            have := (hInLt (w - 27) hj).1; change _ < w; omega) ∨
          ih (in1 (w - 27)) (by
            have hj : w - 27 < C.gates.length := by omega
            have := (hInLt (w - 27) hj).2; change _ < w; omega)
      else False
    have hRI_lt26 : ∀ w < 26, reachesInp w := by
      intro w hw; dsimp only [reachesInp]; rw [WellFounded.fix_eq, dif_pos hw]; trivial
    have hRI_26 : reachesInp 26 ↔ (maskSet mask).Nonempty := by
      dsimp only [reachesInp]; rw [WellFounded.fix_eq, dif_neg (Nat.lt_irrefl 26), dif_pos rfl]
    have hRI_and : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ¬ reachesInp (27 + j) := by
      intro j hj hop
      have h1 : ¬ 27 + j < 26 := by omega
      have h2 : 27 + j ≠ 26 := by omega
      have h3 : 27 + j < 27 + C.gates.length := Nat.add_lt_add_left hj 27
      dsimp only [reachesInp]
      rw [WellFounded.fix_eq, dif_neg h1, dif_neg h2, dif_pos h3]
      simp [hop]
    have hRI_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        (reachesInp (27 + j) ↔ reachesInp (in0 j) ∨ reachesInp (in1 j)) := by
      intro j hj hop
      have h1 : ¬ 27 + j < 26 := by omega
      have h2 : 27 + j ≠ 26 := by omega
      have h3 : 27 + j < 27 + C.gates.length := Nat.add_lt_add_left hj 27
      conv_lhs =>
        dsimp only [reachesInp]
        rw [WellFounded.fix_eq, dif_neg h1, dif_neg h2, dif_pos h3]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, reduceCtorEq, ite_false]
      rfl
    have hTA_lt27 : ∀ w < 27, topAndsOf w = ∅ := by
      intro w hw; dsimp only [topAndsOf]; rw [WellFounded.fix_eq, dif_pos hw]
    have hTA_and : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → topAndsOf (27 + j) = {j} := by
      intro j hj hop
      have h1 : ¬ 27 + j < 27 := Nat.not_lt.mpr (Nat.le_add_right 27 j)
      have h2 : 27 + j < 27 + C.gates.length := Nat.add_lt_add_left hj 27
      dsimp only [topAndsOf]
      rw [WellFounded.fix_eq, dif_neg h1, dif_pos h2]
      simp [hop]
    have hTA_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        topAndsOf (27 + j) = topAndsOf (in0 j) ∪ topAndsOf (in1 j) := by
      intro j hj hop
      have h1 : ¬ 27 + j < 27 := Nat.not_lt.mpr (Nat.le_add_right 27 j)
      have h2 : 27 + j < 27 + C.gates.length := Nat.add_lt_add_left hj 27
      conv_lhs =>
        dsimp only [topAndsOf]
        rw [WellFounded.fix_eq, dif_neg h1, dif_pos h2]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, reduceCtorEq, ite_false]
      rfl
    have hTO_lt27 : ∀ w < 27, topOrsOf w = ∅ := by
      intro w hw; dsimp only [topOrsOf]; rw [WellFounded.fix_eq, dif_pos hw]
    have hTO_and : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → topOrsOf (27 + j) = ∅ := by
      intro j hj hop
      have h1 : ¬ 27 + j < 27 := Nat.not_lt.mpr (Nat.le_add_right 27 j)
      have h2 : 27 + j < 27 + C.gates.length := Nat.add_lt_add_left hj 27
      dsimp only [topOrsOf]
      rw [WellFounded.fix_eq, dif_neg h1, dif_pos h2]
      simp [hop]
    have hTO_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        topOrsOf (27 + j) = insert j (topOrsOf (in0 j) ∪ topOrsOf (in1 j)) := by
      intro j hj hop
      have h1 : ¬ 27 + j < 27 := Nat.not_lt.mpr (Nat.le_add_right 27 j)
      have h2 : 27 + j < 27 + C.gates.length := Nat.add_lt_add_left hj 27
      conv_lhs =>
        dsimp only [topOrsOf]
        rw [WellFounded.fix_eq, dif_neg h1, dif_pos h2]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, reduceCtorEq, ite_false]
      rfl
    have hRI_single : ∀ w < 27 + C.gates.length, reachesInp w →
        ∃ u : Fin 26, (C.wires (inp (fun v => decide (v = u)))).getD w false = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt hri
        by_cases h26 : w < 26
        · refine ⟨⟨w, h26⟩, ?_⟩
          change (wF C.gates _).getD w false = true
          rw [hWFLt _ _ w (by rw [hInpLen]; omega), hInpGet _ ⟨w, h26⟩]; simp
        · by_cases hw26 : w = 26
          · subst hw26
            obtain ⟨u, hu⟩ := hRI_26.mp hri
            refine ⟨u, ?_⟩
            change (wF C.gates _).getD 26 false = true
            rw [hWFLt _ _ 26 (by rw [hInpLen]; omega), hInp26]
            exact decide_eq_true ⟨u, hu, by simp⟩
          · let j := w - 27
            have hj : j < C.gates.length := by omega
            have hwj : w = 27 + j := by omega
            rw [hwj] at hri ⊢
            rcases hMonoOps C hM (gateAt C j) (by rw [hGateAtEq C j hj]; exact List.getElem_mem hj) with hop | hop
            · exact absurd hri (hRI_and j hj hop)
            · rcases (hRI_or j hj hop).mp hri with h0 | h1
              · have hlt0 : in0 j < 27 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
                obtain ⟨u, hu⟩ := ih (in0 j) (by omega) (by omega) h0
                refine ⟨u, ?_⟩
                let xu : Fin 26 → Bool := fun v => decide (v = u)
                rw [show (27 : ℕ) = (inp xu).length from (hInpLen xu).symm]
                rw [hWireGate C (inp xu) j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj]
                simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false, Bool.or_eq_true, xu]
                exact Or.inl hu
              · have hlt1 : in1 j < 27 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
                obtain ⟨u, hu⟩ := ih (in1 j) (by omega) (by omega) h1
                refine ⟨u, ?_⟩
                let xu : Fin 26 → Bool := fun v => decide (v = u)
                rw [show (27 : ℕ) = (inp xu).length from (hInpLen xu).symm]
                rw [hWireGate C (inp xu) j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj]
                simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false, Bool.or_eq_true, xu]
                exact Or.inr hu
    have hOutNRI : ¬ reachesInp C.output := by
      intro hri
      obtain ⟨u, hu⟩ := hRI_single C.output hOutHi hri
      have hF := hGoodEvalSingle C ⟨hM, hRB, hPos, hNeg⟩ u
      change (C.wires _).getD C.output false = false at hF
      rw [hF] at hu; exact Bool.false_ne_true hu
    have hTopProps : ∀ w < 27 + C.gates.length, ¬ reachesInp w →
        (∀ j ∈ topAndsOf w, j < C.gates.length ∧ (gateAt C j).op = GateOp.and) ∧
        (∀ j ∈ topOrsOf w, j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ ¬ reachesInp (27 + j)) ∧
        (∀ x : Fin 26 → Bool, (C.wires (inp x)).getD w false = true ↔
          ∃ j ∈ topAndsOf w, (C.wires (inp x)).getD (27 + j) false = true) ∧
        (∀ u ∈ topAndsOf w ∪ topOrsOf w, 27 + u = w ∨
          ∃ k ∈ topOrsOf w, 27 + u ∈ (gateAt C k).inputs) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt hnri
        by_cases h27 : w < 27
        · have hw26 : w = 26 := by
            by_contra hne; exact hnri (hRI_lt26 w (by omega))
          subst hw26
          have hm0 : maskSet mask = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro u hu; exact hnri (hRI_26.mpr ⟨u, hu⟩)
          rw [hTA_lt27 26 (by omega), hTO_lt27 26 (by omega)]
          refine ⟨fun k hk => by simp at hk, fun k hk => by simp at hk, fun x => ?_, fun u hu => by simp at hu⟩
          change (wF C.gates (inp x)).getD 26 false = true ↔ _
          rw [hWFLt _ _ 26 (by rw [hInpLen]; omega), hInp26 x, hm0]
          simp
        · let j := w - 27
          have hj : j < C.gates.length := by omega
          have hwj : w = 27 + j := by omega
          rw [hwj] at hnri ⊢
          rcases hMonoOps C hM (gateAt C j) (by rw [hGateAtEq C j hj]; exact List.getElem_mem hj) with hop | hop
          · rw [hTA_and j hj hop, hTO_and j hj hop]
            refine ⟨fun k hk => by rw [Finset.mem_singleton.mp hk]; exact ⟨hj, hop⟩,
              fun k hk => by simp at hk,
              fun x => by simp,
              fun u hu => by simp at hu; subst hu; exact Or.inl rfl⟩
          · have hn0 : ¬ reachesInp (in0 j) := fun h => hnri ((hRI_or j hj hop).mpr (Or.inl h))
            have hn1 : ¬ reachesInp (in1 j) := fun h => hnri ((hRI_or j hj hop).mpr (Or.inr h))
            have hlt0 : in0 j < 27 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
            have hlt1 : in1 j < 27 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
            obtain ⟨hA0, hO0, hE0, hP0⟩ := ih (in0 j) (by omega) (by omega) hn0
            obtain ⟨hA1, hO1, hE1, hP1⟩ := ih (in1 j) (by omega) (by omega) hn1
            rw [hTA_or j hj hop, hTO_or j hj hop]
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro k hk
              rcases Finset.mem_union.mp hk with h | h
              · exact hA0 k h
              · exact hA1 k h
            · intro k hk
              rcases Finset.mem_insert.mp hk with rfl | h
              · exact ⟨hj, hop, hnri⟩
              · rcases Finset.mem_union.mp h with h | h
                · exact hO0 k h
                · exact hO1 k h
            · intro x
              rw [show (27 : ℕ) = (inp x).length from (hInpLen x).symm]
              rw [hWireGate C (inp x) j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj]
              simp only [hEvalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false, Bool.or_eq_true, hE0 x, hE1 x, Finset.mem_union]
              constructor
              · rintro (⟨k, hk, ht⟩ | ⟨k, hk, ht⟩)
                · exact ⟨k, Or.inl hk, ht⟩
                · exact ⟨k, Or.inr hk, ht⟩
              · rintro ⟨k, hk | hk, ht⟩
                · exact Or.inl ⟨k, hk, ht⟩
                · exact Or.inr ⟨k, hk, ht⟩
            · intro u hu
              by_cases huj : u = j
              · exact Or.inl (by omega)
              · right
                have hu01 : u ∈ topAndsOf (in0 j) ∪ topOrsOf (in0 j) ∨
                    u ∈ topAndsOf (in1 j) ∪ topOrsOf (in1 j) := by
                  simp only [Finset.mem_union, Finset.mem_insert] at hu ⊢
                  rcases hu with (h | h) | (rfl | h | h)
                  · exact Or.inl (Or.inl h)
                  · exact Or.inr (Or.inl h)
                  · exact absurd rfl huj
                  · exact Or.inl (Or.inr h)
                  · exact Or.inr (Or.inr h)
                rcases hu01 with h0 | h1
                · rcases hP0 u h0 with heq | ⟨k, hk, hkin⟩
                  · exact ⟨j, Finset.mem_insert_self _ _, by rw [hInsEq j hj, heq]; simp⟩
                  · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_left _ hk), hkin⟩
                · rcases hP1 u h1 with heq | ⟨k, hk, hkin⟩
                  · exact ⟨j, Finset.mem_insert_self _ _, by rw [hInsEq j hj, heq]; simp⟩
                  · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_right _ hk), hkin⟩
    let A := topAndsOf C.output
    let T := topOrsOf C.output
    obtain ⟨hA_prop, hT_prop, hOutEval, hTopParent⟩ := hTopProps C.output hOutHi hOutNRI
    have hAT_disj : Disjoint A T := by
      rw [Finset.disjoint_left]
      intro j hjA hjT
      have h1 := (hA_prop j hjA).2
      have h2 := (hT_prop j hjT).2.1
      rw [h1] at h2; exact GateOp.noConfusion h2
    have hA_le_T : A.card ≤ T.card + 1 := by
      by_cases hTe : T = ∅
      · have hA1 : A.card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro u hu v hv
          have hu' : 27 + u = C.output := by
            rcases hTopParent u (Finset.mem_union_left _ hu) with heq | ⟨k, hk, _⟩
            · exact heq
            · change k ∈ T at hk; rw [hTe] at hk; simp at hk
          have hv' : 27 + v = C.output := by
            rcases hTopParent v (Finset.mem_union_left _ hv) with heq | ⟨k, hk, _⟩
            · exact heq
            · change k ∈ T at hk; rw [hTe] at hk; simp at hk
          omega
        omega
      · let outG := C.output - 27
        have houtEq : C.output = 27 + outG := by omega
        have houtLt : outG < C.gates.length := by omega
        have houtMem : outG ∈ A ∪ T := by
          rcases hMonoOps C hM (gateAt C outG) (by rw [hGateAtEq C outG houtLt]; exact List.getElem_mem houtLt) with hop | hop
          · apply Finset.mem_union_left
            change outG ∈ topAndsOf C.output
            rw [houtEq, hTA_and outG houtLt hop]; simp
          · apply Finset.mem_union_right
            change outG ∈ topOrsOf C.output
            rw [houtEq, hTO_or outG houtLt hop]; simp
        let rem := (A ∪ T).erase outG
        have hRemSub : rem.image (· + 27) ⊆ T.biUnion (fun k => (gateAt C k).inputs.toFinset) := by
          intro w hw
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
          have hne : u ≠ outG := (Finset.mem_erase.mp hu).1
          have hum : u ∈ A ∪ T := (Finset.mem_erase.mp hu).2
          rcases hTopParent u hum with heq | ⟨k, hk, hkin⟩
          · exact absurd (by omega) hne
          · exact Finset.mem_biUnion.mpr ⟨k, hk, List.mem_toFinset.mpr (by rwa [Nat.add_comm])⟩
        have hCard1 : rem.card ≤ (T.biUnion (fun k => (gateAt C k).inputs.toFinset)).card := by
          calc rem.card = (rem.image (· + 27)).card :=
                (Finset.card_image_of_injective rem (fun a b h => by omega)).symm
            _ ≤ _ := Finset.card_le_card hRemSub
        have hCard2 : (T.biUnion (fun k => (gateAt C k).inputs.toFinset)).card ≤ 2 * T.card := by
          calc _ ≤ ∑ k ∈ T, ((gateAt C k).inputs.toFinset).card := Finset.card_biUnion_le
            _ ≤ ∑ k ∈ T, 2 := by
                apply Finset.sum_le_sum
                intro k hk
                have hlt := (hT_prop k hk).1
                have h2 : (gateAt C k).inputs.length = 2 := hLen2 _ (by rw [hGateAtEq C k hlt]; exact List.getElem_mem hlt)
                exact (List.toFinset_card_le _).trans (le_of_eq h2)
            _ = 2 * T.card := by simp [Nat.mul_comm]
        have hRemCard : rem.card + 1 = A.card + T.card := by
          rw [Finset.card_erase_add_one houtMem, Finset.card_union_of_disjoint hAT_disj]
        omega
    have hAndChildNE : ∀ j ∈ A, (orVars (in0 j)).Nonempty ∧ (orVars (in1 j)).Nonempty := by
      intro j hjA
      obtain ⟨hj, hop⟩ := hA_prop j hjA
      obtain ⟨haf0, haf1⟩ := hAndChildAF j hj hop
      have hlt0 : in0 j < 27 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
      have hlt1 : in1 j < 27 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
      constructor
      · by_contra hne
        have hemp : orVars (in0 j) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hm0 : maskSet mask = ∅ := hOV_empty_imp (in0 j) (by omega) haf0 hemp
        have heq : ∀ x : Fin 26 → Bool, (C.wires (inp x)).getD (27 + j) false = (C.wires (inp x)).getD 26 false := by
          intro x
          rw [show (27 : ℕ) = (inp x).length from (hInpLen x).symm]
          rw [hWireGate C (inp x) j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj]
          simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
            Bool.and_true, hAF_eval (in0 j) (by omega) haf0 x, hemp]
          change false = (wF C.gates (inp x)).getD 26 false
          rw [hWFLt _ _ 26 (by rw [hInpLen]; omega), hInp26 x, hm0]
          simp
        obtain ⟨C', hG', hlt'⟩ := hErase C ⟨hM, hRB, hPos, hNeg⟩ j 26 hj (by omega) heq
        exact absurd (hMin C' hG') (by omega)
      · by_contra hne
        have hemp : orVars (in1 j) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hm0 : maskSet mask = ∅ := hOV_empty_imp (in1 j) (by omega) haf1 hemp
        have heq : ∀ x : Fin 26 → Bool, (C.wires (inp x)).getD (27 + j) false = (C.wires (inp x)).getD 26 false := by
          intro x
          rw [show (27 : ℕ) = (inp x).length from (hInpLen x).symm]
          rw [hWireGate C (inp x) j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj]
          simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
            Bool.and_true, hAF_eval (in1 j) (by omega) haf1 x, hemp]
          change ((C.wires (inp x)).getD (in0 j) false && false) = (wF C.gates (inp x)).getD 26 false
          rw [Bool.and_false, hWFLt _ _ 26 (by rw [hInpLen]; omega), hInp26 x, hm0]
          simp
        obtain ⟨C', hG', hlt'⟩ := hErase C ⟨hM, hRB, hPos, hNeg⟩ j 26 hj (by omega) heq
        exact absurd (hMin C' hG') (by omega)
    have hAndStar : ∀ j ∈ A,
        (∀ u ∈ orVars (in0 j), ∀ v ∈ orVars (in1 j), adj u v = true) ∧
        ((orVars (in0 j)).card = 1 ∨ (orVars (in1 j)).card = 1) := by
      intro j hjA
      obtain ⟨hj, hop⟩ := hA_prop j hjA
      obtain ⟨haf0, haf1⟩ := hAndChildAF j hj hop
      obtain ⟨hne0, hne1⟩ := hAndChildNE j hjA
      have hlt0 : in0 j < 27 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
      have hlt1 : in1 j < 27 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
      have hadj : ∀ u ∈ orVars (in0 j), ∀ v ∈ orVars (in1 j), adj u v = true := by
        intro u hu v hv
        let x : Fin 26 → Bool := fun w => decide (w = u ∨ w = v)
        have hjT : (C.wires (inp x)).getD (27 + j) false = true := by
          rw [show (27 : ℕ) = (inp x).length from (hInpLen x).symm]
          rw [hWireGate C (inp x) j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj]
          simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true,
            hAF_eval (in0 j) (by omega) haf0 x, hAF_eval (in1 j) (by omega) haf1 x, decide_eq_true_eq]
          exact ⟨⟨u, hu, by simp [x]⟩, ⟨v, hv, by simp [x]⟩⟩
        have houtT : C.eval (inp x) = true := (hOutEval x).mpr ⟨j, hjA, hjT⟩
        rw [hGoodEvalPair C ⟨hM, hRB, hPos, hNeg⟩ u v] at houtT
        exact houtT
      refine ⟨hadj, ?_⟩
      by_contra hboth
      push Not at hboth
      have hc0 : 2 ≤ (orVars (in0 j)).card := by have := hne0.card_pos; omega
      have hc1 : 2 ≤ (orVars (in1 j)).card := by have := hne1.card_pos; omega
      obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp (by omega : 1 < (orVars (in0 j)).card)
      obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < (orVars (in1 j)).card)
      exact hNoC4 u1 u2 v1 v2 hune hvne (hadj u1 hu1 v1 hv1) (hadj u1 hu1 v2 hv2)
        (hadj u2 hu2 v1 hv1) (hadj u2 hu2 v2 hv2)
    let center : ℕ → Fin 26 := fun j =>
      if h : (orVars (in0 j)).Nonempty ∧ (orVars (in0 j)).card = 1 then h.1.choose
      else if h2 : (orVars (in1 j)).Nonempty then h2.choose
      else 0
    let leafWire : ℕ → ℕ := fun j =>
      if (orVars (in0 j)).card = 1 then in1 j else in0 j
    have hStarProp : ∀ j ∈ A,
        andFree (leafWire j) ∧ leafWire j < 27 + C.gates.length ∧
        (∀ v ∈ orVars (leafWire j), adj (center j) v = true) ∧
        (∀ u v : Fin 26,
          (C.wires (inp (fun w => decide (w = u ∨ w = v)))).getD (27 + j) false = true →
          (u = center j ∧ v ∈ orVars (leafWire j)) ∨ (v = center j ∧ u ∈ orVars (leafWire j))) := by
      intro j hjA
      obtain ⟨hj, hop⟩ := hA_prop j hjA
      obtain ⟨haf0, haf1⟩ := hAndChildAF j hj hop
      obtain ⟨hne0, hne1⟩ := hAndChildNE j hjA
      have hlt0 : in0 j < 27 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
      have hlt1 : in1 j < 27 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
      obtain ⟨hadj, hcard⟩ := hAndStar j hjA
      by_cases hc0 : (orVars (in0 j)).card = 1
      · have hcen : center j = hne0.choose := by simp [center, hne0, hc0]
        have hcenMem : center j ∈ orVars (in0 j) := by rw [hcen]; exact hne0.choose_spec
        have hsing : orVars (in0 j) = {center j} := by
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc0
          have : center j = a := Finset.mem_singleton.mp (ha ▸ hcenMem)
          rw [ha, this]
        have hlw : leafWire j = in1 j := by simp [leafWire, hc0]
        refine ⟨by rw [hlw]; exact haf1, by rw [hlw]; omega,
          fun v hv => hadj (center j) hcenMem v (by rw [← hlw]; exact hv), ?_⟩
        intro u v hjT
        rw [show (27 : ℕ) = (inp _).length from (hInpLen _).symm] at hjT
        rw [hWireGate C _ j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj] at hjT
        simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true,
          hAF_eval (in0 j) (by omega) haf0 _, hAF_eval (in1 j) (by omega) haf1 _,
          decide_eq_true_eq, hsing, Finset.mem_singleton] at hjT
        obtain ⟨⟨a, rfl, ha⟩, ⟨b, hb, hbuv⟩⟩ := hjT
        rw [hlw]
        rcases ha with hcu | hcv
        · rcases hbuv with rfl | rfl
          · exfalso; have := hadj (center j) hcenMem (center j) (hcu ▸ hb); rw [hAdjIrrefl] at this; exact Bool.false_ne_true this
          · exact Or.inl ⟨hcu.symm, hb⟩
        · rcases hbuv with rfl | rfl
          · exact Or.inr ⟨hcv.symm, hb⟩
          · exfalso; have := hadj (center j) hcenMem (center j) (hcv ▸ hb); rw [hAdjIrrefl] at this; exact Bool.false_ne_true this
      · have hc1 : (orVars (in1 j)).card = 1 := hcard.resolve_left hc0
        have hcen : center j = hne1.choose := by simp [center, hc0, hne1]
        have hcenMem : center j ∈ orVars (in1 j) := by rw [hcen]; exact hne1.choose_spec
        have hsing : orVars (in1 j) = {center j} := by
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc1
          have : center j = a := Finset.mem_singleton.mp (ha ▸ hcenMem)
          rw [ha, this]
        have hlw : leafWire j = in0 j := by simp [leafWire, hc0]
        refine ⟨by rw [hlw]; exact haf0, by rw [hlw]; omega,
          fun v hv => by rw [hAdjSymm]; exact hadj v (by rw [← hlw]; exact hv) (center j) hcenMem, ?_⟩
        intro u v hjT
        rw [show (27 : ℕ) = (inp _).length from (hInpLen _).symm] at hjT
        rw [hWireGate C _ j (by rw [hInpLen]; exact hRB) hj, hop, hInsEq j hj] at hjT
        simp only [hEvalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true,
          hAF_eval (in0 j) (by omega) haf0 _, hAF_eval (in1 j) (by omega) haf1 _,
          decide_eq_true_eq, hsing, Finset.mem_singleton] at hjT
        obtain ⟨⟨b, hb, hbuv⟩, ⟨a, rfl, ha⟩⟩ := hjT
        rw [hlw]
        rcases ha with hcu | hcv
        · rcases hbuv with rfl | rfl
          · exfalso; have := hadj (center j) (hcu ▸ hb) (center j) hcenMem; rw [hAdjIrrefl] at this; exact Bool.false_ne_true this
          · exact Or.inl ⟨hcu.symm, hb⟩
        · rcases hbuv with rfl | rfl
          · exact Or.inr ⟨hcv.symm, hb⟩
          · exfalso; have := hadj (center j) (hcv ▸ hb) (center j) hcenMem; rw [hAdjIrrefl] at this; exact Bool.false_ne_true this
    have hEdgeCov : ∀ u v : Fin 26, adj u v = true →
        ∃ j ∈ A, (u = center j ∧ v ∈ orVars (leafWire j)) ∨
          (v = center j ∧ u ∈ orVars (leafWire j)) := by
      intro u v huv
      have houtT : C.eval (inp (fun w => decide (w = u ∨ w = v))) = true := by
        rw [hGoodEvalPair C ⟨hM, hRB, hPos, hNeg⟩ u v]; exact huv
      obtain ⟨j, hjA, hjT⟩ := (hOutEval _).mp houtT
      exact ⟨j, hjA, (hStarProp j hjA).2.2.2 u v hjT⟩
    let edges : Finset (Fin 26 × Fin 26) :=
      Finset.univ.filter fun p => p.1 < p.2 ∧ adj p.1 p.2 = true
    have hA_ge_13 : 13 ≤ A.card := by
      let inc : Fin 26 → Finset (Fin 26 × Fin 26) := fun c =>
        edges.filter fun p => p.1 = c ∨ p.2 = c
      have hIncLe : ∀ c : Fin 26, (inc c).card ≤ 4 := by
        intro c
        let otherV : Fin 26 × Fin 26 → Fin 26 := fun p => if p.1 = c then p.2 else p.1
        have hSub : (inc c).image otherV ⊆ Finset.univ.filter fun v : Fin 26 => adj c v = true := by
          intro v hv
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
          simp only [inc, edges, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          obtain ⟨⟨_, hadj⟩, h1 | h2⟩ := hp
          · simp only [otherV, h1, ite_true]; rwa [← h1]
          · have hne : p.1 ≠ c := by intro h; rw [h, h2, hAdjIrrefl] at hadj; exact Bool.false_ne_true hadj
            simp only [otherV, hne, ite_false]; rw [hAdjSymm, ← h2]; exact hadj
        have hInj : Set.InjOn otherV (inc c : Set (Fin 26 × Fin 26)) := by
          intro p hp q hq heq
          simp only [Finset.mem_coe, inc, edges, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
          rcases hp with ⟨⟨hpLt, _⟩, hp1 | hp2⟩
          · rcases hq with ⟨⟨hqLt, _⟩, hq1 | hq2⟩
            · have hpe : otherV p = p.2 := by simp [otherV, hp1]
              have hqe : otherV q = q.2 := by simp [otherV, hq1]
              rw [hpe, hqe] at heq; exact Prod.ext (hp1.trans hq1.symm) heq
            · have hpe : otherV p = p.2 := by simp [otherV, hp1]
              have hne : q.1 ≠ c := ne_of_lt (hq2 ▸ hqLt)
              have hqe : otherV q = q.1 := by simp [otherV, hne]
              rw [hpe, hqe] at heq
              exact absurd (lt_trans (hp1 ▸ hpLt) (heq ▸ hq2 ▸ hqLt)) (lt_irrefl _)
          · rcases hq with ⟨⟨hqLt, _⟩, hq1 | hq2⟩
            · have hne : p.1 ≠ c := ne_of_lt (hp2 ▸ hpLt)
              have hpe : otherV p = p.1 := by simp [otherV, hne]
              have hqe : otherV q = q.2 := by simp [otherV, hq1]
              rw [hpe, hqe] at heq
              exact absurd (lt_trans (hq1 ▸ hqLt) (heq.symm ▸ hp2 ▸ hpLt)) (lt_irrefl _)
            · have hnep : p.1 ≠ c := ne_of_lt (hp2 ▸ hpLt)
              have hneq : q.1 ≠ c := ne_of_lt (hq2 ▸ hqLt)
              have hpe : otherV p = p.1 := by simp [otherV, hnep]
              have hqe : otherV q = q.1 := by simp [otherV, hneq]
              rw [hpe, hqe] at heq; exact Prod.ext heq (hp2.trans hq2.symm)
        calc (inc c).card = ((inc c).image otherV).card := (Finset.card_image_of_injOn hInj).symm
          _ ≤ (Finset.univ.filter fun v : Fin 26 => adj c v = true).card := Finset.card_le_card hSub
          _ = 4 := hDeg4 c
      have hSub : edges ⊆ (A.image center).biUnion inc := by
        intro p hp
        have hadj : adj p.1 p.2 = true := (Finset.mem_filter.mp hp).2.2
        obtain ⟨j, hjA, ⟨h1, _⟩ | ⟨h2, _⟩⟩ := hEdgeCov p.1 p.2 hadj
        · exact Finset.mem_biUnion.mpr ⟨center j, Finset.mem_image_of_mem _ hjA,
            Finset.mem_filter.mpr ⟨hp, Or.inl h1⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨center j, Finset.mem_image_of_mem _ hjA,
            Finset.mem_filter.mpr ⟨hp, Or.inr h2⟩⟩
      have h52 : 52 ≤ 4 * A.card := by
        calc 52 = edges.card := hEdgeCard.symm
          _ ≤ ((A.image center).biUnion inc).card := Finset.card_le_card hSub
          _ ≤ ∑ c ∈ A.image center, (inc c).card := Finset.card_biUnion_le
          _ ≤ ∑ c ∈ A.image center, 4 := Finset.sum_le_sum fun c _ => hIncLe c
          _ = 4 * (A.image center).card := by simp [Nat.mul_comm]
          _ ≤ 4 * A.card := Nat.mul_le_mul_left 4 Finset.card_image_le
      omega
    let orCone : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h27 : w < 27 then ∅
      else if hlt : w < 27 + C.gates.length then
        if (gateAt C (w - 27)).op = GateOp.or then
          insert (w - 27) (
            ih (in0 (w - 27)) (by
              have hj : w - 27 < C.gates.length := by omega
              have := (hInLt (w - 27) hj).1; change _ < w; omega) ∪
            ih (in1 (w - 27)) (by
              have hj : w - 27 < C.gates.length := by omega
              have := (hInLt (w - 27) hj).2; change _ < w; omega))
        else ∅
      else ∅
    let baseIn : ℕ → Finset ℕ := WellFounded.fix Nat.lt_wfRel.wf fun w ih =>
      if h27 : w < 27 then {w}
      else if hlt : w < 27 + C.gates.length then
        if (gateAt C (w - 27)).op = GateOp.or then
          ih (in0 (w - 27)) (by
            have hj : w - 27 < C.gates.length := by omega
            have := (hInLt (w - 27) hj).1; change _ < w; omega) ∪
          ih (in1 (w - 27)) (by
            have hj : w - 27 < C.gates.length := by omega
            have := (hInLt (w - 27) hj).2; change _ < w; omega)
        else ∅
      else ∅
    have hOC_lt27 : ∀ w < 27, orCone w = ∅ := by
      intro w hw; dsimp only [orCone]; rw [WellFounded.fix_eq, dif_pos hw]
    have hOC_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        orCone (27 + j) = insert j (orCone (in0 j) ∪ orCone (in1 j)) := by
      intro j hj hop
      have h1 : ¬ 27 + j < 27 := Nat.not_lt.mpr (Nat.le_add_right 27 j)
      have h2 : 27 + j < 27 + C.gates.length := Nat.add_lt_add_left hj 27
      conv_lhs =>
        dsimp only [orCone]
        rw [WellFounded.fix_eq, dif_neg h1, dif_pos h2]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, ite_true]
      rfl
    have hBI_lt27 : ∀ w < 27, baseIn w = {w} := by
      intro w hw; dsimp only [baseIn]; rw [WellFounded.fix_eq, dif_pos hw]
    have hBI_or : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        baseIn (27 + j) = baseIn (in0 j) ∪ baseIn (in1 j) := by
      intro j hj hop
      have h1 : ¬ 27 + j < 27 := Nat.not_lt.mpr (Nat.le_add_right 27 j)
      have h2 : 27 + j < 27 + C.gates.length := Nat.add_lt_add_left hj 27
      conv_lhs =>
        dsimp only [baseIn]
        rw [WellFounded.fix_eq, dif_neg h1, dif_pos h2]
      dsimp only
      rw [Nat.add_sub_cancel_left]
      simp only [hop, ite_true]
      rfl
    have hBotProps : ∀ w < 27 + C.gates.length, andFree w →
        (∀ k ∈ orCone w, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
          andFree (27 + k) ∧ orVars (27 + k) ⊆ orVars w) ∧
        (∀ i ∈ baseIn w, i < 27) ∧
        (orVars w = (baseIn w).biUnion fun i => orVars i) ∧
        (w ∈ baseIn w ∪ (orCone w).image (· + 27)) ∧
        (∀ u ∈ baseIn w ∪ (orCone w).image (· + 27), u = w ∨
          ∃ k ∈ orCone w, u ∈ (gateAt C k).inputs) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf
        by_cases h27 : w < 27
        · rw [hOC_lt27 w h27, hBI_lt27 w h27]
          refine ⟨fun k hk => by simp at hk, fun i hi => by simp at hi; omega,
            by simp, by simp, fun u hu => by simp at hu; exact Or.inl hu⟩
        · let j := w - 27
          have hj : j < C.gates.length := by omega
          have hwj : w = 27 + j := by omega
          rw [hwj] at haf ⊢
          obtain ⟨hop, haf0, haf1⟩ := (hAF_gate j hj).mp haf
          have hlt0 : in0 j < 27 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
          have hlt1 : in1 j < 27 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
          obtain ⟨hC0, hB0, hV0, hM0, hP0⟩ := ih (in0 j) (by omega) (by omega) haf0
          obtain ⟨hC1, hB1, hV1, hM1, hP1⟩ := ih (in1 j) (by omega) (by omega) haf1
          rw [hOC_or j hj hop, hBI_or j hj hop]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro k hk
            rcases Finset.mem_insert.mp hk with rfl | h
            · exact ⟨hj, hop, haf, Finset.Subset.rfl⟩
            · rcases Finset.mem_union.mp h with h | h
              · obtain ⟨a, b, c, d⟩ := hC0 k h
                exact ⟨a, b, c, d.trans (by rw [hOV_or j hj hop]; exact Finset.subset_union_left)⟩
              · obtain ⟨a, b, c, d⟩ := hC1 k h
                exact ⟨a, b, c, d.trans (by rw [hOV_or j hj hop]; exact Finset.subset_union_right)⟩
          · intro i hi
            rcases Finset.mem_union.mp hi with h | h
            · exact hB0 i h
            · exact hB1 i h
          · rw [hOV_or j hj hop, hV0, hV1, Finset.union_biUnion]
          · apply Finset.mem_union_right
            exact Finset.mem_image.mpr ⟨j, Finset.mem_insert_self _ _, Nat.add_comm j 27⟩
          · intro u hu
            by_cases huj : u = 27 + j
            · exact Or.inl huj
            · right
              have hu01 : u ∈ baseIn (in0 j) ∪ (orCone (in0 j)).image (· + 27) ∨
                  u ∈ baseIn (in1 j) ∪ (orCone (in1 j)).image (· + 27) := by
                simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert] at hu ⊢
                rcases hu with (h | h) | ⟨k, rfl | h | h, rfl⟩
                · exact Or.inl (Or.inl h)
                · exact Or.inr (Or.inl h)
                · exact absurd (Nat.add_comm j 27) huj
                · exact Or.inl (Or.inr ⟨k, h, rfl⟩)
                · exact Or.inr (Or.inr ⟨k, h, rfl⟩)
              rcases hu01 with h0 | h1
              · rcases hP0 u h0 with rfl | ⟨k, hk, hkin⟩
                · exact ⟨j, Finset.mem_insert_self _ _, by rw [hInsEq j hj]; simp⟩
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_left _ hk), hkin⟩
              · rcases hP1 u h1 with rfl | ⟨k, hk, hkin⟩
                · exact ⟨j, Finset.mem_insert_self _ _, by rw [hInsEq j hj]; simp⟩
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_right _ hk), hkin⟩
    let Ac : Fin 26 → Finset ℕ := fun c => A.filter (fun j => center j = c)
    let Bc : Fin 26 → Finset ℕ := fun c => (Ac c).biUnion (fun j => orCone (leafWire j))
    let Ic : Fin 26 → Finset ℕ := fun c => (Ac c).biUnion (fun j => baseIn (leafWire j))
    let Ec : Fin 26 → Finset (Fin 26) := fun c => (Ac c).biUnion (fun j => orVars (leafWire j))
    have hAF_reaches : ∀ w < 27 + C.gates.length, andFree w → (orVars w).Nonempty → reachesInp w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwLt haf hne
        by_cases h26 : w < 26
        · exact hRI_lt26 w h26
        · by_cases hw26 : w = 26
          · subst hw26; rw [hOV_26] at hne; exact hRI_26.mpr hne
          · let j := w - 27
            have hj : j < C.gates.length := by omega
            have hwj : w = 27 + j := by omega
            rw [hwj] at haf hne ⊢
            obtain ⟨hop, haf0, haf1⟩ := (hAF_gate j hj).mp haf
            rw [hOV_or j hj hop] at hne
            have hlt0 : in0 j < 27 + j := hRB j hj (in0 j) (by rw [hInsEq j hj]; simp)
            have hlt1 : in1 j < 27 + j := hRB j hj (in1 j) (by rw [hInsEq j hj]; simp)
            obtain ⟨u, hu⟩ := hne
            rcases Finset.mem_union.mp hu with hu0 | hu1
            · exact (hRI_or j hj hop).mpr (Or.inl (ih (in0 j) (by omega) (by omega) haf0 ⟨u, hu0⟩))
            · exact (hRI_or j hj hop).mpr (Or.inr (ih (in1 j) (by omega) (by omega) haf1 ⟨u, hu1⟩))
    have hBc_props : ∀ c : Fin 26, ∀ k ∈ Bc c,
        k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ andFree (27 + k) ∧
        (∀ v ∈ orVars (27 + k), adj c v = true) := by
      intro c k hk
      obtain ⟨j, hjAc, hkj⟩ := Finset.mem_biUnion.mp hk
      obtain ⟨hjA, hcen⟩ := Finset.mem_filter.mp hjAc
      obtain ⟨haf, hlt, hadj, _⟩ := hStarProp j hjA
      obtain ⟨hkLt, hkop, hkAF, hkSub⟩ := (hBotProps (leafWire j) hlt haf).1 k hkj
      exact ⟨hkLt, hkop, hkAF, fun v hv => hcen ▸ hadj v (hkSub hv)⟩
    have hBc_disj : ∀ c1 c2 : Fin 26, c1 ≠ c2 → Disjoint (Bc c1) (Bc c2) := by
      intro c1 c2 hne
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      obtain ⟨hkLt, _, hkAF, hadj1⟩ := hBc_props c1 k hk1
      obtain ⟨_, _, _, hadj2⟩ := hBc_props c2 k hk2
      have hge2 := hAF_card_ge_2 k hkLt hkAF
      obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < (orVars (27 + k)).card)
      exact hNoC4 c1 c2 v1 v2 hne hvne (hadj1 v1 hv1) (hadj1 v2 hv2) (hadj2 v1 hv1) (hadj2 v2 hv2)
    let Ball := Finset.univ.biUnion Bc
    have hBall_sub : Ball ⊆ Finset.range C.gates.length := by
      intro k hk
      obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hk
      exact Finset.mem_range.mpr (hBc_props c k hkc).1
    have hBall_disj_A : Disjoint Ball A := by
      rw [Finset.disjoint_left]
      intro k hkB hkA
      obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hkB
      have h1 := (hBc_props c k hkc).2.1
      have h2 := (hA_prop k hkA).2
      rw [h1] at h2; exact GateOp.noConfusion h2
    have hBall_disj_T : Disjoint Ball T := by
      rw [Finset.disjoint_left]
      intro k hkB hkT
      obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hkB
      obtain ⟨hkLt, _, hkAF, _⟩ := hBc_props c k hkc
      have hne : (orVars (27 + k)).Nonempty := Finset.card_pos.mp (by have := hAF_card_ge_2 k hkLt hkAF; omega)
      exact (hT_prop k hkT).2.2 (hAF_reaches (27 + k) (by omega) hkAF hne)
    have hIc_bound : ∀ c : Fin 26, (Ic c).card ≤ (Bc c).card + (Ac c).card := by
      intro c
      let R : Finset ℕ := (Ac c).image leafWire
      have hRcard : R.card ≤ (Ac c).card := Finset.card_image_le
      let Wc : Finset ℕ := Ic c ∪ (Bc c).image (· + 27)
      have hIcDisj : Disjoint (Ic c) ((Bc c).image (· + 27)) := by
        rw [Finset.disjoint_left]
        intro u hu1 hu2
        obtain ⟨j, hjAc, huj⟩ := Finset.mem_biUnion.mp hu1
        obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
        obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
        have huLt := (hBotProps (leafWire j) hlt haf).2.1 u huj
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu2
        omega
      have hWcCard : Wc.card = (Ic c).card + (Bc c).card := by
        rw [Finset.card_union_of_disjoint hIcDisj,
          Finset.card_image_of_injective _ (fun a b h => by omega)]
      have hSub : Wc \ R ⊆ (Bc c).biUnion (fun k => (gateAt C k).inputs.toFinset) := by
        intro u hu
        have hnotR : u ∉ R := (Finset.mem_sdiff.mp hu).2
        rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hu).1 with huI | huG
        · obtain ⟨j, hjAc, huij⟩ := Finset.mem_biUnion.mp huI
          obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
          rcases (hBotProps (leafWire j) hlt haf).2.2.2.2 u (Finset.mem_union_left _ huij) with rfl | ⟨k, hk, hkin⟩
          · exact absurd (Finset.mem_image_of_mem leafWire hjAc) hnotR
          · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_biUnion.mpr ⟨j, hjAc, hk⟩, List.mem_toFinset.mpr hkin⟩
        · obtain ⟨k0, hk0, rfl⟩ := Finset.mem_image.mp huG
          obtain ⟨j, hjAc, hkj⟩ := Finset.mem_biUnion.mp hk0
          obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
          rcases (hBotProps (leafWire j) hlt haf).2.2.2.2 (k0 + 27)
              (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hkj)) with heq | ⟨k, hk, hkin⟩
          · exact absurd (heq ▸ Finset.mem_image_of_mem leafWire hjAc) hnotR
          · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_biUnion.mpr ⟨j, hjAc, hk⟩, List.mem_toFinset.mpr hkin⟩
      have hDiffLe : (Wc \ R).card ≤ 2 * (Bc c).card := by
        calc (Wc \ R).card ≤ ((Bc c).biUnion (fun k => (gateAt C k).inputs.toFinset)).card := Finset.card_le_card hSub
          _ ≤ ∑ k ∈ Bc c, ((gateAt C k).inputs.toFinset).card := Finset.card_biUnion_le
          _ ≤ ∑ k ∈ Bc c, 2 := by
              apply Finset.sum_le_sum
              intro k hk
              have hkLt := (hBc_props c k hk).1
              have h2 : (gateAt C k).inputs.length = 2 := hLen2 _ (by rw [hGateAtEq C k hkLt]; exact List.getElem_mem hkLt)
              exact (List.toFinset_card_le _).trans (le_of_eq h2)
          _ = 2 * (Bc c).card := by simp [Nat.mul_comm]
      have hWcLe : Wc.card ≤ (Wc \ R).card + R.card := by
        have h1 : Wc ⊆ (Wc \ R) ∪ R := fun x hx => by
          by_cases hxR : x ∈ R
          · exact Finset.mem_union_right _ hxR
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxR⟩)
        exact (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
      omega
    let bonusC : Finset (Fin 26) :=
      Finset.univ.filter fun c : Fin 26 => (maskSet mask).card = 2 ∧ ∀ v ∈ maskSet mask, adj c v = true
    have hBonusCard : bonusC.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro c1 hc1 c2 hc2
      by_contra hne
      simp only [bonusC, Finset.mem_filter, Finset.mem_univ, true_and] at hc1 hc2
      obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < (maskSet mask).card)
      exact hNoC4 c1 c2 v1 v2 hne hvne (hc1.2 v1 hv1) (hc1.2 v2 hv2) (hc2.2 v1 hv1) (hc2.2 v2 hv2)
    have hEc_bound : ∀ c : Fin 26, (Ec c).card ≤ (Ic c).card + (if c ∈ bonusC then 1 else 0) := by
      intro c
      have hEq : Ec c = (Ic c).biUnion orVars := by
        ext v
        simp only [Ec, Ic, Finset.mem_biUnion]
        constructor
        · rintro ⟨j, hjAc, hv⟩
          obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
          rw [(hBotProps (leafWire j) hlt haf).2.2.1] at hv
          obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
          exact ⟨i, ⟨j, hjAc, hi⟩, hvi⟩
        · rintro ⟨i, ⟨j, hjAc, hi⟩, hvi⟩
          obtain ⟨hjA, _⟩ := Finset.mem_filter.mp hjAc
          obtain ⟨haf, hlt, _, _⟩ := hStarProp j hjA
          exact ⟨j, hjAc, by rw [(hBotProps (leafWire j) hlt haf).2.2.1]; exact Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩⟩
      rw [hEq]
      have hSumLe : ((Ic c).biUnion orVars).card ≤ ∑ i ∈ Ic c, (orVars i).card := Finset.card_biUnion_le
      have hEach : ∀ i ∈ Ic c, (orVars i).card ≤ 1 + (if i = 26 ∧ c ∈ bonusC then 1 else 0) := by
        intro i hi
        obtain ⟨j, hjAc, hij⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨hjA, hcen⟩ := Finset.mem_filter.mp hjAc
        obtain ⟨haf, hlt, hadj, _⟩ := hStarProp j hjA
        have hiLt : i < 27 := (hBotProps (leafWire j) hlt haf).2.1 i hij
        by_cases h26 : i = 26
        · subst h26
          rw [hOV_26]
          by_cases hcard2 : (maskSet mask).card = 2
          · have hAdjAll : ∀ v ∈ maskSet mask, adj c v = true := by
              intro v hv
              have hvIn : v ∈ orVars (leafWire j) := by
                rw [(hBotProps (leafWire j) hlt haf).2.2.1]
                exact Finset.mem_biUnion.mpr ⟨26, hij, by rwa [hOV_26]⟩
              exact hcen ▸ hadj v hvIn
            have hmemB : c ∈ bonusC := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard2, hAdjAll⟩
            rw [if_pos ⟨rfl, hmemB⟩]; omega
          · omega
        · have hi26 : i < 26 := by omega
          rw [show i = (⟨i, hi26⟩ : Fin 26).val from rfl, hOV_lt26]
          simp
      have hSum2 : ∑ i ∈ Ic c, (orVars i).card ≤ (Ic c).card + (if c ∈ bonusC then 1 else 0) := by
        calc ∑ i ∈ Ic c, (orVars i).card
            ≤ ∑ i ∈ Ic c, (1 + (if i = 26 ∧ c ∈ bonusC then 1 else 0)) := Finset.sum_le_sum hEach
          _ = (Ic c).card + ∑ i ∈ Ic c, (if i = 26 ∧ c ∈ bonusC then 1 else 0) := by
              rw [Finset.sum_add_distrib]; simp
          _ ≤ (Ic c).card + (if c ∈ bonusC then 1 else 0) := by
              apply Nat.add_le_add_left
              by_cases hcB : c ∈ bonusC
              · rw [if_pos hcB]
                calc ∑ i ∈ Ic c, (if i = 26 ∧ c ∈ bonusC then 1 else 0)
                    = ∑ i ∈ Ic c, (if i = 26 then 1 else 0) := by
                        apply Finset.sum_congr rfl; intro i _; simp [hcB]
                  _ ≤ 1 := by
                      rw [Finset.sum_ite_eq']
                      split_ifs <;> omega
              · rw [if_neg hcB]
                have : ∀ i ∈ Ic c, (if i = 26 ∧ c ∈ bonusC then 1 else 0) = 0 := by
                  intro i _; simp [hcB]
                rw [Finset.sum_eq_zero this]
      exact hSumLe.trans hSum2
    have hSumEc : 52 ≤ ∑ c : Fin 26, (Ec c).card := by
      let covPairs : Finset (Σ c : Fin 26, Fin 26) := Finset.univ.sigma Ec
      have hCovCard : covPairs.card = ∑ c : Fin 26, (Ec c).card := Finset.card_sigma Finset.univ Ec
      let toEdge : (Σ _ : Fin 26, Fin 26) → Fin 26 × Fin 26 := fun x =>
        if x.1 < x.2 then (x.1, x.2) else (x.2, x.1)
      have hSub : edges ⊆ covPairs.image toEdge := by
        intro p hp
        obtain ⟨hlt, hadj⟩ := (Finset.mem_filter.mp hp).2
        obtain ⟨j, hjA, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hEdgeCov p.1 p.2 hadj
        · apply Finset.mem_image.mpr
          refine ⟨⟨p.1, p.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjA, h1.symm⟩, h2⟩
          · simp [toEdge, hlt]
        · apply Finset.mem_image.mpr
          refine ⟨⟨p.2, p.1⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjA, h1.symm⟩, h2⟩
          · have hnot : ¬ (p.2 < p.1) := not_lt.mpr (le_of_lt hlt)
            simp [toEdge, hnot]
      rw [← hCovCard, ← hEdgeCard]
      exact (Finset.card_le_card hSub).trans Finset.card_image_le
    have hSumAc : ∑ c : Fin 26, (Ac c).card = A.card := by
      have hPart : Finset.univ.biUnion Ac = A := by
        ext j
        simp only [Ac, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
        exact ⟨fun h => by obtain ⟨_, hj, _⟩ := h; exact hj, fun h => ⟨center j, h, rfl⟩⟩
      rw [← hPart, Finset.card_biUnion]
      intro c1 _ c2 _ hne
      change Disjoint (Ac c1) (Ac c2)
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      exact hne ((Finset.mem_filter.mp hj1).2.symm.trans (Finset.mem_filter.mp hj2).2)
    have hSumBc : ∑ c : Fin 26, (Bc c).card = Ball.card := by
      rw [Finset.card_biUnion]
      intro c1 _ c2 _ hne
      exact hBc_disj c1 c2 hne
    have hStep1 : 52 ≤ Ball.card + A.card + 1 := by
      calc 52 ≤ ∑ c : Fin 26, (Ec c).card := hSumEc
        _ ≤ ∑ c : Fin 26, ((Ic c).card + (if c ∈ bonusC then 1 else 0)) :=
            Finset.sum_le_sum fun c _ => hEc_bound c
        _ = (∑ c : Fin 26, (Ic c).card) + bonusC.card := by
            rw [Finset.sum_add_distrib]
            simp [Finset.sum_boole]
        _ ≤ (∑ c : Fin 26, ((Bc c).card + (Ac c).card)) + 1 :=
            Nat.add_le_add (Finset.sum_le_sum fun c _ => hIc_bound c) hBonusCard
        _ = Ball.card + A.card + 1 := by
            rw [Finset.sum_add_distrib, hSumBc, hSumAc]
    have hAllSub : Ball ∪ A ∪ T ⊆ Finset.range C.gates.length := by
      intro k hk
      rcases Finset.mem_union.mp hk with hk1 | hkT
      · rcases Finset.mem_union.mp hk1 with hkB | hkA
        · exact hBall_sub hkB
        · exact Finset.mem_range.mpr (hA_prop k hkA).1
      · exact Finset.mem_range.mpr (hT_prop k hkT).1
    have hCardAll : (Ball ∪ A ∪ T).card = Ball.card + A.card + T.card := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hBall_disj_T, hAT_disj⟩),
        Finset.card_union_of_disjoint hBall_disj_A]
    have hSizeGe : Ball.card + A.card + T.card ≤ C.size := by
      have := Finset.card_le_card hAllSub
      rw [hCardAll, Finset.card_range] at this
      exact this
    omega
  · by_cases hAP1 : andPairs 27 C = 1
    · apply h_one C mask hMask hAO2 hAP1
      refine ⟨fun p l hpl => ?_, fun Q hQ1 hQ2 => ?_⟩
      · convert hPos p l hpl using 2
      · convert hNeg Q hQ1 (by intro l; convert hQ2 l) using 2
    · apply h_ge_two C mask hMask hAO2 (by omega)
      refine ⟨fun p l hpl => ?_, fun Q hQ1 hQ2 => ?_⟩
      · convert hPos p l hpl using 2
      · convert hNeg Q hQ1 (by intro l; convert hQ2 l) using 2
