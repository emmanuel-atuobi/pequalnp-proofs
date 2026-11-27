import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5066_1
    (hIrred :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ u : Fin n, (u, u) ∈ E) →
        (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + n) C →
        (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C x =
          Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ C.size ∧
          PEqualNP.TopForm.IsAO2 (n + n) D ∧
          (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x =
            Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) ∧
          (∀ g ∈ D.gates, g.inputs.Nodup) ∧
          (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (n + n) → Bool,
            (D.wires (List.ofFn x)).getD (n + n + i.val) Bool.false ≠
            (D.wires (List.ofFn x)).getD (n + n + j.val) Bool.false))
    (hCover :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ u : Fin n, (u, u) ∈ E) →
        ((∀ u : Fin n, ∃ v : Fin n, v ≠ u ∧ (u, v) ∈ E) ∧ ∀ v : Fin n, ∃ u : Fin n, u ≠ v ∧ (u, v) ∈ E) →
        (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + n) D →
        (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x =
          Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (n + n) → Bool,
          (D.wires (List.ofFn x)).getD (n + n + i.val) Bool.false ≠
          (D.wires (List.ofFn x)).getD (n + n + j.val) Bool.false) →
        ∃ (L R : Finset (Fin n)), (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ D.size + 1) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x12 ≠ x3 x11 ∧ (x11, x12) ∈ x2) ∧ ∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x3 x12 ≠ x11 ∧ (x12, x11) ∈ x2) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  intro n E p C _ _ hc4 hmatch hAO hfun hdeg
  let E' : Finset (Fin n × Fin n) := E.image (fun e => (e.1, p.symm e.2))
  have hE'_card : E'.card = E.card := by
    apply Finset.card_image_of_injective
    intro e1 e2 heq
    have h1 : e1.1 = e2.1 := (Prod.mk.inj heq).1
    have h2 : p.symm e1.2 = p.symm e2.2 := (Prod.mk.inj heq).2
    exact Prod.ext h1 (p.symm.injective h2)
  have hE'_mem : ∀ u v : Fin n, (u, v) ∈ E' ↔ (u, p v) ∈ E := by
    intro u v
    simp only [E', Finset.mem_image]
    constructor
    · rintro ⟨⟨a, b⟩, hab, heq⟩
      have h1 : a = u := congrArg Prod.fst heq
      have h2 : p.symm b = v := congrArg Prod.snd heq
      subst h1
      have hb : b = p v := by rw [← h2, Equiv.apply_symm_apply]
      subst hb
      exact hab
    · intro huv
      exact ⟨(u, p v), huv, by simp⟩
  have hE'_id : ∀ u : Fin n, (u, u) ∈ E' := fun u => (hE'_mem u u).mpr (hmatch u)
  have hE'_c4 : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
      ¬((a, c) ∈ E' ∧ (a, d) ∈ E' ∧ (b, c) ∈ E' ∧ (b, d) ∈ E') := by
    intro a b c d hab hcd h
    simp only [hE'_mem] at h
    exact hc4 a b (p c) (p d) hab (fun heq => hcd (p.injective heq)) h
  have hE'_deg : (∀ u : Fin n, ∃ v : Fin n, v ≠ u ∧ (u, v) ∈ E') ∧
      ∀ v : Fin n, ∃ u : Fin n, u ≠ v ∧ (u, v) ∈ E' := by
    constructor
    · intro u
      obtain ⟨w, hwu, huw⟩ := hdeg.1 u
      refine ⟨p.symm w, fun heq => hwu (by rw [← heq, Equiv.apply_symm_apply]), ?_⟩
      rw [hE'_mem, Equiv.apply_symm_apply]
      exact huw
    · intro v
      obtain ⟨u, huv, huvE⟩ := hdeg.2 (p v)
      refine ⟨u, fun heq => huv (by rw [heq]), (hE'_mem u v).mpr huvE⟩
  let remap : ℕ → ℕ := fun w =>
    if h : n ≤ w ∧ w < n + n then n + (p.symm ⟨w - n, by omega⟩).val else w
  have hremap_lt : ∀ w j : ℕ, w < n + n + j → remap w < n + n + j := by
    intro w j hw
    dsimp only [remap]
    split_ifs with h
    · have := (p.symm ⟨w - n, by omega⟩).isLt
      omega
    · exact hw
  have hremap_ge : ∀ w : ℕ, n + n ≤ w → remap w = w := by
    intro w hw
    dsimp only [remap]
    split_ifs with h
    · omega
    · rfl
  let C' : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := C.gates.map (fun g => ⟨g.op, g.inputs.map remap⟩)
      output := remap C.output }
  have hC'_size : C'.size = C.size := List.length_map _
  have hC'_AO : PEqualNP.TopForm.IsAO2 (n + n) C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact hAO.1 g0 hg0
    · intro j hj i hi
      simp only [C', List.length_map] at hj
      have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
          ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C j).op,
           (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map remap⟩ := by
        change (C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map remap } : PEqualNP.CircuitLowerBounds.Gate))).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
          ⟨(C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op,
           (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.map remap⟩
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hj]
        rfl
      rw [hgate] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      exact hremap_lt i0 j (hAO.2.1 j hj i0 hi0)
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      simpa using hAO.2.2 g0 hg0
  have hC'_fun : ∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C' x =
      Decidable.decide (∃ u v : Fin n, (u, v) ∈ E' ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true) := by
    intro x
    let y : Fin (n + n) → Bool := fun i =>
      if h : i.val < n then x (Fin.castAdd n ⟨i.val, h⟩)
      else x (Fin.natAdd n (p.symm ⟨i.val - n, by omega⟩))
    have hstep : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : List Bool),
        a.length = b.length → n + n ≤ a.length →
        (∀ w : ℕ, a.getD (remap w) false = b.getD w false) →
        let a' := (gs.map (fun g => ({ op := g.op, inputs := g.inputs.map remap } : PEqualNP.CircuitLowerBounds.Gate))).foldl
          (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) a
        let b' := gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) b
        a'.length = b'.length ∧ n + n ≤ a'.length ∧ ∀ w : ℕ, a'.getD (remap w) false = b'.getD w false := by
      intro gs
      induction gs with
      | nil =>
        intro a b hlen hge hget
        exact ⟨hlen, hge, hget⟩
      | cons g rest ih =>
        intro a b hlen hge hget
        simp only [List.map_cons, List.foldl_cons]
        have heval : g.op.eval ((g.inputs.map remap).map fun i => a.getD i false) =
            g.op.eval (g.inputs.map fun i => b.getD i false) := by
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro w _
          exact hget w
        rw [heval]
        let v := g.op.eval (g.inputs.map fun i => b.getD i false)
        apply ih (a ++ [v]) (b ++ [v])
        · simp [hlen]
        · simp; omega
        · intro w
          by_cases hw : w < a.length
          · have hrw : remap w < a.length := by
              dsimp only [remap]
              split_ifs with h
              · have := (p.symm ⟨w - n, by omega⟩).isLt; omega
              · exact hw
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hrw,
              List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
            exact hget w
          · have hge_w : n + n ≤ w := by omega
            rw [hremap_ge w hge_w, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
              List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
    have hbase_get : ∀ w : ℕ, (List.ofFn x).getD (remap w) false = (List.ofFn y).getD w false := by
      intro w
      by_cases hw1 : w < n
      · have hr : remap w = w := by dsimp only [remap]; split_ifs with h; omega; rfl
        have hw : w < n + n := by omega
        rw [hr, List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hw, ↓reduceDIte, Option.getD_some, y, hw1]
        congr 1
      · by_cases hw2 : w < n + n
        · have hr : remap w = n + (p.symm ⟨w - n, by omega⟩).val := by
            dsimp only [remap]
            have hcond : n ≤ w ∧ w < n + n := ⟨by omega, hw2⟩
            simp only [hcond, and_self, ↓reduceDIte]
          have hrl : n + (p.symm ⟨w - n, by omega⟩).val < n + n := by
            have := (p.symm ⟨w - n, by omega⟩).isLt; omega
          rw [hr, List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [hrl, hw2, ↓reduceDIte, Option.getD_some, y, hw1]
          congr 1
        · have hr : remap w = w := hremap_ge w (by omega)
          rw [hr, List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [hw2, ↓reduceDIte, Option.getD_none]
    have hrun := hstep C.gates (List.ofFn x) (List.ofFn y) (by simp) (by simp) hbase_get
    have heval_eq : PEqualNP.MetaComplexity.circuitFun (n + n) C' x = PEqualNP.MetaComplexity.circuitFun (n + n) C y := by
      exact hrun.2.2 C.output
    rw [heval_eq, hfun y]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨u, v, huv, hyu, hyv⟩
      refine ⟨u, p.symm v, ?_, ?_, ?_⟩
      · rw [hE'_mem, Equiv.apply_symm_apply]; exact huv
      · simpa [y, u.isLt] using hyu
      · have hnot : ¬ (n + v.val < n) := by omega
        have hsub : n + v.val - n = v.val := by omega
        simpa [y, Fin.natAdd, hnot, hsub] using hyv
    · rintro ⟨u, v, huv, hxu, hxv⟩
      refine ⟨u, p v, (hE'_mem u v).mp huv, ?_, ?_⟩
      · simpa [y, u.isLt] using hxu
      · have hnot : ¬ (n + (p v).val < n) := by omega
        have hsub : n + (p v).val - n = (p v).val := by omega
        simpa [y, Fin.natAdd, hnot, hsub] using hxv
  obtain ⟨D, hDle, hDAO, hDfun, hDnd, hDdist⟩ := hIrred n E' C' hE'_id hE'_c4 hC'_AO hC'_fun
  obtain ⟨L, R, hcov, hbound⟩ := hCover n E' D hE'_id hE'_deg hE'_c4 hDAO hDfun hDnd hDdist
  have hkonig : n ≤ L.card + R.card := by
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ L ∪ R := by
      intro u _
      rw [Finset.mem_union]
      exact hcov (u, u) (hE'_id u)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    exact le_trans hcard (Finset.card_union_le L R)
  omega
