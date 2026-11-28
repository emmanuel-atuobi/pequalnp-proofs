import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5326_2
    (hRawCenter :
      ∃ (k : ℕ),
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
          (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) →
          PEqualNP.TopForm.IsLeastAO G C →
          PEqualNP.TopForm.TopForm G C →
          {e ∈ PEqualNP.TopForm.Ustar G C |
            ∃ (u v : Fin n), e = s(u, v) ∧
            ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ (b : Fin (2 : ℕ)),
              (∀ (w : Fin n), PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a b) (PEqualNP.EdgeOwnership.pairInput w w) = Bool.true ↔ w = u) ∧
              PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a ((1 : Fin (2 : ℕ)) - b)) (PEqualNP.EdgeOwnership.pairInput v v) = Bool.true ∧
              u ∈ PEqualNP.TopForm.side C a b ∧
              v ∉ PEqualNP.TopForm.side C a ((1 : Fin (2 : ℕ)) - b)}.card ≤ k * (C.size + (1 : ℕ)))
    (hNonRawCenter :
      ∃ (k : ℕ),
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
          (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) →
          PEqualNP.TopForm.IsLeastAO G C →
          PEqualNP.TopForm.TopForm G C →
          {e ∈ PEqualNP.TopForm.Ustar G C |
            ∃ (u v : Fin n), e = s(u, v) ∧
            ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ (b : Fin (2 : ℕ)),
              (∀ (w : Fin n), PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a b) (PEqualNP.EdgeOwnership.pairInput w w) = Bool.true ↔ w = u) ∧
              PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a ((1 : Fin (2 : ℕ)) - b)) (PEqualNP.EdgeOwnership.pairInput v v) = Bool.true ∧
              u ∉ PEqualNP.TopForm.side C a b}.card ≤ k * (C.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, PEqualNP.CleanedNonEdge.wireVal x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.true ∧ PEqualNP.CleanedNonEdge.wireVal x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k1, hk1⟩ := hRawCenter
  obtain ⟨k2, hk2⟩ := hNonRawCenter
  refine ⟨k1 + k2, ?_⟩
  intro n G _ C hGirth hLeast hTF
  have hB1 := @hk1 n G _ C hGirth hLeast hTF
  have hB2 := @hk2 n G _ C hGirth hLeast hTF
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hStepLen : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate), (step w g).length = w.length + 1 := by
    intro w g
    change (w ++ [_]).length = w.length + 1
    rw [List.length_append, List.length_singleton]
  have hLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, hStepLen, List.length_cons]
      omega
  have hPref : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length + gs.length → ((gs ++ hs).foldl step w).getD i false = (gs.foldl step w).getD i false := by
    intro gs hs w i hi
    induction hs using List.reverseRecOn with
    | nil => simp
    | append_singleton hs g ih =>
      rw [← List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hl : ((gs ++ hs).foldl step w).length = w.length + (gs ++ hs).length := hLen (gs ++ hs) w
      change (((gs ++ hs).foldl step w) ++ [_]).getD i false = _
      rw [List.getD_append _ _ _ _ (by rw [hl, List.length_append]; omega)]
      exact ih
  have hGateEval : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length),
      (gs.foldl step w).getD (w.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => if i < w.length + k then (gs.foldl step w).getD i false else false) := by
    intro gs w
    induction gs using List.reverseRecOn with
    | nil => intro k hk; simp at hk
    | append_singleton gs g ih =>
      intro k hk
      have hl : (gs.foldl step w).length = w.length + gs.length := hLen gs w
      have hsame : ∀ (m : ℕ), m ≤ gs.length → ∀ l : List ℕ,
          (l.map fun i => if i < w.length + m then ((gs ++ [g]).foldl step w).getD i false else false) =
          l.map fun i => if i < w.length + m then (gs.foldl step w).getD i false else false := by
        intro m hm l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · exact hPref gs [g] w i (by omega)
        · rfl
      rcases Nat.lt_or_ge k gs.length with hlt | hge
      · rw [List.getElem_append_left hlt, hsame k (by omega), hPref gs [g] w _ (by omega)]
        exact ih k hlt
      · have hkk : k = gs.length := by simp only [List.length_append, List.length_singleton] at hk; omega
        subst hkk
        have hg' : (gs ++ [g])[gs.length] = g := by simp
        rw [hg', hsame _ le_rfl, List.foldl_append, List.foldl_cons, List.foldl_nil]
        change ((gs.foldl step w) ++ [_]).getD (w.length + gs.length) false = _
        rw [← hl, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hOpMono : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (l1 l2 : List Bool),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      l1.length = 2 → l2.length = 2 →
      (∀ i, l1.getD i false = true → l2.getD i false = true) →
      op.eval l1 = true → op.eval l2 = true := by
    intro op l1 l2 hop hl1 hl2 hle h1
    rcases l1 with _ | ⟨a1, t1⟩
    · simp at hl1
    · rcases t1 with _ | ⟨b1, t1'⟩
      · simp at hl1
      · rcases t1' with _ | ⟨_, _⟩
        · rcases l2 with _ | ⟨a2, t2⟩
          · simp at hl2
          · rcases t2 with _ | ⟨b2, t2'⟩
            · simp at hl2
            · rcases t2' with _ | ⟨_, _⟩
              · have ha : a1 = true → a2 = true := hle 0
                have hb : b1 = true → b2 = true := hle 1
                rcases hop with rfl | rfl <;> cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;>
                  first | rfl | exact Bool.noConfusion h1 | exact Bool.noConfusion (ha rfl) | exact Bool.noConfusion (hb rfl)
              · simp at hl2
        · simp at hl1
  have hMonoFold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl step w1).getD i false = true → (gs.foldl step w2).getD i false = true := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro _ w1 w2 _ hle i hi; exact hle i hi
    | append_singleton gs g ih =>
      intro hAO w1 w2 hwl hle i hi
      have hAOpre : ∀ h ∈ gs, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ h.inputs.length = 2 :=
        fun h hh => hAO h (List.mem_append_left [g] hh)
      have hAOg := hAO g (List.mem_append_right gs List.mem_cons_self)
      have ih' := ih hAOpre w1 w2 hwl hle
      have hl1 : (gs.foldl step w1).length = w1.length + gs.length := hLen gs w1
      have hl2 : (gs.foldl step w2).length = w2.length + gs.length := hLen gs w2
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hi ⊢
      change ((gs.foldl step w1) ++ [_]).getD i false = true at hi
      change ((gs.foldl step w2) ++ [_]).getD i false = true
      rcases Nat.lt_or_ge i (gs.foldl step w1).length with hlt | hge
      · rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact ih' i hi
      · rcases Nat.eq_or_lt_of_le hge with heq | hgt
        · rw [← heq, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at hi
          have h2eq : (gs.foldl step w2).length = i := by omega
          rw [← h2eq, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          refine hOpMono g.op _ _ hAOg.1 (by simp only [List.length_map]; exact hAOg.2) (by simp only [List.length_map]; exact hAOg.2) ?_ hi
          intro idx hidx
          rcases Nat.lt_or_ge idx g.inputs.length with hidxLt | hidxGe
          · rw [List.getD_eq_getElem _ _ (by simp only [List.length_map]; exact hidxLt), List.getElem_map] at hidx
            rw [List.getD_eq_getElem _ _ (by simp only [List.length_map]; exact hidxLt), List.getElem_map]
            exact ih' g.inputs[idx] hidx
          · rw [List.getD_eq_default _ _ (by simp only [List.length_map]; exact hidxGe)] at hidx
            exact Bool.noConfusion hidx
        · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)] at hi
          exact Bool.noConfusion hi
  have hWireMono : ∀ (w : ℕ) (x y : Fin n → Bool),
      (∀ i : Fin n, x i = true → y i = true) →
      PEqualNP.CleanedNonEdge.wireVal n C w x = true →
      PEqualNP.CleanedNonEdge.wireVal n C w y = true := by
    intro w x y hxy hx
    apply hMonoFold C.gates (fun g hg => ⟨hLeast.1.1 g hg, hLeast.1.2.2 g hg⟩) (List.ofFn x) (List.ofFn y)
      (by simp only [List.length_ofFn])
    · intro i hi
      rcases Nat.lt_or_ge i n with hilt | hige
      · rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hilt), List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hilt), List.getElem_ofFn]
        exact hxy ⟨i, hilt⟩ hi
      · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; exact hige)] at hi
        exact Bool.noConfusion hi
    · exact hx
  have hBiclique : ∀ a ∈ PEqualNP.TopForm.tops G C, ∀ (p q : Fin n),
      PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a 0) (PEqualNP.EdgeOwnership.pairInput p p) = true →
      PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a 1) (PEqualNP.EdgeOwnership.pairInput q q) = true →
      G.Adj p q := by
    letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    intro a ha p q hp hq
    have haLt : a < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have haAnd : (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op = PEqualNP.CircuitLowerBounds.GateOp.and :=
      (Finset.mem_filter.mp ha).2.1
    have haBelow : PEqualNP.TopForm.BelowF G C a := (Finset.mem_filter.mp ha).2.2
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C a = C.gates[a]'haLt := List.getD_eq_getElem _ _ haLt
    have hlen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs.length = 2 := by
      rw [hga]; exact hLeast.1.2.2 (C.gates[a]'haLt) (List.getElem_mem haLt)
    have hxy0 : ∀ i : Fin n, PEqualNP.EdgeOwnership.pairInput p p i = true → PEqualNP.EdgeOwnership.pairInput p q i = true := by
      intro i hi
      have hip : i = p := by rcases of_decide_eq_true hi with rfl | rfl <;> rfl
      exact decide_eq_true (Or.inl hip)
    have hxy1 : ∀ i : Fin n, PEqualNP.EdgeOwnership.pairInput q q i = true → PEqualNP.EdgeOwnership.pairInput p q i = true := by
      intro i hi
      have hiq : i = q := by rcases of_decide_eq_true hi with rfl | rfl <;> rfl
      exact decide_eq_true (Or.inr hiq)
    have hp' := hWireMono (PEqualNP.TopForm.opnd C a 0) _ _ hxy0 hp
    have hq' := hWireMono (PEqualNP.TopForm.opnd C a 1) _ _ hxy1 hq
    have hinp : (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs =
        [PEqualNP.TopForm.opnd C a 0, PEqualNP.TopForm.opnd C a 1] := by
      rcases hin : (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs with _ | ⟨w0, t1⟩
      · rw [hin] at hlen2; simp at hlen2
      · rcases t1 with _ | ⟨w1, t2⟩
        · rw [hin] at hlen2; simp at hlen2
        · rcases t2 with _ | ⟨_, _⟩
          · change [w0, w1] = [(PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs.getD 0 0,
              (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs.getD 1 0]
            rw [hin]; rfl
          · rw [hin] at hlen2; simp at hlen2
    have hw0Lt : PEqualNP.TopForm.opnd C a 0 < n + a :=
      hLeast.1.2.1 a haLt _ (by rw [hinp]; exact List.mem_cons_self)
    have hw1Lt : PEqualNP.TopForm.opnd C a 1 < n + a :=
      hLeast.1.2.1 a haLt _ (by rw [hinp]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hGateTrue : PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput p q) = true := by
      change (C.gates.foldl step (List.ofFn (PEqualNP.EdgeOwnership.pairInput p q))).getD (n + a) false = true
      have hrg := hGateEval C.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput p q)) a haLt
      rw [List.length_ofFn] at hrg
      rw [hrg, ← hga, haAnd, hinp, List.map_cons, List.map_cons, List.map_nil]
      rw [ite_eq_left_iff.mpr (fun h => absurd hw0Lt h), ite_eq_left_iff.mpr (fun h => absurd hw1Lt h)]
      change PEqualNP.CircuitLowerBounds.GateOp.and.eval
        [PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a 0) (PEqualNP.EdgeOwnership.pairInput p q),
         PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a 1) (PEqualNP.EdgeOwnership.pairInput p q)] = true
      rw [hp', hq']
      rfl
    have hGF := haBelow (PEqualNP.EdgeOwnership.pairInput p q) hGateTrue
    change (decide (∃ x ∈ (∅ : Finset (Fin n)), PEqualNP.EdgeOwnership.pairInput p q x = true) ||
      decide (∃ x y, G.Adj x y ∧ PEqualNP.EdgeOwnership.pairInput p q x = true ∧ PEqualNP.EdgeOwnership.pairInput p q y = true)) = true at hGF
    have hL : decide (∃ x ∈ (∅ : Finset (Fin n)), PEqualNP.EdgeOwnership.pairInput p q x = true) = false :=
      decide_eq_false (by rintro ⟨x, hx, _⟩; exact Finset.notMem_empty x hx)
    rw [hL, Bool.false_or] at hGF
    obtain ⟨x, y, hxy, hx, hy⟩ := of_decide_eq_true hGF
    rcases of_decide_eq_true hx with rfl | rfl <;> rcases of_decide_eq_true hy with rfl | rfl
    · exact False.elim (G.ne_of_adj hxy rfl)
    · exact hxy
    · exact hxy.symm
    · exact False.elim (G.ne_of_adj hxy rfl)
  have hNo4 : ∀ (a b c d : Fin n), G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d → False := by
    intro a b c d hab hbc hcd hda hac hbd
    have e1 := G.ne_of_adj hab
    have e2 := G.ne_of_adj hbc
    have e3 := G.ne_of_adj hcd
    have e4 := G.ne_of_adj hda
    have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
        (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.cons_isPath_iff, e2, e3, e4, hbd, Ne.symm e1, Ne.symm hac]
      · simp [e1, e2, hac, hbd, Ne.symm e1, Ne.symm e4]
    have h5 := hGirth a _ hcyc
    simp at h5
  have hSub :
      {x9 ∈ PEqualNP.TopForm.Ustar G C | ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops G C, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C x12 0) (PEqualNP.EdgeOwnership.pairInput x10 x10) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C x12 1) (PEqualNP.EdgeOwnership.pairInput x11 x11) = true} ⊆
      {e ∈ PEqualNP.TopForm.Ustar G C | ∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ (b : Fin 2), (∀ (w : Fin n), PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a b) (PEqualNP.EdgeOwnership.pairInput w w) = true ↔ w = u) ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a (1 - b)) (PEqualNP.EdgeOwnership.pairInput v v) = true ∧ u ∈ PEqualNP.TopForm.side C a b ∧ v ∉ PEqualNP.TopForm.side C a (1 - b)} ∪
      {e ∈ PEqualNP.TopForm.Ustar G C | ∃ (u v : Fin n), e = s(u, v) ∧ ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ (b : Fin 2), (∀ (w : Fin n), PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a b) (PEqualNP.EdgeOwnership.pairInput w w) = true ↔ w = u) ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a (1 - b)) (PEqualNP.EdgeOwnership.pairInput v v) = true ∧ u ∉ PEqualNP.TopForm.side C a b} := by
    intro e he
    obtain ⟨heU, u, v, heEq, a, haTop, hu0, hv1⟩ := Finset.mem_filter.mp he
    have hStarWit : ∃ (c l : Fin n) (b : Fin 2), e = s(c, l) ∧
        (∀ w : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a b) (PEqualNP.EdgeOwnership.pairInput w w) = true ↔ w = c) ∧
        PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a (1 - b)) (PEqualNP.EdgeOwnership.pairInput l l) = true := by
      by_cases hUniq0 : ∀ w : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C a 0) (PEqualNP.EdgeOwnership.pairInput w w) = true → w = u
      · exact ⟨u, v, 0, heEq, fun w => ⟨hUniq0 w, fun h => h ▸ hu0⟩, hv1⟩
      · push Not at hUniq0
        obtain ⟨u', hu'0, hu'ne⟩ := hUniq0
        refine ⟨v, u, 1, by rw [heEq, Sym2.eq_swap], ?_, hu0⟩
        intro w
        constructor
        · intro hw1
          by_contra hwne
          exact hNo4 u v u' w (hBiclique a haTop u v hu0 hv1) (hBiclique a haTop u' v hu'0 hv1).symm
            (hBiclique a haTop u' w hu'0 hw1) (hBiclique a haTop u w hu0 hw1).symm hu'ne.symm (Ne.symm hwne)
        · intro h; exact h ▸ hv1
    obtain ⟨c, l, b, heCL, hUniq, hLeaf⟩ := hStarWit
    rw [Finset.mem_union]
    by_cases hcSide : c ∈ PEqualNP.TopForm.side C a b
    · left
      refine Finset.mem_filter.mpr ⟨heU, c, l, heCL, a, haTop, b, hUniq, hLeaf, hcSide, ?_⟩
      intro hlSide
      have heNotStar : e ∉ PEqualNP.TopForm.starEdges G C := (Finset.mem_sdiff.mp heU).2
      apply heNotStar
      refine Finset.mem_biUnion.mpr ⟨a, haTop, Finset.mem_image.mpr ?_⟩
      fin_cases b
      · exact ⟨(c, l), Finset.mem_product.mpr ⟨hcSide, hlSide⟩, heCL.symm⟩
      · exact ⟨(l, c), Finset.mem_product.mpr ⟨hlSide, hcSide⟩, by rw [heCL, Sym2.eq_swap]⟩
    · right
      exact Finset.mem_filter.mpr ⟨heU, c, l, heCL, a, haTop, b, hUniq, hLeaf, hcSide⟩
  have hCard := le_trans (Finset.card_le_card hSub) (Finset.card_union_le _ _)
  have hMul : (k1 + k2) * (C.size + 1) = k1 * (C.size + 1) + k2 * (C.size + 1) := Nat.add_mul k1 k2 (C.size + 1)
  omega
