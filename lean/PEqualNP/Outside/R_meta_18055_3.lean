import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18055_3
    (hReadsRaw :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
        (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (g u v : ℕ) (x10 : Fin (26 : ℕ)),
          PEqualNP.TopForm.IsLeastAO x1 x4 →
          g < x4.gates.length →
          (26 : ℕ) + g ≠ x4.output →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 g).inputs = [u, v] →
          u < (26 : ℕ) + g ∧ v < (26 : ℕ) + g ∧ u ≠ (0 : ℕ) ∧ v ≠ (0 : ℕ) →
          (x10 = (1 : Fin (26 : ℕ)) ∨ x10 = (14 : Fin (26 : ℕ))) →
          (u = ↑x10 ∨ v = ↑x10) →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 g (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) x10) = Bool.true →
          False)
    (hBothInternal :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
        (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (g a b : ℕ) (x10 : Fin (26 : ℕ)),
          PEqualNP.TopForm.IsLeastAO x1 x4 →
          g < x4.gates.length →
          (26 : ℕ) + g ≠ x4.output →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 g).inputs = [(26 : ℕ) + a, (26 : ℕ) + b] →
          a < g ∧ b < g →
          (x10 = (0 : Fin (26 : ℕ)) ∨ x10 = (1 : Fin (26 : ℕ)) ∨ x10 = (14 : Fin (26 : ℕ))) →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 a (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) x10) = Bool.true →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 b (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) x10) = Bool.true →
          False) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ x6 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → (0 : ℕ) ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).inputs → ∀ (x10 : Fin (26 : ℕ)), x10 = (0 : Fin (26 : ℕ)) ∨ x10 = (1 : Fin (26 : ℕ)) ∨ x10 = (14 : Fin (26 : ℕ)) → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) x10) = Bool.false := by
  intro G _ hAdj C hLeast g hg hAnd hNot0 t ht
  by_contra hNotF
  have hTrueG : PEqualNP.EdgeOwnership.gateVal 26 C g (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) t) = Bool.true :=
    Bool.eq_true_of_not_eq_false hNotF
  let x : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) t
  have hNotAdj0t : ¬G.Adj (0 : Fin 26) t := by
    intro hadj
    obtain ⟨p, l, hdiff, hpair⟩ := (hAdj 0 t).mp hadj
    rcases ht with rfl | rfl | rfl
    · exact G.ne_of_adj hadj rfl
    · rcases hpair with ⟨_, hl⟩ | ⟨_, hl⟩
      · have := congrArg Fin.val hl
        simp only [Fin.val_natAdd] at this
        change 1 = 13 + l.val at this
        omega
      · have := congrArg Fin.val hl
        simp only [Fin.val_zero, Fin.val_natAdd] at this
        omega
    · rcases hpair with ⟨hp, hl⟩ | ⟨hp, _⟩
      · have hp0 : p = 0 := by
          apply Fin.ext
          have := congrArg Fin.val hp
          simp only [Fin.val_zero, Fin.val_castAdd] at this
          exact this.symm
        have hl1 : l = 1 := by
          apply Fin.ext
          have := congrArg Fin.val hl
          simp only [Fin.val_natAdd] at this
          change 14 = 13 + l.val at this
          change l.val = 1
          omega
        rw [hp0, hl1] at hdiff
        exact absurd hdiff (by decide)
      · have := congrArg Fin.val hp
        simp only [Fin.val_castAdd] at this
        change 14 = p.val at this
        omega
  have hFunFalse : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = Bool.false := by
    change (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) ||
      decide (∃ u v : Fin 26, G.Adj u v ∧ x u = true ∧ x v = true)) = false
    have hL : decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) = false :=
      decide_eq_false (by rintro ⟨a, ha, _⟩; exact Finset.notMem_empty a ha)
    have hR : decide (∃ u v : Fin 26, G.Adj u v ∧ x u = true ∧ x v = true) = false := by
      rw [decide_eq_false_iff_not]
      rintro ⟨u, v, huv, hxu, hxv⟩
      have hu : u = 0 ∨ u = t := of_decide_eq_true hxu
      have hv : v = 0 ∨ v = t := of_decide_eq_true hxv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact G.ne_of_adj huv rfl
      · exact hNotAdj0t huv
      · exact hNotAdj0t huv.symm
      · exact G.ne_of_adj huv rfl
    rw [hL, hR]
    rfl
  have hNeOut : 26 + g ≠ C.output := by
    intro heq
    have hcf := congrFun hLeast.2.1 x
    rw [hFunFalse] at hcf
    change (C.wires (List.ofFn x)).getD C.output false = false at hcf
    rw [← heq] at hcf
    change PEqualNP.EdgeOwnership.gateVal 26 C g x = false at hcf
    rw [hTrueG] at hcf
    exact Bool.noConfusion hcf
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
  have run_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (h : PEqualNP.CircuitLowerBounds.Gate) (v : List Bool),
      (gs ++ [h]).foldl step v = gs.foldl step v ++ [h.op.eval (h.inputs.map fun i => (gs.foldl step v).getD i false)] := by
    intro gs h v
    simp only [step, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool),
      (gs.foldl step v).length = v.length + gs.length := by
    intro gs v
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs h ih =>
      rw [run_snoc]
      simp only [List.length_append, List.length_singleton, ih]
      omega
  have run_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool) (i : ℕ),
      i < v.length + gs.length →
      ((gs ++ hs).foldl step v).getD i false = (gs.foldl step v).getD i false := by
    intro gs hs v i hi
    induction hs using List.reverseRecOn with
    | nil => simp
    | append_singleton hs h ih =>
      rw [← List.append_assoc, run_snoc]
      have hlen : ((gs ++ hs).foldl step v).length = v.length + (gs ++ hs).length := run_length (gs ++ hs) v
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen, List.length_append]; omega), ← List.getD_eq_getElem?_getD]
      exact ih
  have run_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool) (i : ℕ),
      i < v.length → (gs.foldl step v).getD i false = v.getD i false := by
    intro gs v i hi
    have h := run_prefix [] gs v i (by simpa only [List.length_nil, Nat.add_zero] using hi)
    simpa only [List.nil_append, List.foldl_nil] using h
  have run_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool) (k : ℕ) (hk : k < gs.length),
      (gs.foldl step v).getD (v.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i =>
        if i < v.length + k then (gs.foldl step v).getD i false else false) := by
    intro gs v
    induction gs using List.reverseRecOn with
    | nil => intro k hk; simp at hk
    | append_singleton gs h ih =>
      intro k hk
      have hlen : (gs.foldl step v).length = v.length + gs.length := run_length gs v
      have same : ∀ (m : ℕ), m ≤ gs.length → ∀ l : List ℕ,
          (l.map fun i => if i < v.length + m then ((gs ++ [h]).foldl step v).getD i false else false) =
          l.map fun i => if i < v.length + m then (gs.foldl step v).getD i false else false := by
        intro m hm l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · exact run_prefix gs [h] v i (by omega)
        · rfl
      rcases Nat.lt_or_ge k gs.length with hlt | hge
      · rw [List.getElem_append_left hlt, same k (by omega), run_prefix gs [h] v _ (by omega)]
        exact ih k hlt
      · have hkk : k = gs.length := by simp only [List.length_append, List.length_singleton] at hk; omega
        subst hkk
        have hg' : (gs ++ [h])[gs.length] = h := by simp
        rw [hg', same _ le_rfl, run_snoc, ← hlen]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hAndEval : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
    intro a b
    cases a <;> cases b <;> rfl
  have hga0 : PEqualNP.MetaComplexity.NestedCover.gateAt C g = C.gates[g]'hg := by
    change C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hg
  have hAO := hLeast.1
  have hLen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.length = 2 := by
    rw [hga0]
    exact hAO.2.2 (C.gates[g]'hg) (List.getElem_mem hg)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, v] := by
    rcases hin : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs with _ | ⟨u, t1⟩
    · rw [hin] at hLen2; simp at hLen2
    · rcases t1 with _ | ⟨v, t2⟩
      · rw [hin] at hLen2; simp at hLen2
      · rcases t2 with _ | ⟨w, t3⟩
        · exact ⟨u, v, rfl⟩
        · rw [hin] at hLen2; simp at hLen2
  have huLt : u < 26 + g := hAO.2.1 g hg u (by rw [huv]; exact List.mem_cons_self)
  have hvLt : v < 26 + g := hAO.2.1 g hg v (by rw [huv]; exact List.mem_cons_of_mem u List.mem_cons_self)
  have huNe0 : u ≠ 0 := fun h => hNot0 (by rw [huv, h]; exact List.mem_cons_self)
  have hvNe0 : v ≠ 0 := fun h => hNot0 (by rw [huv, h]; exact List.mem_cons_of_mem u List.mem_cons_self)
  have hEvalG : PEqualNP.EdgeOwnership.gateVal 26 C g x =
      ((C.wires (List.ofFn x)).getD u false && (C.wires (List.ofFn x)).getD v false) := by
    change (C.gates.foldl step (List.ofFn x)).getD (26 + g) false = _
    have hlen : (List.ofFn x).length = 26 := List.length_ofFn
    have hrg := run_gate C.gates (List.ofFn x) g hg
    rw [hlen] at hrg
    rw [hrg, ← hga0, hAnd, huv, List.map_cons, List.map_cons, List.map_nil, hAndEval]
    rw [ite_eq_left_iff.mpr (fun h => absurd huLt h), ite_eq_left_iff.mpr (fun h => absurd hvLt h)]
    rfl
  have hBothTrue : (C.wires (List.ofFn x)).getD u false = true ∧ (C.wires (List.ofFn x)).getD v false = true := by
    rw [hEvalG] at hTrueG
    exact (Bool.and_eq_true _ _).mp hTrueG
  have hRawVal : ∀ w : ℕ, w < 26 → w ≠ 0 → (C.wires (List.ofFn x)).getD w false = true →
      w = (t : ℕ) ∧ (t = (1 : Fin 26) ∨ t = (14 : Fin 26)) := by
    intro w hw26 hwNe0 hwTrue
    change (C.gates.foldl step (List.ofFn x)).getD w false = true at hwTrue
    rw [run_input C.gates (List.ofFn x) w (by rw [List.length_ofFn]; exact hw26)] at hwTrue
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hwTrue
    simp only [hw26, ↓reduceDIte, Option.getD_some] at hwTrue
    change decide ((⟨w, hw26⟩ : Fin 26) = 0 ∨ (⟨w, hw26⟩ : Fin 26) = t) = true at hwTrue
    rcases of_decide_eq_true hwTrue with h0 | hEqT
    · exact False.elim (hwNe0 (congrArg Fin.val h0))
    · have hwEq : w = (t : ℕ) := congrArg Fin.val hEqT
      rcases ht with rfl | h1 | h14
      · exact False.elim (hwNe0 hwEq)
      · exact ⟨hwEq, Or.inl h1⟩
      · exact ⟨hwEq, Or.inr h14⟩
  rcases Nat.lt_or_ge u 26 with hu26 | huGe
  · obtain ⟨huT, ht114⟩ := hRawVal u hu26 huNe0 hBothTrue.1
    exact @hReadsRaw G _ hAdj C g u v t hLeast hg hNeOut hAnd huv ⟨huLt, hvLt, huNe0, hvNe0⟩ ht114 (Or.inl huT) hTrueG
  · rcases Nat.lt_or_ge v 26 with hv26 | hvGe
    · obtain ⟨hvT, ht114⟩ := hRawVal v hv26 hvNe0 hBothTrue.2
      exact @hReadsRaw G _ hAdj C g u v t hLeast hg hNeOut hAnd huv ⟨huLt, hvLt, huNe0, hvNe0⟩ ht114 (Or.inr hvT) hTrueG
    · have huEq : 26 + (u - 26) = u := by omega
      have hvEq : 26 + (v - 26) = v := by omega
      have huv' : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [26 + (u - 26), 26 + (v - 26)] := by
        rw [huEq, hvEq]; exact huv
      have haTrue : PEqualNP.EdgeOwnership.gateVal 26 C (u - 26) x = true := by
        change (C.wires (List.ofFn x)).getD (26 + (u - 26)) false = true
        rw [huEq]; exact hBothTrue.1
      have hbTrue : PEqualNP.EdgeOwnership.gateVal 26 C (v - 26) x = true := by
        change (C.wires (List.ofFn x)).getD (26 + (v - 26)) false = true
        rw [hvEq]; exact hBothTrue.2
      exact @hBothInternal G _ hAdj C g (u - 26) (v - 26) t hLeast hg hNeOut hAnd huv' ⟨by omega, by omega⟩ ht haTrue hbTrue
