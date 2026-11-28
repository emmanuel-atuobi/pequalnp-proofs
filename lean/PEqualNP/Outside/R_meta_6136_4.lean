import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6136_4
    (hReadsRaw :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
        (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (j0 u v : ℕ),
          PEqualNP.TopForm.IsLeastAO x1 x4 →
          j0 < x4.gates.length →
          (26 : ℕ) + j0 ≠ x4.output →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j0).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j0).inputs = [u, v] →
          u < (26 : ℕ) + j0 →
          v < (26 : ℕ) + j0 →
          ((u = (0 : ℕ) ∨ u = (1 : ℕ)) ∨ (v = (0 : ℕ) ∨ v = (1 : ℕ))) →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 j0 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))) = Bool.true →
          (∀ k < j0, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 k).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 k (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))) = Bool.false) →
          False)
    (hBothOr :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
        (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (j0 a b : ℕ),
          PEqualNP.TopForm.IsLeastAO x1 x4 →
          j0 < x4.gates.length →
          (26 : ℕ) + j0 ≠ x4.output →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j0).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j0).inputs = [(26 : ℕ) + a, (26 : ℕ) + b] →
          a < j0 →
          b < j0 →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 a).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 b).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 a (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))) = Bool.true →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 b (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))) = Bool.true →
          (∀ k < j0, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 k).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 k (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))) = Bool.false) →
          False) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ x6 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))) = Bool.false := by
  classical
  intro G _ hAdj C hLeast j hj hAnd
  by_contra hNotF
  have hTrueJ : PEqualNP.EdgeOwnership.gateVal 26 C j (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) (1 : Fin 26)) = Bool.true :=
    Bool.eq_true_of_not_eq_false hNotF
  let x : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) (1 : Fin 26)
  let P : ℕ → Prop := fun k =>
    k < C.gates.length ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    PEqualNP.EdgeOwnership.gateVal 26 C k x = Bool.true
  have hEx : ∃ k, P k := ⟨j, hj, hAnd, hTrueJ⟩
  let j0 : ℕ := Nat.find hEx
  have hj0Spec : P j0 := Nat.find_spec hEx
  have hj0Lt : j0 < C.gates.length := hj0Spec.1
  have hj0And : (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and := hj0Spec.2.1
  have hj0True : PEqualNP.EdgeOwnership.gateVal 26 C j0 x = Bool.true := hj0Spec.2.2
  have hMin : ∀ k < j0, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      PEqualNP.EdgeOwnership.gateVal 26 C k x = Bool.false := by
    intro k hk hAndK
    have hnotP : ¬P k := Nat.find_min hEx hk
    by_contra hne
    have hT : PEqualNP.EdgeOwnership.gateVal 26 C k x = Bool.true := Bool.eq_true_of_not_eq_false hne
    exact hnotP ⟨lt_trans hk hj0Lt, hAndK, hT⟩
  have hNotAdj01 : ¬G.Adj (0 : Fin 26) (1 : Fin 26) := by
    intro hadj
    obtain ⟨p, l, _, hpair⟩ := (hAdj 0 1).mp hadj
    rcases hpair with ⟨_, hl⟩ | ⟨_, hl⟩
    · have := congrArg Fin.val hl
      simp only [Fin.val_natAdd] at this
      change 1 = 13 + l.val at this
      omega
    · have := congrArg Fin.val hl
      simp only [Fin.val_natAdd] at this
      change 0 = 13 + l.val at this
      omega
  have hFunFalse : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = Bool.false := by
    change decide (∃ u v : Fin 26, G.Adj u v ∧ x u = true ∧ x v = true) = false
    rw [decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hxu, hxv⟩
    have hu : u = 0 ∨ u = 1 := by
      change decide (u = 0 ∨ u = 1) = true at hxu
      exact of_decide_eq_true hxu
    have hv : v = 0 ∨ v = 1 := by
      change decide (v = 0 ∨ v = 1) = true at hxv
      exact of_decide_eq_true hxv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact G.ne_of_adj huv rfl
    · exact hNotAdj01 huv
    · exact hNotAdj01 (G.symm.symm 1 0 huv)
    · exact G.ne_of_adj huv rfl
  have hNeOut : 26 + j0 ≠ C.output := by
    intro heq
    have hcf := congrFun hLeast.2.1 x
    rw [hFunFalse] at hcf
    change (C.wires (List.ofFn x)).getD C.output false = false at hcf
    rw [← heq] at hcf
    change PEqualNP.EdgeOwnership.gateVal 26 C j0 x = false at hcf
    rw [hj0True] at hcf
    exact Bool.noConfusion hcf
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have run_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (v : List Bool),
      (gs ++ [g]).foldl step v = gs.foldl step v ++ [g.op.eval (g.inputs.map fun i => (gs.foldl step v).getD i false)] := by
    intro gs g v
    simp only [step, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool),
      (gs.foldl step v).length = v.length + gs.length := by
    intro gs v
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [run_snoc]
      simp only [List.length_append, List.length_singleton, ih]
      omega
  have run_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool) (i : ℕ),
      i < v.length + gs.length →
      ((gs ++ hs).foldl step v).getD i false = (gs.foldl step v).getD i false := by
    intro gs hs v i hi
    induction hs using List.reverseRecOn with
    | nil => simp
    | append_singleton hs g ih =>
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
    | append_singleton gs g ih =>
      intro k hk
      have hlen : (gs.foldl step v).length = v.length + gs.length := run_length gs v
      have same : ∀ (m : ℕ), m ≤ gs.length → ∀ l : List ℕ,
          (l.map fun i => if i < v.length + m then ((gs ++ [g]).foldl step v).getD i false else false) =
          l.map fun i => if i < v.length + m then (gs.foldl step v).getD i false else false := by
        intro m hm l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · exact run_prefix gs [g] v i (by omega)
        · rfl
      rcases Nat.lt_or_ge k gs.length with h | h
      · rw [List.getElem_append_left h, same k (by omega), run_prefix gs [g] v _ (by omega)]
        exact ih k h
      · have hkk : k = gs.length := by simp only [List.length_append, List.length_singleton] at hk; omega
        subst hkk
        have hg : (gs ++ [g])[gs.length] = g := by simp
        rw [hg, same _ le_rfl, run_snoc, ← hlen]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hAndEval : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
    intro a b
    cases a <;> cases b <;> rfl
  have hga0 : PEqualNP.MetaComplexity.NestedCover.gateAt C j0 = C.gates[j0]'hj0Lt := by
    change C.gates.getD j0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hj0Lt
  have hAO := hLeast.1
  have hLen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.length = 2 := by
    rw [hga0]
    exact hAO.2.2 (C.gates[j0]'hj0Lt) (List.getElem_mem hj0Lt)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs = [u, v] := by
    rcases hin : (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs with _ | ⟨u, t1⟩
    · rw [hin] at hLen2; simp at hLen2
    · rcases t1 with _ | ⟨v, t2⟩
      · rw [hin] at hLen2; simp at hLen2
      · rcases t2 with _ | ⟨w, t3⟩
        · exact ⟨u, v, rfl⟩
        · rw [hin] at hLen2; simp at hLen2
  have huLt : u < 26 + j0 := hAO.2.1 j0 hj0Lt u (by rw [huv]; exact List.mem_cons_self ..)
  have hvLt : v < 26 + j0 := hAO.2.1 j0 hj0Lt v (by rw [huv]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hEvalJ0 : PEqualNP.EdgeOwnership.gateVal 26 C j0 x =
      ((C.wires (List.ofFn x)).getD u false && (C.wires (List.ofFn x)).getD v false) := by
    change (C.gates.foldl step (List.ofFn x)).getD (26 + j0) false = _
    have hlen : (List.ofFn x).length = 26 := List.length_ofFn
    have hg := run_gate C.gates (List.ofFn x) j0 hj0Lt
    rw [hlen] at hg
    rw [hg, ← hga0, hj0And, huv, List.map_cons, List.map_cons, List.map_nil, hAndEval]
    rw [ite_eq_left_iff.mpr (fun h => absurd huLt h), ite_eq_left_iff.mpr (fun h => absurd hvLt h)]
    rfl
  have hBothTrue : (C.wires (List.ofFn x)).getD u false = true ∧ (C.wires (List.ofFn x)).getD v false = true := by
    rw [hEvalJ0] at hj0True
    exact (Bool.and_eq_true _ _).mp hj0True
  have hWireClass : ∀ w : ℕ, w < 26 + j0 → (C.wires (List.ofFn x)).getD w false = true →
      (w = 0 ∨ w = 1) ∨
      (26 ≤ w ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.EdgeOwnership.gateVal 26 C (w - 26) x = true) := by
    intro w hwLt hwTrue
    by_cases hw26 : w < 26
    · left
      change (C.gates.foldl step (List.ofFn x)).getD w false = true at hwTrue
      rw [run_input C.gates (List.ofFn x) w (by rw [List.length_ofFn]; exact hw26)] at hwTrue
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hwTrue
      simp only [hw26, ↓reduceDIte, Option.getD_some] at hwTrue
      change decide ((⟨w, hw26⟩ : Fin 26) = 0 ∨ (⟨w, hw26⟩ : Fin 26) = 1) = true at hwTrue
      rcases of_decide_eq_true hwTrue with h0 | h1
      · left; exact congrArg Fin.val h0
      · right; exact congrArg Fin.val h1
    · right
      have hwGe : 26 ≤ w := Nat.le_of_not_lt hw26
      have hkLt : w - 26 < j0 := by omega
      have hkLen : w - 26 < C.gates.length := lt_trans hkLt hj0Lt
      have hgv : PEqualNP.EdgeOwnership.gateVal 26 C (w - 26) x = true := by
        change (C.wires (List.ofFn x)).getD (26 + (w - 26)) false = true
        have hadd : 26 + (w - 26) = w := by omega
        rw [hadd]
        exact hwTrue
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C (w - 26) = C.gates[w - 26]'hkLen := by
        change C.gates.getD (w - 26) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
        exact List.getD_eq_getElem _ _ hkLen
      have hop := hAO.1 (C.gates[w - 26]'hkLen) (List.getElem_mem hkLen)
      rw [← hga] at hop
      rcases hop with hAndK | hOrK
      · have hF := hMin (w - 26) hkLt hAndK
        rw [hgv] at hF
        exact Bool.noConfusion hF
      · exact ⟨hwGe, hOrK, hgv⟩
  rcases hWireClass u huLt hBothTrue.1 with huRaw | ⟨huGe, huOr, huVal⟩
  · exact @hReadsRaw G _ hAdj C j0 u v hLeast hj0Lt hNeOut hj0And huv huLt hvLt (Or.inl huRaw) hj0True hMin
  · rcases hWireClass v hvLt hBothTrue.2 with hvRaw | ⟨hvGe, hvOr, hvVal⟩
    · exact @hReadsRaw G _ hAdj C j0 u v hLeast hj0Lt hNeOut hj0And huv huLt hvLt (Or.inr hvRaw) hj0True hMin
    · have huEq : 26 + (u - 26) = u := by omega
      have hvEq : 26 + (v - 26) = v := by omega
      have huv' : (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs = [26 + (u - 26), 26 + (v - 26)] := by
        rw [huEq, hvEq]
        exact huv
      exact @hBothOr G _ hAdj C j0 (u - 26) (v - 26) hLeast hj0Lt hNeOut hj0And huv' (by omega) (by omega) huOr hvOr huVal hvVal hMin
