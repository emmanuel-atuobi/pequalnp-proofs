import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8085_2
    (hReads13 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (g a : ℕ),
        have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →
        x1.size ≤ (63 : ℕ) →
        (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size →
        a < g ∧ g < x1.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).inputs = [(13 : ℕ), (26 : ℕ) + a] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).inputs = [(26 : ℕ) + a, (13 : ℕ)]) →
        PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1 a (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true →
        PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1 a (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.false →
        (∀ (x7 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x8 - x9 ∈ x2 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        False)
    (hBothInternal :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (g a b : ℕ),
        have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →
        x1.size ≤ (63 : ℕ) →
        (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size →
        a < g ∧ b < g ∧ a ≠ b ∧ g < x1.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).inputs = [(26 : ℕ) + a, (26 : ℕ) + b] →
        PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1 a (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true →
        PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1 b (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true →
        PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1 a (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.false →
        PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1 b (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.false →
        (∀ (x7 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x8 - x9 ∈ x2 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};   PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x4 ∈ x1.gates, x4.inputs.Nodup) → x1.size ≤ (63 : ℕ) → (∃ x6 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true ∧ ∀ (x7 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x6 x7) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.false) → ∃ (x7 : Fin (26 : ℕ) → Bool), ¬(x1.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x8 - x9 ∈ x2 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) := by
  intro C x2 hAO hNodup hSz hEx
  by_contra hNotEx
  have hSpec : ∀ (x7 : Fin (26 : ℕ) → Bool), C.eval (List.ofFn x7) = Bool.true ↔
      ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x8 - x9 ∈ x2 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true := by
    intro x7
    by_contra hne
    exact hNotEx ⟨x7, hne⟩
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
  let p013 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) (13 : Fin 26)
  let p00 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) (0 : Fin 26)
  have hC013 : C.eval (List.ofFn p013) = true :=
    (hSpec p013).mpr ⟨0, 0, by decide, by decide, by decide⟩
  have hOutLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hev : (C.gates.foldl step (List.ofFn p013)).getD C.output false = true := hC013
    have hl : (C.gates.foldl step (List.ofFn p013)).length = 26 + C.size := by
      rw [run_length, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn p013)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    let w0 : Fin 26 := ⟨C.output, hlt⟩
    let fS : Fin 26 → Bool := fun i => decide (i = w0)
    have hCfS : C.eval (List.ofFn fS) = false := by
      cases h : C.eval (List.ofFn fS)
      · rfl
      · obtain ⟨p, l, _, hp, hl⟩ := (hSpec fS).mp h
        have hp' : Fin.castAdd 13 p = w0 := of_decide_eq_true hp
        have hl' : Fin.natAdd 13 l = w0 := of_decide_eq_true hl
        have hval := congrArg Fin.val (hp'.trans hl'.symm)
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
    have hev : (C.gates.foldl step (List.ofFn fS)).getD C.output false = false := hCfS
    rw [run_input C.gates (List.ofFn fS) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
    simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
    change decide (w0 = w0) = false at hev
    rw [decide_eq_true rfl] at hev
    exact Bool.noConfusion hev
  obtain ⟨g, hg, hAnd, hTrue013, hOpFalse00⟩ := hEx
  have hga0 : PEqualNP.MetaComplexity.NestedCover.gateAt C g = C.gates[g]'hg := by
    change C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hg
  have hLen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.length = 2 := by
    rw [hga0]
    exact hAO.2.2 (C.gates[g]'hg) (List.getElem_mem hg)
  have hGnodup : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.Nodup := by
    rw [hga0]
    exact hNodup (C.gates[g]'hg) (List.getElem_mem hg)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, v] := by
    rcases hin : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs with _ | ⟨u, t1⟩
    · rw [hin] at hLen2; cases hLen2
    · rcases t1 with _ | ⟨v, t2⟩
      · rw [hin] at hLen2; cases hLen2
      · rcases t2 with _ | ⟨w, t3⟩
        · exact ⟨u, v, rfl⟩
        · rw [hin] at hLen2; cases hLen2
  have huvNe : u ≠ v := by
    rw [huv] at hGnodup
    have h1 := (List.nodup_cons.mp hGnodup).1
    intro heq
    exact h1 (heq ▸ List.mem_cons_self)
  have huLt : u < 26 + g := hAO.2.1 g hg u (by rw [huv]; exact List.mem_cons_self)
  have hvLt : v < 26 + g := hAO.2.1 g hg v (by rw [huv]; exact List.mem_cons_of_mem u List.mem_cons_self)
  have hAndEval : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
    intro a b
    cases a <;> cases b <;> rfl
  have hEvalG : PEqualNP.EdgeOwnership.gateVal 26 C g p013 =
      ((C.wires (List.ofFn p013)).getD u false && (C.wires (List.ofFn p013)).getD v false) := by
    change (C.gates.foldl step (List.ofFn p013)).getD (26 + g) false = _
    have hlen : (List.ofFn p013).length = 26 := List.length_ofFn
    have hrg := run_gate C.gates (List.ofFn p013) g hg
    rw [hlen] at hrg
    rw [hrg, ← hga0, hAnd, huv, List.map_cons, List.map_cons, List.map_nil, hAndEval]
    rw [ite_eq_left_iff.mpr (fun h => absurd huLt h), ite_eq_left_iff.mpr (fun h => absurd hvLt h)]
    rfl
  have hBothTrue : (C.wires (List.ofFn p013)).getD u false = true ∧ (C.wires (List.ofFn p013)).getD v false = true := by
    rw [hEvalG] at hTrue013
    exact (Bool.and_eq_true _ _).mp hTrue013
  have hOp0 : PEqualNP.TopForm.opnd C g 0 = u := by
    change (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 0 0 = u
    rw [huv]; rfl
  have hOp1 : PEqualNP.TopForm.opnd C g 1 = v := by
    change (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 1 0 = v
    rw [huv]; rfl
  have huFalse00 : (C.wires (List.ofFn p00)).getD u false = false := by
    have h := hOpFalse00 0
    rw [hOp0] at h
    exact h
  have hvFalse00 : (C.wires (List.ofFn p00)).getD v false = false := by
    have h := hOpFalse00 1
    rw [hOp1] at h
    exact h
  have hRawMustBe13 : ∀ w : ℕ, w < 26 → (C.wires (List.ofFn p013)).getD w false = true →
      (C.wires (List.ofFn p00)).getD w false = false → w = 13 := by
    intro w hw26 hwT hwF
    change (C.gates.foldl step (List.ofFn p013)).getD w false = true at hwT
    rw [run_input C.gates (List.ofFn p013) w (by rw [List.length_ofFn]; exact hw26)] at hwT
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hwT
    simp only [hw26, ↓reduceDIte, Option.getD_some] at hwT
    change decide ((⟨w, hw26⟩ : Fin 26) = 0 ∨ (⟨w, hw26⟩ : Fin 26) = 13) = true at hwT
    rcases of_decide_eq_true hwT with h0 | h13
    · have hw0 : w = 0 := congrArg Fin.val h0
      subst hw0
      change (C.gates.foldl step (List.ofFn p00)).getD 0 false = false at hwF
      rw [run_input C.gates (List.ofFn p00) 0 (by rw [List.length_ofFn]; decide)] at hwF
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hwF
      simp only [hw26, ↓reduceDIte, Option.getD_some] at hwF
      change decide ((0 : Fin 26) = 0 ∨ (0 : Fin 26) = 0) = false at hwF
      exact absurd hwF (by decide)
    · exact congrArg Fin.val h13
  rcases Nat.lt_or_ge u 26 with hu26 | huGe
  · have hu13 : u = 13 := hRawMustBe13 u hu26 hBothTrue.1 huFalse00
    have hvGe : 26 ≤ v := by
      by_contra hv26
      have hv13 : v = 13 := hRawMustBe13 v (Nat.lt_of_not_ge hv26) hBothTrue.2 hvFalse00
      exact huvNe (hu13.trans hv13.symm)
    let a : ℕ := v - 26
    have haEq : 26 + a = v := by omega
    have huv' : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [13, 26 + a] := by
      rw [← hu13, haEq]; exact huv
    have haT : PEqualNP.EdgeOwnership.gateVal 26 C a p013 = true := by
      change (C.wires (List.ofFn p013)).getD (26 + a) false = true
      rw [haEq]; exact hBothTrue.2
    have haF : PEqualNP.EdgeOwnership.gateVal 26 C a p00 = false := by
      change (C.wires (List.ofFn p00)).getD (26 + a) false = false
      rw [haEq]; exact hvFalse00
    exact hReads13 C g a hAO hNodup hSz ⟨hOutGe, hOutLt⟩ ⟨by omega, hg⟩ hAnd (Or.inl huv') haT haF hSpec
  · rcases Nat.lt_or_ge v 26 with hv26 | hvGe
    · have hv13 : v = 13 := hRawMustBe13 v hv26 hBothTrue.2 hvFalse00
      let a : ℕ := u - 26
      have haEq : 26 + a = u := by omega
      have huv' : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [26 + a, 13] := by
        rw [haEq, ← hv13]; exact huv
      have haT : PEqualNP.EdgeOwnership.gateVal 26 C a p013 = true := by
        change (C.wires (List.ofFn p013)).getD (26 + a) false = true
        rw [haEq]; exact hBothTrue.1
      have haF : PEqualNP.EdgeOwnership.gateVal 26 C a p00 = false := by
        change (C.wires (List.ofFn p00)).getD (26 + a) false = false
        rw [haEq]; exact huFalse00
      exact hReads13 C g a hAO hNodup hSz ⟨hOutGe, hOutLt⟩ ⟨by omega, hg⟩ hAnd (Or.inr huv') haT haF hSpec
    · let a : ℕ := u - 26
      let b : ℕ := v - 26
      have haEq : 26 + a = u := by omega
      have hbEq : 26 + b = v := by omega
      have huv' : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [26 + a, 26 + b] := by
        rw [haEq, hbEq]; exact huv
      have haT : PEqualNP.EdgeOwnership.gateVal 26 C a p013 = true := by
        change (C.wires (List.ofFn p013)).getD (26 + a) false = true
        rw [haEq]; exact hBothTrue.1
      have hbT : PEqualNP.EdgeOwnership.gateVal 26 C b p013 = true := by
        change (C.wires (List.ofFn p013)).getD (26 + b) false = true
        rw [hbEq]; exact hBothTrue.2
      have haF : PEqualNP.EdgeOwnership.gateVal 26 C a p00 = false := by
        change (C.wires (List.ofFn p00)).getD (26 + a) false = false
        rw [haEq]; exact huFalse00
      have hbF : PEqualNP.EdgeOwnership.gateVal 26 C b p00 = false := by
        change (C.wires (List.ofFn p00)).getD (26 + b) false = false
        rw [hbEq]; exact hvFalse00
      exact hBothInternal C g a b hAO hNodup hSz ⟨hOutGe, hOutLt⟩ ⟨by omega, by omega, by omega, hg⟩ hAnd huv' haT hbT haF hbF hSpec
