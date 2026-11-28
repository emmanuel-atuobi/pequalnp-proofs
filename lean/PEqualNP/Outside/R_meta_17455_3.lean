import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17455_3
    (hHasAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        (26 : ℕ) ≤ x1.output →
        x1.output < (26 : ℕ) + x1.size →
        a < x1.output - (26 : ℕ) ∧ b < x1.output - (26 : ℕ) →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).inputs = [(26 : ℕ) + a, (26 : ℕ) + b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).inputs = [(26 : ℕ) + b, (26 : ℕ) + a]) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 a).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (59 : ℕ) ≤ x1.size)
    (hBothOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        (26 : ℕ) ≤ x1.output →
        x1.output < (26 : ℕ) + x1.size →
        a < x1.output - (26 : ℕ) ∧ b < x1.output - (26 : ℕ) →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).inputs = [(26 : ℕ) + a, (26 : ℕ) + b] →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 a).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 b).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (59 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (59 : ℕ) ≤ x1.size := by
  intro C hOutGe hOutLt hAO hSpec hOutOr
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
  have hOrEval : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
    intro a b
    cases a <;> cases b <;> rfl
  let out : ℕ := C.output - 26
  have houtEq : 26 + out = C.output := by omega
  have houtLt : out < C.gates.length := by change C.output - 26 < C.size; omega
  have hgaOut : PEqualNP.MetaComplexity.NestedCover.gateAt C out = C.gates[out]'houtLt :=
    List.getD_eq_getElem _ _ houtLt
  have hLen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C out).inputs.length = 2 := by
    rw [hgaOut]
    exact hAO.2.2 (C.gates[out]'houtLt) (List.getElem_mem houtLt)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C out).inputs = [u, v] := by
    rcases hin : (PEqualNP.MetaComplexity.NestedCover.gateAt C out).inputs with _ | ⟨u, t1⟩
    · rw [hin] at hLen2; cases hLen2
    · rcases t1 with _ | ⟨v, t2⟩
      · rw [hin] at hLen2; cases hLen2
      · rcases t2 with _ | ⟨w, t3⟩
        · exact ⟨u, v, rfl⟩
        · rw [hin] at hLen2; cases hLen2
  have huLt : u < 26 + out := hAO.2.1 out houtLt u (by rw [huv]; exact List.mem_cons_self)
  have hvLt : v < 26 + out := hAO.2.1 out houtLt v (by rw [huv]; exact List.mem_cons_of_mem u List.mem_cons_self)
  have hEvalOut : ∀ x : Fin 26 → Bool,
      C.eval (List.ofFn x) = ((C.wires (List.ofFn x)).getD u false || (C.wires (List.ofFn x)).getD v false) := by
    intro x
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
    rw [← houtEq]
    have hrg := run_gate C.gates (List.ofFn x) out houtLt
    rw [List.length_ofFn] at hrg
    rw [hrg, ← hgaOut, hOutOr, huv, List.map_cons, List.map_cons, List.map_nil, hOrEval]
    rw [ite_eq_left_iff.mpr (fun h => absurd huLt h), ite_eq_left_iff.mpr (fun h => absurd hvLt h)]
    rfl
  have hSingleFalse : ∀ w0 : Fin 26, C.eval (List.ofFn (fun i : Fin 26 => decide (i = w0))) = false := by
    intro w0
    cases h : C.eval (List.ofFn (fun i : Fin 26 => decide (i = w0)))
    · rfl
    · obtain ⟨p, l, _, _, hp, hl⟩ := (hSpec _).mp h
      have hp' : Fin.castAdd 13 p = w0 := of_decide_eq_true hp
      have hl' : Fin.natAdd 13 l = w0 := of_decide_eq_true hl
      have hval := congrArg Fin.val (hp'.trans hl'.symm)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
  have hNotRaw : ∀ w : ℕ, (w = u ∨ w = v) → 26 ≤ w := by
    intro w hw
    by_contra hlt
    have hlt : w < 26 := Nat.lt_of_not_ge hlt
    let w0 : Fin 26 := ⟨w, hlt⟩
    let fS : Fin 26 → Bool := fun i => decide (i = w0)
    have hF : C.eval (List.ofFn fS) = false := hSingleFalse w0
    have hwT : (C.wires (List.ofFn fS)).getD w false = true := by
      change (C.gates.foldl step (List.ofFn fS)).getD w false = true
      rw [run_input C.gates (List.ofFn fS) w (by rw [List.length_ofFn]; exact hlt)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hlt, ↓reduceDIte, Option.getD_some]
      exact decide_eq_true rfl
    rw [hEvalOut fS] at hF
    rcases hw with rfl | rfl
    · rw [hwT, Bool.true_or] at hF
      exact Bool.noConfusion hF
    · rw [hwT, Bool.or_true] at hF
      exact Bool.noConfusion hF
  have huGe : 26 ≤ u := hNotRaw u (Or.inl rfl)
  have hvGe : 26 ≤ v := hNotRaw v (Or.inr rfl)
  let a : ℕ := u - 26
  let b : ℕ := v - 26
  have haEq : 26 + a = u := by omega
  have hbEq : 26 + b = v := by omega
  have haLt : a < out := by omega
  have hbLt : b < out := by omega
  have haGLt : a < C.gates.length := Nat.lt_trans haLt houtLt
  have hbGLt : b < C.gates.length := Nat.lt_trans hbLt houtLt
  have huv' : (PEqualNP.MetaComplexity.NestedCover.gateAt C out).inputs = [26 + a, 26 + b] := by
    rw [haEq, hbEq]; exact huv
  have hgaA : PEqualNP.MetaComplexity.NestedCover.gateAt C a = C.gates[a]'haGLt :=
    List.getD_eq_getElem _ _ haGLt
  have hgaB : PEqualNP.MetaComplexity.NestedCover.gateAt C b = C.gates[b]'hbGLt :=
    List.getD_eq_getElem _ _ hbGLt
  rcases hAO.1 (C.gates[a]'haGLt) (List.getElem_mem haGLt) with haAnd | haOr
  · exact hHasAnd C a b hOutGe hOutLt ⟨haLt, hbLt⟩ hAO hSpec hOutOr (Or.inl huv') (by rw [hgaA]; exact haAnd)
  · rcases hAO.1 (C.gates[b]'hbGLt) (List.getElem_mem hbGLt) with hbAnd | hbOr
    · exact hHasAnd C b a hOutGe hOutLt ⟨hbLt, haLt⟩ hAO hSpec hOutOr (Or.inr huv') (by rw [hgaB]; exact hbAnd)
    · exact hBothOr C a b hOutGe hOutLt ⟨haLt, hbLt⟩ hAO hSpec hOutOr huv' (by rw [hgaA]; exact haOr) (by rw [hgaB]; exact hbOr)
