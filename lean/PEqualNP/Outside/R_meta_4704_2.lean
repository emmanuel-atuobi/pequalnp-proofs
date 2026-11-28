import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4704_2
    (hOutAnd :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        (200 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
        ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) →
        (3 : ℕ) ≤ x4.size →
        x4.output = x2 + x2 + (x4.size - (1 : ℕ)) →
        a < x4.size - (1 : ℕ) ∧ b < x4.size - (1 : ℕ) ∧ a ≠ b →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.size - (1 : ℕ))).inputs = [x2 + x2 + a, x2 + x2 + b] →
        PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
        (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) →
        (∀ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x14 → x14.output < x2 + x2 + x14.size → (∀ (x17 x18 : Finset (Fin x2)), x14.eval (PEqualNP.GenericRejection.incidenceInput x17 x18) = x4.eval (PEqualNP.GenericRejection.incidenceInput x17 x18)) → x4.size ≤ x14.size) →
        x2 * x1 ≤ (100 : ℕ) * x4.size)
    (hOutOr :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        (200 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
        ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) →
        (3 : ℕ) ≤ x4.size →
        x4.output = x2 + x2 + (x4.size - (1 : ℕ)) →
        a < x4.size - (1 : ℕ) ∧ b < x4.size - (1 : ℕ) ∧ a ≠ b →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.size - (1 : ℕ))).inputs = [x2 + x2 + a, x2 + x2 + b] →
        PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
        (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) →
        (∀ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x14 → x14.output < x2 + x2 + x14.size → (∀ (x17 x18 : Finset (Fin x2)), x14.eval (PEqualNP.GenericRejection.incidenceInput x17 x18) = x4.eval (PEqualNP.GenericRejection.incidenceInput x17 x18)) → x4.size ≤ x14.size) →
        x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → (∀ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x14 → x14.output < x2 + x2 + x14.size → (∀ (x17 x18 : Finset (Fin x2)), x14.eval (PEqualNP.GenericRejection.incidenceInput x17 x18) = x4.eval (PEqualNP.GenericRejection.incidenceInput x17 x18)) → x4.size ≤ x14.size) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N L C hq hN hCard hUnique hAO hNotR2 hOutLt hRight hFalse hMin
  have hNge2 : 2 ≤ N := by
    have hq2 : 200 ≤ q * q := by nlinarith
    have hsq : q ^ 2 = q * q := Nat.pow_two q
    omega
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
  have hIncLen : ∀ (X Y : Finset (Fin N)), (PEqualNP.GenericRejection.incidenceInput X Y).length = N + N := by
    intro X Y
    change (List.ofFn (fun p : Fin N => decide (p ∈ X)) ++ List.ofFn (fun l : Fin N => decide (l ∈ Y))).length = N + N
    simp only [List.length_append, List.length_ofFn]
  have hIncGetL : ∀ (X Y : Finset (Fin N)) (i : ℕ) (hi : i < N),
      (PEqualNP.GenericRejection.incidenceInput X Y).getD i false = decide ((⟨i, hi⟩ : Fin N) ∈ X) := by
    intro X Y i hi
    change (List.ofFn (fun p : Fin N => decide (p ∈ X)) ++ List.ofFn (fun l : Fin N => decide (l ∈ Y))).getD i false = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_ofFn]; exact hi), List.getElem?_ofFn]
    simp only [hi, ↓reduceDIte, Option.getD_some]
  have hIncGetR : ∀ (X Y : Finset (Fin N)) (i : ℕ) (hi1 : N ≤ i) (hi2 : i < N + N),
      (PEqualNP.GenericRejection.incidenceInput X Y).getD i false = decide ((⟨i - N, by omega⟩ : Fin N) ∈ Y) := by
    intro X Y i hi1 hi2
    change (List.ofFn (fun p : Fin N => decide (p ∈ X)) ++ List.ofFn (fun l : Fin N => decide (l ∈ Y))).getD i false = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_ofFn]; exact hi1)]
    simp only [List.length_ofFn]
    rw [List.getElem?_ofFn]
    have hsub : i - N < N := by omega
    simp only [hsub, ↓reduceDIte, Option.getD_some]
  let emp : Finset (Fin N) := ∅
  have hPtFalse : ∀ p0 : Fin N, C.eval (PEqualNP.GenericRejection.incidenceInput {p0} emp) = false := by
    intro p0
    apply hFalse {p0} emp (by rw [Finset.card_empty]; exact Nat.zero_le q)
    intro l hl
    exact False.elim (Finset.notMem_empty l hl)
  have hLineFalse : ∀ l0 : Fin N, C.eval (PEqualNP.GenericRejection.incidenceInput emp {l0}) = false := by
    intro l0
    apply hFalse emp {l0} (by rw [Finset.card_singleton]; omega)
    intro l _
    exact Finset.disjoint_empty_right (L l)
  have hOutGe : N + N ≤ C.output := by
    by_contra hlt
    have hlt : C.output < N + N := Nat.lt_of_not_ge hlt
    rcases Nat.lt_or_ge C.output N with hL | hR
    · let p0 : Fin N := ⟨C.output, hL⟩
      have hF : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p0} emp)).getD C.output false = false := hPtFalse p0
      rw [run_input C.gates _ C.output (by rw [hIncLen]; exact hlt), hIncGetL {p0} emp C.output hL] at hF
      rw [decide_eq_true (Finset.mem_singleton_self p0)] at hF
      exact Bool.noConfusion hF
    · let l0 : Fin N := ⟨C.output - N, by omega⟩
      have hF : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput emp {l0})).getD C.output false = false := hLineFalse l0
      rw [run_input C.gates _ C.output (by rw [hIncLen]; exact hlt), hIncGetR emp {l0} C.output hR hlt] at hF
      rw [decide_eq_true (Finset.mem_singleton_self l0)] at hF
      exact Bool.noConfusion hF
  let out : ℕ := C.output - (N + N)
  have houtEq : N + N + out = C.output := by omega
  have houtLt : out < C.gates.length := by change C.output - (N + N) < C.size; omega
  have hTakeAO2 : ∀ (m : ℕ) (hm : m ≤ C.gates.length) (o : ℕ),
      PEqualNP.TopForm.IsAO2 (N + N) { gates := C.gates.take m, output := o } := by
    intro m hm o
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      exact hAO.1 g (List.mem_of_mem_take hg)
    · intro j hj i hi
      dsimp only at hj
      have hjM : j < m := by
        have hlt := List.length_take_of_le hm
        omega
      have hjC : j < C.gates.length := Nat.lt_of_lt_of_le hjM hm
      have hgaD : PEqualNP.MetaComplexity.NestedCover.gateAt { gates := C.gates.take m, output := o } j = (C.gates.take m)[j]'hj :=
        List.getD_eq_getElem _ _ hj
      have hgaC : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j]'hjC :=
        List.getD_eq_getElem _ _ hjC
      rw [hgaD, List.getElem_take] at hi
      exact hAO.2.1 j hjC i (by rw [hgaC]; exact hi)
    · intro g hg
      exact hAO.2.2 g (List.mem_of_mem_take hg)
  have hOutLast : out + 1 = C.size := by
    let D : PEqualNP.CircuitLowerBounds.Circuit := { gates := C.gates.take (out + 1), output := C.output }
    have hDsz : D.size = out + 1 := List.length_take_of_le (Nat.succ_le_of_lt houtLt)
    have hDout : D.output = C.output := rfl
    have hDoutLt : D.output < N + N + D.size := by omega
    have hDeq : ∀ X Y : Finset (Fin N),
        D.eval (PEqualNP.GenericRejection.incidenceInput X Y) = C.eval (PEqualNP.GenericRejection.incidenceInput X Y) := by
      intro X Y
      change (D.gates.foldl step (PEqualNP.GenericRejection.incidenceInput X Y)).getD C.output false =
        (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput X Y)).getD C.output false
      have hsplit : C.gates = C.gates.take (out + 1) ++ C.gates.drop (out + 1) := (List.take_append_drop (out + 1) C.gates).symm
      have hlenT : (C.gates.take (out + 1)).length = out + 1 := List.length_take_of_le (Nat.succ_le_of_lt houtLt)
      conv_rhs => rw [hsplit]
      exact (run_prefix (C.gates.take (out + 1)) (C.gates.drop (out + 1)) (PEqualNP.GenericRejection.incidenceInput X Y) C.output (by rw [hIncLen, hlenT]; omega)).symm
    have hLe : C.size ≤ D.size := hMin D (hTakeAO2 (out + 1) (Nat.succ_le_of_lt houtLt) C.output) hDoutLt hDeq
    have hCsz : C.size = C.gates.length := rfl
    omega
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
  have huLt : u < N + N + out := hAO.2.1 out houtLt u (by rw [huv]; exact List.mem_cons_self)
  have hvLt : v < N + N + out := hAO.2.1 out houtLt v (by rw [huv]; exact List.mem_cons_of_mem u List.mem_cons_self)
  have hAndEval : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
    intro a b; cases a <;> cases b <;> rfl
  have hOrEval : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
    intro a b; cases a <;> cases b <;> rfl
  have hEvalOut : ∀ (X Y : Finset (Fin N)),
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C out).op.eval
        [(C.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD u false,
         (C.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD v false] := by
    intro X Y
    change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput X Y)).getD C.output false = _
    rw [← houtEq]
    have hrg := run_gate C.gates (PEqualNP.GenericRejection.incidenceInput X Y) out houtLt
    rw [hIncLen] at hrg
    rw [hrg, ← hgaOut, huv, List.map_cons, List.map_cons, List.map_nil]
    rw [ite_eq_left_iff.mpr (fun h => absurd huLt h), ite_eq_left_iff.mpr (fun h => absurd hvLt h)]
    rfl
  have huvNe : u ≠ v := by
    intro heq
    let D' : PEqualNP.CircuitLowerBounds.Circuit := { gates := C.gates.take out, output := u }
    have hDsz : D'.size = out := List.length_take_of_le (Nat.le_of_lt houtLt)
    have hDout : D'.output = u := rfl
    have hDoutLt : D'.output < N + N + D'.size := by omega
    have hDeq : ∀ X Y : Finset (Fin N),
        D'.eval (PEqualNP.GenericRejection.incidenceInput X Y) = C.eval (PEqualNP.GenericRejection.incidenceInput X Y) := by
      intro X Y
      rw [hEvalOut X Y, ← heq]
      have hIdem : ∀ b : Bool, (PEqualNP.MetaComplexity.NestedCover.gateAt C out).op.eval [b, b] = b := by
        intro b
        rcases hAO.1 (C.gates[out]'houtLt) (List.getElem_mem houtLt) with hA | hO
        · rw [hgaOut, hA, hAndEval]; cases b <;> rfl
        · rw [hgaOut, hO, hOrEval]; cases b <;> rfl
      rw [hIdem]
      change ((C.gates.take out).foldl step (PEqualNP.GenericRejection.incidenceInput X Y)).getD u false =
        (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput X Y)).getD u false
      have hsplit : C.gates = C.gates.take out ++ C.gates.drop out := (List.take_append_drop out C.gates).symm
      have hlenT : (C.gates.take out).length = out := List.length_take_of_le (Nat.le_of_lt houtLt)
      conv_rhs => rw [hsplit]
      exact (run_prefix (C.gates.take out) (C.gates.drop out) (PEqualNP.GenericRejection.incidenceInput X Y) u (by rw [hIncLen, hlenT]; exact huLt)).symm
    have hLe : C.size ≤ D'.size := hMin D' (hTakeAO2 out (Nat.le_of_lt houtLt) u) hDoutLt hDeq
    omega
  have houtSub : C.size - 1 = out := by omega
  have hOutForm : C.output = N + N + (C.size - 1) := by omega
  rcases hAO.1 (C.gates[out]'houtLt) (List.getElem_mem houtLt) with hOpAnd | hOpOr
  · have hOpAnd' : (PEqualNP.MetaComplexity.NestedCover.gateAt C out).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
      rw [hgaOut]; exact hOpAnd
    have hNotRawAnd : ∀ w : ℕ, (w = u ∨ w = v) → N + N ≤ w := by
      intro w hw
      by_contra hlt
      have hlt : w < N + N := Nat.lt_of_not_ge hlt
      rcases Nat.lt_or_ge w N with hL | hR
      · let p0 : Fin N := ⟨w, hL⟩
        let l0 : Fin N := ⟨0, by omega⟩
        have hCardL0 : (L l0).card = q + 1 := hCard l0
        have hErPos : 0 < ((L l0).erase p0).card := by
          have h1 := Finset.pred_card_le_card_erase (s := L l0) (a := p0)
          omega
        obtain ⟨p1, hp1Er⟩ := Finset.card_pos.mp hErPos
        have hp1Ne : p1 ≠ p0 := (Finset.mem_erase.mp hp1Er).1
        have hp1Mem : p1 ∈ L l0 := (Finset.mem_erase.mp hp1Er).2
        have hT : C.eval (PEqualNP.GenericRejection.incidenceInput {p1} {l0}) = true := hRight l0 p1 hp1Mem
        rw [hEvalOut {p1} {l0}, hOpAnd', hAndEval] at hT
        have hBoth := (Bool.and_eq_true _ _).mp hT
        have hwT : (C.wires (PEqualNP.GenericRejection.incidenceInput {p1} {l0})).getD w false = true := by
          rcases hw with rfl | rfl
          · exact hBoth.1
          · exact hBoth.2
        change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p1} {l0})).getD w false = true at hwT
        rw [run_input C.gates _ w (by rw [hIncLen]; exact hlt), hIncGetL {p1} {l0} w hL] at hwT
        have hEqp : p0 = p1 := Finset.mem_singleton.mp (of_decide_eq_true hwT)
        exact hp1Ne hEqp.symm
      · let l0 : Fin N := ⟨w - N, by omega⟩
        let l1 : Fin N := if l0.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
        have hl1Ne : l1 ≠ l0 := by
          intro heq
          have hv := congrArg Fin.val heq
          by_cases h0 : l0.val = 0
          · simp only [l1, h0, ↓reduceIte] at hv
            omega
          · simp only [l1, h0, ↓reduceIte] at hv
            exact h0 hv.symm
        have hCardL1 : (L l1).card = q + 1 := hCard l1
        obtain ⟨p1, hp1Mem⟩ := Finset.card_pos.mp (by omega : 0 < (L l1).card)
        have hT : C.eval (PEqualNP.GenericRejection.incidenceInput {p1} {l1}) = true := hRight l1 p1 hp1Mem
        rw [hEvalOut {p1} {l1}, hOpAnd', hAndEval] at hT
        have hBoth := (Bool.and_eq_true _ _).mp hT
        have hwT : (C.wires (PEqualNP.GenericRejection.incidenceInput {p1} {l1})).getD w false = true := by
          rcases hw with rfl | rfl
          · exact hBoth.1
          · exact hBoth.2
        change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p1} {l1})).getD w false = true at hwT
        rw [run_input C.gates _ w (by rw [hIncLen]; exact hlt), hIncGetR {p1} {l1} w hR hlt] at hwT
        have hEql : l0 = l1 := Finset.mem_singleton.mp (of_decide_eq_true hwT)
        exact hl1Ne hEql.symm
    have huGe : N + N ≤ u := hNotRawAnd u (Or.inl rfl)
    have hvGe : N + N ≤ v := hNotRawAnd v (Or.inr rfl)
    let a : ℕ := u - (N + N)
    let b : ℕ := v - (N + N)
    have haEq : N + N + a = u := by omega
    have hbEq : N + N + b = v := by omega
    have hab : a < C.size - 1 ∧ b < C.size - 1 ∧ a ≠ b := by omega
    have hSz3 : 3 ≤ C.size := by omega
    have huv' : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - 1)).inputs = [N + N + a, N + N + b] := by
      rw [houtSub, haEq, hbEq]; exact huv
    have hOpAnd'' : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - 1)).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
      rw [houtSub]; exact hOpAnd'
    exact hOutAnd q N L C a b hq hN hCard hUnique hAO hNotR2 hSz3 hOutForm hab hOpAnd'' huv' hRight hFalse hMin
  · have hOpOr' : (PEqualNP.MetaComplexity.NestedCover.gateAt C out).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      rw [hgaOut]; exact hOpOr
    have hNotRawOr : ∀ w : ℕ, (w = u ∨ w = v) → N + N ≤ w := by
      intro w hw
      by_contra hlt
      have hlt : w < N + N := Nat.lt_of_not_ge hlt
      rcases Nat.lt_or_ge w N with hL | hR
      · let p0 : Fin N := ⟨w, hL⟩
        have hF : C.eval (PEqualNP.GenericRejection.incidenceInput {p0} emp) = false := hPtFalse p0
        rw [hEvalOut {p0} emp, hOpOr', hOrEval] at hF
        have hwT : (C.wires (PEqualNP.GenericRejection.incidenceInput {p0} emp)).getD w false = true := by
          change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p0} emp)).getD w false = true
          rw [run_input C.gates _ w (by rw [hIncLen]; exact hlt), hIncGetL {p0} emp w hL]
          exact decide_eq_true (Finset.mem_singleton_self p0)
        rcases hw with rfl | rfl
        · rw [hwT, Bool.true_or] at hF; exact Bool.noConfusion hF
        · rw [hwT, Bool.or_true] at hF; exact Bool.noConfusion hF
      · let l0 : Fin N := ⟨w - N, by omega⟩
        have hF : C.eval (PEqualNP.GenericRejection.incidenceInput emp {l0}) = false := hLineFalse l0
        rw [hEvalOut emp {l0}, hOpOr', hOrEval] at hF
        have hwT : (C.wires (PEqualNP.GenericRejection.incidenceInput emp {l0})).getD w false = true := by
          change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput emp {l0})).getD w false = true
          rw [run_input C.gates _ w (by rw [hIncLen]; exact hlt), hIncGetR emp {l0} w hR hlt]
          exact decide_eq_true (Finset.mem_singleton_self l0)
        rcases hw with rfl | rfl
        · rw [hwT, Bool.true_or] at hF; exact Bool.noConfusion hF
        · rw [hwT, Bool.or_true] at hF; exact Bool.noConfusion hF
    have huGe : N + N ≤ u := hNotRawOr u (Or.inl rfl)
    have hvGe : N + N ≤ v := hNotRawOr v (Or.inr rfl)
    let a : ℕ := u - (N + N)
    let b : ℕ := v - (N + N)
    have haEq : N + N + a = u := by omega
    have hbEq : N + N + b = v := by omega
    have hab : a < C.size - 1 ∧ b < C.size - 1 ∧ a ≠ b := by omega
    have hSz3 : 3 ≤ C.size := by omega
    have huv' : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - 1)).inputs = [N + N + a, N + N + b] := by
      rw [houtSub, haEq, hbEq]; exact huv
    have hOpOr'' : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - 1)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      rw [houtSub]; exact hOpOr'
    exact hOutOr q N L C a b hq hN hCard hUnique hAO hNotR2 hSz3 hOutForm hab hOpOr'' huv' hRight hFalse hMin
