import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8011_1
    (hHasAndChild :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3};
      have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5};
      have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ);
      have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ);
      have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8;
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (a : ℕ),
        have k : ℕ := x7.output - (26 : ℕ);
        have g : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7 k;
        PEqualNP.MetaComplexity.Monotone2 x7 →
        x7.size ≤ (63 : ℕ) →
        (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) →
        ((26 : ℕ) ≤ x7.output ∧ PEqualNP.ReadTwo.isOr x7 k) →
        (a < k ∧ (26 : ℕ) + a ∈ g.inputs ∧ PEqualNP.ReadTwo.isAnd x7 a) →
        (∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x4 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x12 (x2 x12)) = Bool.true) ∨ ∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x5 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x12) x12) = Bool.true)
    (hOnlyOrChildren :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3};
      have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5};
      have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ);
      have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ);
      have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8;
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (a : ℕ),
        have k : ℕ := x7.output - (26 : ℕ);
        have g : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7 k;
        PEqualNP.MetaComplexity.Monotone2 x7 →
        x7.size ≤ (63 : ℕ) →
        (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) →
        ((26 : ℕ) ≤ x7.output ∧ PEqualNP.ReadTwo.isOr x7 k) →
        (a < k ∧ (26 : ℕ) + a ∈ g.inputs ∧ ∀ w ∈ g.inputs, w < x7.output → (26 : ℕ) ≤ w ∧ PEqualNP.ReadTwo.isOr x7 (w - (26 : ℕ))) →
        (∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x4 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x12 (x2 x12)) = Bool.true) ∨ ∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x5 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x12) x12) = Bool.true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5}; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ); have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ); have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (63 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x7.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (26 : ℕ) ≤ x7.output ∧ x7.output < (26 : ℕ) + x7.size → (∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x4 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x12 (x2 x12)) = Bool.true) ∨ ∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x5 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x12) x12) = Bool.true := by
  intro x1 x2 x3 x4 x5 x6 C hM hSz hPos hOut
  rcases hOut with ⟨hOutOr, hOutGe, hOutLt⟩
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool),
      (gs.foldl step s).length = s.length + gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro s; simp
    | append_singleton gs g ih =>
      intro s
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, step, List.length_append, List.length_singleton]
      rw [ih s]
      omega
  have hPref : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool) (i : ℕ),
      i < s.length + gs.length →
      ((gs ++ hs).foldl step s).getD i false = (gs.foldl step s).getD i false := by
    intro gs hs s i hi
    induction hs using List.reverseRecOn with
    | nil => simp
    | append_singleton hs h ih =>
      rw [← List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (((gs ++ hs).foldl step s) ++ [_]).getD i false = _
      have hl : ((gs ++ hs).foldl step s).length = s.length + (gs ++ hs).length := hLen (gs ++ hs) s
      rw [List.getD_append _ _ _ _ (by rw [hl, List.length_append]; omega)]
      exact ih
  have hPrefIn : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool) (i : ℕ),
      i < s.length → (gs.foldl step s).getD i false = s.getD i false := by
    intro gs s i hi
    have h := hPref [] gs s i (by simpa only [List.length_nil, Nat.add_zero] using hi)
    simpa only [List.nil_append, List.foldl_nil] using h
  have hRunGate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl step s).getD (s.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.take j |>.foldl step s).getD i false) := by
    intro gs s j hj
    have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
      have h1 := List.take_append_drop j gs
      have hdrop : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [hdrop] at h1
      simpa only [List.append_assoc, List.singleton_append] using h1.symm
    have hlenT : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
    have hlen1 : (gs.take j ++ [gs[j]]).length = j + 1 := by
      rw [List.length_append, hlenT, List.length_singleton]
    conv_lhs => rw [hsplit]
    rw [hPref (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) s (s.length + j) (by rw [hlen1]; omega)]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (((gs.take j).foldl step s) ++ [gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step s).getD i false)]).getD (s.length + j) false = _
    have hlenF : ((gs.take j).foldl step s).length = s.length + j := by
      rw [hLen, hlenT]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp only [hlenF, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  let k : ℕ := C.output - 26
  have hkLt : k < C.gates.length := by change C.output - 26 < C.size; omega
  have hOutEq : C.output = 26 + k := by omega
  have hgaOut : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k]'hkLt :=
    List.getD_eq_getElem _ _ hkLt
  have hEvalOut : ∀ f : Fin 26 → Bool,
      PEqualNP.MetaComplexity.circuitFun 26 C f =
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.map fun i =>
        ((C.gates.take k).foldl step (List.ofFn f)).getD i false).any id := by
    intro f
    change (C.gates.foldl step (List.ofFn f)).getD C.output false = _
    rw [hOutEq]
    have hrg := hRunGate C.gates (List.ofFn f) k hkLt
    rw [List.length_ofFn] at hrg
    rw [hrg, ← hgaOut, hOutOr]
    rfl
  by_cases hRaw : ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, w < 26
  · obtain ⟨w, hwMem, hwLt⟩ := hRaw
    have hQcard : ∀ u : Fin 13, ({u, u + 1, u + 4, u + 6} : Finset (Fin 13)).card = 4 := by
      decide
    have hQx4 : ∀ u : Fin 13, x4 ({u, u + 1, u + 4, u + 6} : Finset (Fin 13)) := by
      decide
    have hQx5 : ∀ u : Fin 13, x5 ({u, u + 1, u + 4, u + 6} : Finset (Fin 13)) := by
      decide
    by_cases hw13 : w < 13
    · left
      let u : Fin 13 := ⟨w, hw13⟩
      let Q : Finset (Fin 13) := {u, u + 1, u + 4, u + 6}
      refine ⟨Q, hQcard u, hQx4 u, ?_⟩
      rw [hEvalOut (x6 Q (x2 Q))]
      rw [List.any_eq_true]
      refine ⟨true, List.mem_map.mpr ⟨w, hwMem, ?_⟩, rfl⟩
      rw [hPrefIn (C.gates.take k) (List.ofFn (x6 Q (x2 Q))) w (by rw [List.length_ofFn]; exact hwLt)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hwLt, ↓reduceDIte, Option.getD_some]
      have hcast : (⟨w, hwLt⟩ : Fin 26) = Fin.castAdd 13 u := Fin.ext rfl
      rw [hcast]
      change Fin.addCases (fun (x9 : Fin 13) => Decidable.decide (x9 ∈ Q)) (fun (x9 : Fin 13) => Decidable.decide (x9 ∈ x2 Q)) (Fin.castAdd 13 u) = true
      rw [Fin.addCases_left]
      exact decide_eq_true (Finset.mem_insert_self u _)
    · right
      let l : Fin 13 := ⟨w - 13, by omega⟩
      let Q : Finset (Fin 13) := {l, l + 1, l + 4, l + 6}
      refine ⟨Q, hQcard l, hQx5 l, ?_⟩
      rw [hEvalOut (x6 (x3 Q) Q)]
      rw [List.any_eq_true]
      refine ⟨true, List.mem_map.mpr ⟨w, hwMem, ?_⟩, rfl⟩
      rw [hPrefIn (C.gates.take k) (List.ofFn (x6 (x3 Q) Q)) w (by rw [List.length_ofFn]; exact hwLt)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hwLt, ↓reduceDIte, Option.getD_some]
      have hnat : (⟨w, hwLt⟩ : Fin 26) = Fin.natAdd 13 l := Fin.ext (by change w = 13 + (w - 13); omega)
      rw [hnat]
      change Fin.addCases (fun (x9 : Fin 13) => Decidable.decide (x9 ∈ x3 Q)) (fun (x9 : Fin 13) => Decidable.decide (x9 ∈ Q)) (Fin.natAdd 13 l) = true
      rw [Fin.addCases_right]
      exact decide_eq_true (Finset.mem_insert_self l _)
  · have hNoRaw : ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, 26 ≤ w := by
      intro w hw
      by_contra hlt
      exact hRaw ⟨w, hw, Nat.lt_of_not_ge hlt⟩
    have hExActive : ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, w < C.output := by
      let f0 : Fin 26 → Bool := fun x13 => Decidable.decide (x13 = Fin.castAdd 13 (0 : Fin 13) ∨ x13 = Fin.natAdd 13 (0 : Fin 13))
      have hT : PEqualNP.MetaComplexity.circuitFun 26 C f0 = true := hPos 0 0 (Or.inl rfl)
      rw [hEvalOut f0, List.any_eq_true] at hT
      obtain ⟨b, hbMem, hbEq⟩ := hT
      obtain ⟨w, hwMem, hwVal⟩ := List.mem_map.mp hbMem
      have hwT : ((C.gates.take k).foldl step (List.ofFn f0)).getD w false = true := hwVal.trans hbEq
      have hwLtOut : w < C.output := by
        by_contra hge
        have hge : C.output ≤ w := Nat.le_of_not_lt hge
        have hl : ((C.gates.take k).foldl step (List.ofFn f0)).length = 26 + k := by
          rw [hLen, List.length_ofFn, List.length_take_of_le (Nat.le_of_lt hkLt)]
        have hdf : ((C.gates.take k).foldl step (List.ofFn f0)).getD w false = false :=
          List.getD_eq_default _ _ (by omega)
        rw [hdf] at hwT
        exact Bool.noConfusion hwT
      exact ⟨w, hwMem, hwLtOut⟩
    obtain ⟨w0, hw0Mem, hw0Lt⟩ := hExActive
    have hw0Ge : 26 ≤ w0 := hNoRaw w0 hw0Mem
    by_cases hAndC : ∃ a < k, 26 + a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ PEqualNP.ReadTwo.isAnd C a
    · obtain ⟨a, haLt, haMem, haAnd⟩ := hAndC
      exact hHasAndChild C a hM hSz hPos ⟨hOutGe, hkLt, hOutOr⟩ ⟨haLt, haMem, haAnd⟩
    · have hAllOr : ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, w < C.output →
          26 ≤ w ∧ PEqualNP.ReadTwo.isOr C (w - 26) := by
        intro w hwMem hwLt
        have hwGe : 26 ≤ w := hNoRaw w hwMem
        refine ⟨hwGe, ?_⟩
        have hwk : w - 26 < k := by omega
        have hwLen : w - 26 < C.gates.length := Nat.lt_trans hwk hkLt
        have hgaW : PEqualNP.MetaComplexity.NestedCover.gateAt C (w - 26) = C.gates[w - 26]'hwLen :=
          List.getD_eq_getElem _ _ hwLen
        rcases (hM (C.gates[w - 26]'hwLen) (List.getElem_mem hwLen)).1 with hA | hO
        · have hwEq : 26 + (w - 26) = w := by omega
          exact False.elim (hAndC ⟨w - 26, hwk, hwEq.symm ▸ hwMem, hwLen, by rw [hgaW]; exact hA⟩)
        · exact ⟨hwLen, by rw [hgaW]; exact hO⟩
      have hw0Eq : 26 + (w0 - 26) = w0 := by omega
      exact hOnlyOrChildren C (w0 - 26) hM hSz hPos ⟨hOutGe, hkLt, hOutOr⟩ ⟨by omega, hw0Eq.symm ▸ hw0Mem, hAllOr⟩
