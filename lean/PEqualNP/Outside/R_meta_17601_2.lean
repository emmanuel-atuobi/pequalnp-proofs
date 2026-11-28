import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17601_2
    (hOutAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ) (x3 x4 : Fin (13 : ℕ)),
        x2 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]] →
        x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →
        have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Bool) =>
          have x10 : List Bool := PEqualNP.GenericRejection.incidenceInput x7 x8;
          x1.eval (x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false] ++ [x9]);
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) x1 →
        (28 : ℕ) ≤ x1.output ∧ x1.output < (28 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (28 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x10 x11 : Fin (13 : ℕ)), x10 ∈ PEqualNP.HeptadCover.singerLines3 x11 → x7 {x10} {x11} (Decidable.decide (x10 = x3 ∧ x11 = x4)) = Bool.true) →
        (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → x7 x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) Bool.false = Bool.false) →
        (62 : ℕ) ≤ x1.size)
    (hOutOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ) (x3 x4 : Fin (13 : ℕ)),
        x2 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]] →
        x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →
        have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Bool) =>
          have x10 : List Bool := PEqualNP.GenericRejection.incidenceInput x7 x8;
          x1.eval (x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false] ++ [x9]);
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) x1 →
        (28 : ℕ) ≤ x1.output ∧ x1.output < (28 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (28 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x10 x11 : Fin (13 : ℕ)), x10 ∈ PEqualNP.HeptadCover.singerLines3 x11 → x7 {x10} {x11} (Decidable.decide (x10 = x3 ∧ x11 = x4)) = Bool.true) →
        (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → x7 x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) Bool.false = Bool.false) →
        (62 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ) (x3 x4 : Fin (13 : ℕ)),   x2 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]] →     x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →       have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Bool) =>         have x10 : List Bool := PEqualNP.GenericRejection.incidenceInput x7 x8;         x1.eval (x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false] ++ [x9]);       PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) x1 → (∀ (x10 x11 : Fin (13 : ℕ)), x10 ∈ PEqualNP.HeptadCover.singerLines3 x11 → x7 {x10} {x11} (Decidable.decide (x10 = x3 ∧ x11 = x4)) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → x7 x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) Bool.false = Bool.false) → (62 : ℕ) ≤ x1.size := by
  intro C x2 x3 x4 hx2 hx34 x7 hMono hRB hInc hQuad
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool),
      (gs.foldl step v).length = v.length + gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro v; simp
    | append_singleton gs g ih =>
      intro v
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, step, List.length_append, List.length_singleton]
      rw [ih v]
      omega
  have hPref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool) (i : ℕ),
      i < v.length → (gs.foldl step v).getD i false = v.getD i false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro v i _; rfl
    | append_singleton gs g ih =>
      intro v i hi
      have hl : (gs.foldl step v).length = v.length + gs.length := hLen gs v
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((gs.foldl step v) ++ [_]).getD i false = v.getD i false
      rw [List.getD_append _ _ _ _ (by omega)]
      exact ih v i hi
  have hIIlen : ∀ X Y : Finset (Fin 13), (PEqualNP.GenericRejection.incidenceInput X Y).length = 26 := by
    intro X Y
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y))).length = 26
    simp only [List.length_append, List.length_ofFn]
  have hDiag : ∀ a : Fin 13, a ∈ PEqualNP.HeptadCover.singerLines3 a := by
    intro a; revert a; decide
  have hNeNext : ∀ a : Fin 13, a + 1 ≠ a := by
    intro a; revert a; decide
  have hOutLt : C.output < 28 + C.size := by
    by_contra hge
    have hge : 28 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hev := hInc 0 0 (hDiag 0)
    let x10 := PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}
    let inp := x10 ++ [x2.any fun i => x10.getD i false] ++ [Decidable.decide ((0 : Fin 13) = x3 ∧ (0 : Fin 13) = x4)]
    have hvl : inp.length = 28 := by
      simp only [inp, List.length_append, List.length_singleton, x10, hIIlen]
    change (C.gates.foldl step inp).getD C.output false = true at hev
    have hl : (C.gates.foldl step inp).length = 28 + C.size := by
      rw [hLen, hvl]
      rfl
    have hdf : (C.gates.foldl step inp).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hOutGe : 28 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 28 := Nat.lt_of_not_ge hlt
    by_cases h13 : C.output < 13
    · let p0 : Fin 13 := ⟨C.output, h13⟩
      have hev := hInc (p0 + 1) (p0 + 1) (hDiag (p0 + 1))
      let x10 := PEqualNP.GenericRejection.incidenceInput ({p0 + 1} : Finset (Fin 13)) {p0 + 1}
      let inp := x10 ++ [x2.any fun i => x10.getD i false] ++ [Decidable.decide (p0 + 1 = x3 ∧ p0 + 1 = x4)]
      have hvl : inp.length = 28 := by
        simp only [inp, List.length_append, List.length_singleton, x10, hIIlen]
      change (C.gates.foldl step inp).getD C.output false = true at hev
      rw [hPref C.gates inp C.output (by omega)] at hev
      have hget : inp.getD C.output false = false := by
        simp only [inp]
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, x10, hIIlen]; omega),
          List.getElem?_append_left (by rw [hIIlen]; omega)]
        change (List.ofFn (fun p : Fin 13 => decide (p ∈ ({p0 + 1} : Finset (Fin 13)))) ++
          List.ofFn (fun l : Fin 13 => decide (l ∈ ({p0 + 1} : Finset (Fin 13)))))[C.output]?.getD false = false
        rw [List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13), List.getElem?_ofFn]
        simp only [h13, ↓reduceDIte, Option.getD_some, Finset.mem_singleton]
        exact decide_eq_false (fun h => hNeNext p0 h.symm)
      rw [hget] at hev
      exact Bool.noConfusion hev
    · by_cases h26 : C.output < 26
      · let l0 : Fin 13 := ⟨C.output - 13, by omega⟩
        have hev := hInc (l0 + 1) (l0 + 1) (hDiag (l0 + 1))
        let x10 := PEqualNP.GenericRejection.incidenceInput ({l0 + 1} : Finset (Fin 13)) {l0 + 1}
        let inp := x10 ++ [x2.any fun i => x10.getD i false] ++ [Decidable.decide (l0 + 1 = x3 ∧ l0 + 1 = x4)]
        have hvl : inp.length = 28 := by
          simp only [inp, List.length_append, List.length_singleton, x10, hIIlen]
        change (C.gates.foldl step inp).getD C.output false = true at hev
        rw [hPref C.gates inp C.output (by omega)] at hev
        have hget : inp.getD C.output false = false := by
          simp only [inp]
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, x10, hIIlen]; omega),
            List.getElem?_append_left (by rw [hIIlen]; exact h26)]
          change (List.ofFn (fun p : Fin 13 => decide (p ∈ ({l0 + 1} : Finset (Fin 13)))) ++
            List.ofFn (fun l : Fin 13 => decide (l ∈ ({l0 + 1} : Finset (Fin 13)))))[C.output]?.getD false = false
          rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega)]
          simp only [List.length_ofFn]
          rw [List.getElem?_ofFn]
          have hsub : C.output - 13 < 13 := by omega
          simp only [hsub, ↓reduceDIte, Option.getD_some, Finset.mem_singleton]
          exact decide_eq_false (fun h => hNeNext l0 h.symm)
        rw [hget] at hev
        exact Bool.noConfusion hev
      · by_cases h27 : C.output = 26
        · have hev := hInc 2 2 (hDiag 2)
          let x10 := PEqualNP.GenericRejection.incidenceInput ({(2 : Fin 13)} : Finset (Fin 13)) {(2 : Fin 13)}
          let inp := x10 ++ [x2.any fun i => x10.getD i false] ++ [Decidable.decide ((2 : Fin 13) = x3 ∧ (2 : Fin 13) = x4)]
          have hvl : inp.length = 28 := by
            simp only [inp, List.length_append, List.length_singleton, x10, hIIlen]
          change (C.gates.foldl step inp).getD C.output false = true at hev
          rw [hPref C.gates inp C.output (by omega), h27] at hev
          have hAnyFalse : ∀ l ∈ ([[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]] : List (List ℕ)),
              l.any (fun i => x10.getD i false) = false := by
            decide
          have hget : inp.getD 26 false = false := by
            simp only [inp]
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, x10, hIIlen]; omega),
              List.getElem?_append_right (by rw [hIIlen])]
            simp only [x10, hIIlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            exact hAnyFalse x2 hx2
          rw [hget] at hev
          exact Bool.noConfusion hev
        · have hEq27 : C.output = 27 := by omega
          have hev := hInc (x4 + 1) (x4 + 1) (hDiag (x4 + 1))
          let x10 := PEqualNP.GenericRejection.incidenceInput ({x4 + 1} : Finset (Fin 13)) {x4 + 1}
          let inp := x10 ++ [x2.any fun i => x10.getD i false] ++ [Decidable.decide (x4 + 1 = x3 ∧ x4 + 1 = x4)]
          have hvl : inp.length = 28 := by
            simp only [inp, List.length_append, List.length_singleton, x10, hIIlen]
          change (C.gates.foldl step inp).getD C.output false = true at hev
          rw [hPref C.gates inp C.output (by omega), hEq27] at hev
          have hget : inp.getD 27 false = false := by
            simp only [inp]
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by simp only [List.length_append, List.length_singleton, x10, hIIlen]; omega)]
            simp only [List.length_append, List.length_singleton, x10, hIIlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            exact decide_eq_false (fun h => hNeNext x4 h.2)
          rw [hget] at hev
          exact Bool.noConfusion hev
  have hj : C.output - 28 < C.gates.length := by
    change C.output - 28 < C.size
    omega
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 28) = C.gates[C.output - 28]'hj := by
    change C.gates.getD (C.output - 28) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hj
  have hOp : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 28)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 28)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    rw [hge]
    have hm := (hMono (C.gates[C.output - 28]'hj) (List.getElem_mem hj)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  rcases hOp with hAnd | hOr
  · exact hOutAnd C x2 x3 x4 hx2 hx34 hMono hRB ⟨hOutGe, hOutLt⟩ hAnd hInc hQuad
  · exact hOutOr C x2 x3 x4 hx2 hx34 hMono hRB ⟨hOutGe, hOutLt⟩ hOr hInc hQuad
