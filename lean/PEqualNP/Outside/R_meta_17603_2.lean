import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17603_2
    (hOutAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),
        x2 = [(0 : ℕ), (1 : ℕ)] ∨ x2 = [(13 : ℕ), (14 : ℕ)] →
        have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool → Bool := fun (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : Bool) =>
          have x7 : List Bool := PEqualNP.GenericRejection.incidenceInput x4 x5;
          x1.eval (x7 ++ [x2.any fun (x8 : ℕ) => x7.getD x8 Bool.false] ++ [x6]);
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) x1 →
        (28 : ℕ) ≤ x1.output ∧ x1.output < (28 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (28 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 → x4 {x7} {x8} (if x2 = [(0 : ℕ), (1 : ℕ)] then Decidable.decide (x8 = (0 : Fin (13 : ℕ)) ∧ (x7 = (0 : Fin (13 : ℕ)) ∨ x7 = (1 : Fin (13 : ℕ)))) else Decidable.decide (x7 = (1 : Fin (13 : ℕ)) ∧ (x8 = (0 : Fin (13 : ℕ)) ∨ x8 = (1 : Fin (13 : ℕ))))) = Bool.true) →
        (∀ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x8 → x4 x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8) Bool.false = Bool.false) →
        (62 : ℕ) ≤ x1.size)
    (hOutOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),
        x2 = [(0 : ℕ), (1 : ℕ)] ∨ x2 = [(13 : ℕ), (14 : ℕ)] →
        have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool → Bool := fun (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : Bool) =>
          have x7 : List Bool := PEqualNP.GenericRejection.incidenceInput x4 x5;
          x1.eval (x7 ++ [x2.any fun (x8 : ℕ) => x7.getD x8 Bool.false] ++ [x6]);
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) x1 →
        (28 : ℕ) ≤ x1.output ∧ x1.output < (28 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (28 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 → x4 {x7} {x8} (if x2 = [(0 : ℕ), (1 : ℕ)] then Decidable.decide (x8 = (0 : Fin (13 : ℕ)) ∧ (x7 = (0 : Fin (13 : ℕ)) ∨ x7 = (1 : Fin (13 : ℕ)))) else Decidable.decide (x7 = (1 : Fin (13 : ℕ)) ∧ (x8 = (0 : Fin (13 : ℕ)) ∨ x8 = (1 : Fin (13 : ℕ))))) = Bool.true) →
        (∀ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x8 → x4 x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8) Bool.false = Bool.false) →
        (62 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2 = [(0 : ℕ), (1 : ℕ)] ∨ x2 = [(13 : ℕ), (14 : ℕ)] →     have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool → Bool := fun (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : Bool) =>       have x7 : List Bool := PEqualNP.GenericRejection.incidenceInput x4 x5;       x1.eval (x7 ++ [x2.any fun (x8 : ℕ) => x7.getD x8 Bool.false] ++ [x6]);     PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) x1 → (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 → x4 {x7} {x8} (if x2 = [(0 : ℕ), (1 : ℕ)] then Decidable.decide (x8 = (0 : Fin (13 : ℕ)) ∧ (x7 = (0 : Fin (13 : ℕ)) ∨ x7 = (1 : Fin (13 : ℕ)))) else Decidable.decide (x7 = (1 : Fin (13 : ℕ)) ∧ (x8 = (0 : Fin (13 : ℕ)) ∨ x8 = (1 : Fin (13 : ℕ))))) = Bool.true) → (∀ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x8 → x4 x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8) Bool.false = Bool.false) → (62 : ℕ) ≤ x1.size := by
  intro C xs hxs
  dsimp only
  intro hM hRB hInc hQuad
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
  have hLen26 : ∀ (A B : Finset (Fin 13)), (PEqualNP.GenericRejection.incidenceInput A B).length = 26 := by
    intro A B
    change (List.ofFn (fun i : Fin 13 => decide (i ∈ A)) ++ List.ofFn (fun j : Fin 13 => decide (j ∈ B))).length = 26
    simp only [List.length_append, List.length_ofFn]
  have hLen28 : ∀ (A B : Finset (Fin 13)) (b : Bool),
      ((PEqualNP.GenericRejection.incidenceInput A B) ++
        [xs.any fun x8 => (PEqualNP.GenericRejection.incidenceInput A B).getD x8 false] ++ [b]).length = 28 := by
    intro A B b
    simp only [List.length_append, hLen26, List.length_singleton]
  have h00 : (0 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have h10 : (1 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have h30 : (3 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have h11 : (1 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 1 := by decide
  have h22 : (2 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 2 := by decide
  have hOutLt : C.output < 28 + C.size := by
    by_contra hge
    have hge : 28 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hT := hInc 0 0 h00
    change (C.gates.foldl step _).getD C.output false = true at hT
    have hL : (C.gates.foldl step ((PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}) ++
        [xs.any fun x8 => (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD x8 false] ++
        [if xs = [0, 1] then Decidable.decide ((0 : Fin 13) = 0 ∧ ((0 : Fin 13) = 0 ∨ (0 : Fin 13) = 1))
         else Decidable.decide ((0 : Fin 13) = 1 ∧ ((0 : Fin 13) = 0 ∨ (0 : Fin 13) = 1))])).length = 28 + C.size := by
      rw [hLen, hLen28]
      rfl
    have hF : (C.gates.foldl step ((PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}) ++
        [xs.any fun x8 => (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD x8 false] ++
        [if xs = [0, 1] then Decidable.decide ((0 : Fin 13) = 0 ∧ ((0 : Fin 13) = 0 ∨ (0 : Fin 13) = 1))
         else Decidable.decide ((0 : Fin 13) = 1 ∧ ((0 : Fin 13) = 0 ∨ (0 : Fin 13) = 1))])).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hF] at hT
    exact Bool.noConfusion hT
  have hOutGe : 28 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 28 := Nat.lt_of_not_ge hlt
    have hWire : ∀ (p l : Fin 13) (b : Bool),
        C.eval ((PEqualNP.GenericRejection.incidenceInput {p} {l}) ++
          [xs.any fun x8 => (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD x8 false] ++ [b]) =
        ((PEqualNP.GenericRejection.incidenceInput {p} {l}) ++
          [xs.any fun x8 => (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD x8 false] ++ [b]).getD C.output false := by
      intro p l b
      exact hPref C.gates _ C.output (by rw [hLen28]; exact hlt)
    by_cases h13 : C.output < 13
    · by_cases h0 : C.output = 0
      · have hT := hInc 1 0 h10
        rw [hWire, h0] at hT
        have hF : ((PEqualNP.GenericRejection.incidenceInput ({(1 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}) ++
            [xs.any fun x8 => (PEqualNP.GenericRejection.incidenceInput ({(1 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD x8 false] ++
            [if xs = [0, 1] then Decidable.decide ((0 : Fin 13) = 0 ∧ ((1 : Fin 13) = 0 ∨ (1 : Fin 13) = 1))
             else Decidable.decide ((1 : Fin 13) = 1 ∧ ((0 : Fin 13) = 0 ∨ (0 : Fin 13) = 1))]).getD 0 false = false := by
          rw [List.append_assoc, List.getD_append _ _ _ _ (by rw [hLen26]; omega)]
          decide
        rw [hF] at hT
        exact Bool.noConfusion hT
      · have hT := hInc 0 0 h00
        rw [hWire] at hT
        rw [List.append_assoc, List.getD_append _ _ _ _ (by rw [hLen26]; omega)] at hT
        have hF : ∀ i : Fin 13, i.val ≠ 0 →
            (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD i.val false = false := by
          decide
        rw [hF ⟨C.output, h13⟩ h0] at hT
        exact Bool.noConfusion hT
    · by_cases h26 : C.output < 26
      · by_cases h13eq : C.output = 13
        · have hT := hInc 1 1 h11
          rw [hWire, h13eq] at hT
          rw [List.append_assoc, List.getD_append _ _ _ _ (by rw [hLen26]; omega)] at hT
          have hF : (PEqualNP.GenericRejection.incidenceInput ({(1 : Fin 13)} : Finset (Fin 13)) {(1 : Fin 13)}).getD 13 false = false := by
            decide
          rw [hF] at hT
          exact Bool.noConfusion hT
        · have hT := hInc 0 0 h00
          rw [hWire] at hT
          rw [List.append_assoc, List.getD_append _ _ _ _ (by rw [hLen26]; omega)] at hT
          have hF : ∀ i : Fin 26, 13 < i.val →
              (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD i.val false = false := by
            decide
          rw [hF ⟨C.output, h26⟩ (by show 13 < C.output; omega)] at hT
          exact Bool.noConfusion hT
      · by_cases h26eq : C.output = 26
        · rcases hxs with rfl | rfl
          · have hT := hInc 3 0 h30
            rw [hWire, h26eq] at hT
            have hF : ((PEqualNP.GenericRejection.incidenceInput ({(3 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}) ++
                [[0, 1].any fun x8 => (PEqualNP.GenericRejection.incidenceInput ({(3 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD x8 false] ++
                [if ([0, 1] : List ℕ) = [0, 1] then Decidable.decide ((0 : Fin 13) = 0 ∧ ((3 : Fin 13) = 0 ∨ (3 : Fin 13) = 1))
                 else Decidable.decide ((3 : Fin 13) = 1 ∧ ((0 : Fin 13) = 0 ∨ (0 : Fin 13) = 1))]).getD 26 false = false := by
              decide
            rw [hF] at hT
            exact Bool.noConfusion hT
          · have hT := hInc 2 2 h22
            rw [hWire, h26eq] at hT
            have hF : ((PEqualNP.GenericRejection.incidenceInput ({(2 : Fin 13)} : Finset (Fin 13)) {(2 : Fin 13)}) ++
                [[13, 14].any fun x8 => (PEqualNP.GenericRejection.incidenceInput ({(2 : Fin 13)} : Finset (Fin 13)) {(2 : Fin 13)}).getD x8 false] ++
                [if ([13, 14] : List ℕ) = [0, 1] then Decidable.decide ((2 : Fin 13) = 0 ∧ ((2 : Fin 13) = 0 ∨ (2 : Fin 13) = 1))
                 else Decidable.decide ((2 : Fin 13) = 1 ∧ ((2 : Fin 13) = 0 ∨ (2 : Fin 13) = 1))]).getD 26 false = false := by
              decide
            rw [hF] at hT
            exact Bool.noConfusion hT
        · have h27eq : C.output = 27 := by omega
          have hT := hInc 3 0 h30
          rw [hWire, h27eq] at hT
          rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, hLen26, List.length_singleton]; omega)] at hT
          simp only [List.length_append, hLen26, List.length_singleton, Nat.sub_self, List.getD_cons_zero] at hT
          rcases hxs with rfl | rfl
          · exact absurd hT (by decide)
          · exact absurd hT (by decide)
  have hk_lt : C.output - 28 < C.gates.length := by change C.output - 28 < C.size; omega
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 28) = C.gates[C.output - 28]'hk_lt :=
    List.getD_eq_getElem _ _ hk_lt
  rcases (hM (C.gates[C.output - 28]'hk_lt) (List.getElem_mem hk_lt)).1 with hAnd | hOr
  · exact hOutAnd C xs hxs hM hRB ⟨hOutGe, hOutLt⟩ (by rw [hge]; exact hAnd) hInc hQuad
  · exact hOutOr C xs hxs hM hRB ⟨hOutGe, hOutLt⟩ (by rw [hge]; exact hOr) hInc hQuad
