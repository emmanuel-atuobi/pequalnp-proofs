import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18615_3
    (hTopAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →
        (26 : ℕ) ≤ x3 ∧ x3 < x2 ∧ x2 < (26 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x2 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        have x9 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x9 : ℕ) (x10 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x9;
        have x10 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x10 : ℕ) => {x11 : Fin (13 : ℕ) × Fin (13 : ℕ) | x11.1 ∉ PEqualNP.HeptadCover.singerLines3 x11.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x11.1} {x11.2}) x10 = Bool.true};
        (x10 x2).card ≤ (12 : ℕ) →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } →
        (∀ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 → x9 x2 x14 = Bool.false ∨ x9 x3 x14 = Bool.false) →
        (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x9 x2 x15 = Bool.false ∧ x9 x3 x15 = Bool.true) →
        (∃ (x16 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x16 ∧ x9 x3 x16 = Bool.false ∧ x9 x2 x16 = Bool.true) →
        (63 : ℕ) ≤ x1.size)
    (hTopOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →
        (26 : ℕ) ≤ x3 ∧ x3 < x2 ∧ x2 < (26 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x2 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        have x9 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x9 : ℕ) (x10 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x9;
        have x10 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x10 : ℕ) => {x11 : Fin (13 : ℕ) × Fin (13 : ℕ) | x11.1 ∉ PEqualNP.HeptadCover.singerLines3 x11.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x11.1} {x11.2}) x10 = Bool.true};
        (x10 x2).card ≤ (12 : ℕ) →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } →
        (∀ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 → x9 x2 x14 = Bool.false ∨ x9 x3 x14 = Bool.false) →
        (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x9 x2 x15 = Bool.false ∧ x9 x3 x15 = Bool.true) →
        (∃ (x16 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x16 ∧ x9 x3 x16 = Bool.false ∧ x9 x2 x16 = Bool.true) →
        (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           x3 < x2 →             have x9 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x9 : ℕ) (x10 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x9;             have x10 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x10 : ℕ) => {x11 : Fin (13 : ℕ) × Fin (13 : ℕ) | x11.1 ∉ PEqualNP.HeptadCover.singerLines3 x11.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x11.1} {x11.2}) x10 = Bool.true};             (x10 x2).card ≤ (12 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 → x9 x2 x14 = Bool.false ∨ x9 x3 x14 = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x9 x2 x15 = Bool.false ∧ x9 x3 x15 = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x16 ∧ x9 x3 x16 = Bool.false ∧ x9 x2 x16 = Bool.true) → (63 : ℕ) ≤ x1.size := by
  intro C w2 w3 hM hRB hw2Lt hw3Lt hw32
  dsimp only
  intro hCard hR2 hR3 hQ hE1 hE2
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
  have h00 : (0 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have h10 : (1 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by decide
  have h11 : (1 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 1 := by decide
  have hw3Ge : 26 ≤ w3 := by
    by_contra hlt
    have hlt : w3 < 26 := Nat.lt_of_not_ge hlt
    by_cases h13 : w3 < 13
    · by_cases h0 : w3 = 0
      · have hT := hR3 0 1 h10
        change (C.gates.foldl step _).getD w3 false = true at hT
        rw [hPref C.gates _ w3 (by rw [hLen26]; exact hlt), h0] at hT
        have hF : (PEqualNP.GenericRejection.incidenceInput ({(1 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD 0 false = false := by decide
        rw [hF] at hT
        exact Bool.noConfusion hT
      · have hT := hR3 0 0 h00
        change (C.gates.foldl step _).getD w3 false = true at hT
        rw [hPref C.gates _ w3 (by rw [hLen26]; exact hlt)] at hT
        have hF : ∀ i : Fin 13, i.val ≠ 0 →
            (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD i.val false = false := by decide
        rw [hF ⟨w3, h13⟩ h0] at hT
        exact Bool.noConfusion hT
    · by_cases h13eq : w3 = 13
      · have hT := hR3 1 1 h11
        change (C.gates.foldl step _).getD w3 false = true at hT
        rw [hPref C.gates _ w3 (by rw [hLen26]; exact hlt), h13eq] at hT
        have hF : (PEqualNP.GenericRejection.incidenceInput ({(1 : Fin 13)} : Finset (Fin 13)) {(1 : Fin 13)}).getD 13 false = false := by decide
        rw [hF] at hT
        exact Bool.noConfusion hT
      · have hT := hR3 0 0 h00
        change (C.gates.foldl step _).getD w3 false = true at hT
        rw [hPref C.gates _ w3 (by rw [hLen26]; exact hlt)] at hT
        have hF : ∀ i : Fin 26, 13 < i.val →
            (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}).getD i.val false = false := by decide
        rw [hF ⟨w3, hlt⟩ (by show 13 < w3; omega)] at hT
        exact Bool.noConfusion hT
  have hk2 : w2 - 26 < C.gates.length := by change w2 - 26 < C.size; omega
  have hga2 : PEqualNP.MetaComplexity.NestedCover.gateAt C (w2 - 26) = C.gates[w2 - 26]'hk2 :=
    List.getD_eq_getElem _ _ hk2
  rcases (hM (C.gates[w2 - 26]'hk2) (List.getElem_mem hk2)).1 with hAnd | hOr
  · exact hTopAnd C w2 w3 hM hRB ⟨hw3Ge, hw32, hw2Lt⟩ (by rw [hga2]; exact hAnd) hCard hR2 hR3 hQ hE1 hE2
  · exact hTopOr C w2 w3 hM hRB ⟨hw3Ge, hw32, hw2Lt⟩ (by rw [hga2]; exact hOr) hCard hR2 hR3 hQ hE1 hE2
