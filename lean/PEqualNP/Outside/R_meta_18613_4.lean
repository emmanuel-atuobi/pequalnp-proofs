import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18613_4
    (hLeftAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →
        (26 : ℕ) ≤ x2 →
        x2 < x3 →
        x3 < (26 : ℕ) + x1.size →
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
    (hLeftOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →
        (26 : ℕ) ≤ x2 →
        x2 < x3 →
        x3 < (26 : ℕ) + x1.size →
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
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           x2 < x3 →             have x9 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x9 : ℕ) (x10 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x9;             have x10 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x10 : ℕ) => {x11 : Fin (13 : ℕ) × Fin (13 : ℕ) | x11.1 ∉ PEqualNP.HeptadCover.singerLines3 x11.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x11.1} {x11.2}) x10 = Bool.true};             (x10 x2).card ≤ (12 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 → x9 x2 x14 = Bool.false ∨ x9 x3 x14 = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x9 x2 x15 = Bool.false ∧ x9 x3 x15 = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x16 ∧ x9 x3 x16 = Bool.false ∧ x9 x2 x16 = Bool.true) → (63 : ℕ) ≤ x1.size := by
  classical
  intro C u v hMono hRB huLt hvLt huv x9 x10 hLow hR2 hR3 hDisj hW1 hW2
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
  have hPref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool) (i : ℕ),
      i < s.length → (gs.foldl step s).getD i false = s.getD i false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro s i _; rfl
    | append_singleton gs g ih =>
      intro s i hi
      have hl : (gs.foldl step s).length = s.length + gs.length := hLen gs s
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((gs.foldl step s) ++ [_]).getD i false = s.getD i false
      rw [List.getD_append _ _ _ _ (by omega)]
      exact ih s i hi
  have hAvoidPt : ∀ p0 : Fin 13, ∃ (l : Fin 13) (p : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ p ≠ p0 := by
    decide
  have hAvoidLn : ∀ l0 : Fin 13, ∃ (l : Fin 13) (p : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ l ≠ l0 := by
    decide
  have huGe : 26 ≤ u := by
    by_contra hlt
    have hlt : u < 26 := Nat.lt_of_not_ge hlt
    by_cases h13 : u < 13
    · let p0 : Fin 13 := ⟨u, h13⟩
      obtain ⟨l, p, hpl, hpne⟩ := hAvoidPt p0
      have hTr := hR2 l p hpl
      change (C.gates.foldl step (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))))).getD u false = true at hTr
      rw [hPref C.gates _ u (by simp only [List.length_append, List.length_ofFn]; exact hlt)] at hTr
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13), List.getElem?_ofFn] at hTr
      simp only [h13, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hTr
      exact hpne hTr.symm
    · let l0 : Fin 13 := ⟨u - 13, by omega⟩
      obtain ⟨l, p, hpl, hlne⟩ := hAvoidLn l0
      have hTr := hR2 l p hpl
      change (C.gates.foldl step (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))))).getD u false = true at hTr
      rw [hPref C.gates _ u (by simp only [List.length_append, List.length_ofFn]; exact hlt)] at hTr
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at hTr
      simp only [List.length_ofFn] at hTr
      rw [List.getElem?_ofFn] at hTr
      have hsub : u - 13 < 13 := by omega
      simp only [hsub, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hTr
      exact hlne hTr.symm
  have hjLt : u - 26 < C.gates.length := by change u - 26 < C.size; omega
  have hGateEq : PEqualNP.MetaComplexity.NestedCover.gateAt C (u - 26) = C.gates[u - 26]'hjLt := by
    change C.gates.getD (u - 26) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hjLt
  have hOp := (hMono (C.gates[u - 26]'hjLt) (List.getElem_mem hjLt)).1
  rw [← hGateEq] at hOp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hOp
  rcases hOp with hAnd | hOr
  · exact hLeftAnd C u v hMono hRB huGe huv hvLt hAnd hLow hR2 hR3 hDisj hW1 hW2
  · exact hLeftOr C u v hMono hRB huGe huv hvLt hOr hLow hR2 hR3 hDisj hW1 hW2
