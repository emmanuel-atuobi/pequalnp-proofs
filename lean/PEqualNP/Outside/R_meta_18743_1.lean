import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18743_1
    (hComparable :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size = (63 : ℕ) →
        (26 : ℕ) ≤ x1.output →
        x1.output < (89 : ℕ) →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (∀ x6 ∈ x1.gates, x6.inputs.Nodup) →
        (∀ (x7 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x8 ∈ PEqualNP.HeptadCover.singerLines3 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →
        PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x9 : ℕ) => Decidable.decide (x9 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →
        have x10 : Finset ℕ → ℕ → Bool := fun (x10 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x10);
        have w0 : ℕ → Bool := x10 {(0 : ℕ), (13 : ℕ)};
        have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => ∃ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 : ℕ) (x16 : ℕ), x1.gates[x13]? = Option.some x14 ∧ x12 = (26 : ℕ) + x13 ∧ x14.inputs = [x15, x16] ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x15 ∨ x11 = x16) ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x11 = if w0 x15 = Bool.true then x15 else x16) ∧ w0 x11 = Bool.true ∧ w0 x12 = Bool.true;
        have R : ℕ → ℕ → Prop := Relation.ReflTransGen x11;
        have x12 : ℕ → ℕ → Prop := fun (x12 x13 : ℕ) => R ((26 : ℕ) + x13) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x13 ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs, w0 x14 = Bool.true ∧ x10 {x12} x14 = Bool.false;
        (∃ (x13 : ℕ) (x14 : ℕ), x13 ≠ x14 ∧ x12 (0 : ℕ) x13 ∧ x12 (13 : ℕ) x14 ∧ x10 {(13 : ℕ)} ((26 : ℕ) + x13) = Bool.false ∧ x10 {(0 : ℕ)} ((26 : ℕ) + x14) = Bool.false ∧ (R ((26 : ℕ) + x13) ((26 : ℕ) + x14) ∨ R ((26 : ℕ) + x14) ((26 : ℕ) + x13))) →
        False)
    (hStrictJoin :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (x1.size = (63 : ℕ) ∧ (26 : ℕ) ≤ x1.output ∧ x1.output < (89 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ ∀ x6 ∈ x1.gates, x6.inputs.Nodup) →
        (∀ (x7 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x8 ∈ PEqualNP.HeptadCover.singerLines3 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →
        PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x9 : ℕ) => Decidable.decide (x9 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →
        have x10 : Finset ℕ → ℕ → Bool := fun (x10 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x10);
        have w0 : ℕ → Bool := x10 {(0 : ℕ), (13 : ℕ)};
        have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => ∃ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 : ℕ) (x16 : ℕ), x1.gates[x13]? = Option.some x14 ∧ x12 = (26 : ℕ) + x13 ∧ x14.inputs = [x15, x16] ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x15 ∨ x11 = x16) ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x11 = if w0 x15 = Bool.true then x15 else x16) ∧ w0 x11 = Bool.true ∧ w0 x12 = Bool.true;
        ∀ (g0 : ℕ),
          PEqualNP.ReadTwo.isAnd x1 g0 →
          Relation.ReflTransGen x11 ((26 : ℕ) + g0) x1.output →
          have x12 : ℕ → ℕ → ℕ → Prop := fun (p q g : ℕ) => g < g0 ∧ PEqualNP.ReadTwo.isAnd x1 g ∧ x10 {q} ((26 : ℕ) + g) = Bool.false ∧ Relation.ReflTransGen x11 ((26 : ℕ) + g) ((26 : ℕ) + g0) ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).inputs, w0 x14 = Bool.true ∧ x10 {p} x14 = Bool.false;
          (∃ (x13 x14 : ℕ), x13 ≠ x14 ∧ x12 (0 : ℕ) (13 : ℕ) x13 ∧ x12 (13 : ℕ) (0 : ℕ) x14) →
          False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size = (63 : ℕ) →     (26 : ℕ) ≤ x1.output →       x1.output < (26 : ℕ) + x1.size →         PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →           (∀ x6 ∈ x1.gates, x6.inputs.Nodup) →             (∀ (x7 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →                 PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x9 : ℕ) => Decidable.decide (x9 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                   have x10 : Finset ℕ → ℕ → Bool := fun (x10 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x10);                   have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => ∃ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 : ℕ) (x16 : ℕ), x1.gates[x13]? = Option.some x14 ∧ x12 = (26 : ℕ) + x13 ∧ x14.inputs = [x15, x16] ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x15 ∨ x11 = x16) ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x11 = if x10 {(0 : ℕ), (13 : ℕ)} x15 = Bool.true then x15 else x16) ∧ x10 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true ∧ x10 {(0 : ℕ), (13 : ℕ)} x12 = Bool.true;                   have x12 : ℕ → ℕ → Prop := fun (x12 x13 : ℕ) => Relation.ReflTransGen x11 ((26 : ℕ) + x13) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x13 ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x13).inputs, x10 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true ∧ x10 {x12} x14 = Bool.false;                   (∃ (x13 : ℕ) (x14 : ℕ), x13 ≠ x14 ∧ x12 (0 : ℕ) x13 ∧ x12 (13 : ℕ) x14 ∧ x10 {(13 : ℕ)} ((26 : ℕ) + x13) = Bool.false ∧ x10 {(0 : ℕ)} ((26 : ℕ) + x14) = Bool.false) → False := by
  intro C hSz hOutLo hOutHi hAO hNd hEv hLS1 hLS2 x10 x11 x12 hEx
  have hSingIff : ∀ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ↔ p ∈ PEqualNP.HeptadCover.singerLines3 l := by
    decide
  have hEv' : ∀ (f : Fin 26 → Bool), C.eval (List.ofFn f) = Bool.true ↔
      ∃ (p l : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ f (Fin.castAdd 13 p) = Bool.true ∧ f (Fin.natAdd 13 l) = Bool.true := by
    intro f
    rw [hEv f]
    constructor
    · intro h; obtain ⟨p, l, hpl, hp, hl⟩ := h; exact ⟨p, l, (hSingIff p l).mp hpl, hp, hl⟩
    · intro h; obtain ⟨p, l, hpl, hp, hl⟩ := h; exact ⟨p, l, (hSingIff p l).mpr hpl, hp, hl⟩
  have hOut89 : C.output < 89 := by omega
  obtain ⟨a, b, hNe, h12a, h12b, h13f, h14f⟩ := hEx
  have hStepLt : ∀ u v : ℕ, x11 u v → u < v := by
    intro u v h
    obtain ⟨k, g, u1, u2, hget, hvEq, hin, hop, _, _⟩ := h
    have hk : k < C.gates.length := by
      by_contra hge
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hget
      cases hget
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
      change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g
      rw [List.getD_eq_getElem _ _ hk]
      have hs := List.getElem?_eq_getElem hk
      rw [hs] at hget
      exact Option.some.inj hget
    have hu1Lt : u1 < 26 + k := hAO.2.1 k hk u1 (by rw [hga, hin]; exact List.mem_cons_self ..)
    have hu2Lt : u2 < 26 + k := hAO.2.1 k hk u2 (by rw [hga, hin]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rw [hvEq]
    rcases hop with ⟨_, rfl | rfl⟩ | ⟨_, rfl⟩
    · exact hu1Lt
    · exact hu2Lt
    · by_cases ht : x10 {(0 : ℕ), (13 : ℕ)} u1 = Bool.true
      · rw [ite_eq_left_iff.mpr (fun h => absurd ht h)]; exact hu1Lt
      · rw [ite_eq_right_iff.mpr (fun h => absurd h ht)]; exact hu2Lt
  have hPathLe : ∀ u v : ℕ, Relation.ReflTransGen x11 u v → u ≤ v := by
    intro u v h
    induction h with
    | refl => exact Nat.le_refl u
    | tail _ hstep ih => exact le_trans ih (Nat.le_of_lt (hStepLt _ _ hstep))
  have hOrUnique : ∀ (k : ℕ) (u1 u2 : ℕ),
      k < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      x11 u1 (26 + k) → x11 u2 (26 + k) → u1 = u2 := by
    intro k u1 u2 hk hOr h1 h2
    obtain ⟨k1, g1, p1, q1, hget1, hk1eq, hin1, hop1, _, _⟩ := h1
    obtain ⟨k2, g2, p2, q2, hget2, hk2eq, hin2, hop2, _, _⟩ := h2
    have hkeq1 : k1 = k := by omega
    have hkeq2 : k2 = k := by omega
    rw [hkeq1] at hget1
    rw [hkeq2] at hget2
    rw [hget1] at hget2
    have hgEq : g1 = g2 := Option.some.inj hget2
    subst hgEq
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g1 := by
      change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g1
      rw [List.getD_eq_getElem _ _ hk]
      have hs := List.getElem?_eq_getElem hk
      rw [hs] at hget1
      exact Option.some.inj hget1
    rw [hga] at hOr
    rcases hop1 with ⟨hAnd1, _⟩ | ⟨_, hu1Eq⟩
    · rw [hOr] at hAnd1; cases hAnd1
    · rcases hop2 with ⟨hAnd2, _⟩ | ⟨_, hu2Eq⟩
      · rw [hOr] at hAnd2; cases hAnd2
      · rw [hin1] at hin2
        have hp : p1 = p2 := (List.cons.inj hin2).1
        have hq : q1 = q2 := (List.cons.inj (List.cons.inj hin2).2).1
        rw [hu1Eq, hu2Eq, hp, hq]
  have hFindAnd : ∀ w : ℕ,
      26 ≤ w → w < 26 + C.size →
      Relation.ReflTransGen x11 (26 + a) w →
      Relation.ReflTransGen x11 (26 + b) w →
      Relation.ReflTransGen x11 w C.output →
      ∃ g0 : ℕ, PEqualNP.ReadTwo.isAnd C g0 ∧
        Relation.ReflTransGen x11 (26 + a) (26 + g0) ∧
        Relation.ReflTransGen x11 (26 + b) (26 + g0) ∧
        Relation.ReflTransGen x11 (26 + g0) C.output := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwLo hwHi haW hbW hwOut
      have hk : w - 26 < C.gates.length := by change w - 26 < C.size; omega
      have hwEq : 26 + (w - 26) = w := by omega
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C (w - 26) = C.gates[w - 26]'hk := by
        change C.gates.getD (w - 26) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
        exact List.getD_eq_getElem _ _ hk
      have hop := hAO.1 (C.gates[w - 26]'hk) (List.getElem_mem hk)
      rw [← hga] at hop
      rcases hop with hAndW | hOrW
      · refine ⟨w - 26, ⟨hk, hAndW⟩, ?_, ?_, ?_⟩
        · rw [hwEq]; exact haW
        · rw [hwEq]; exact hbW
        · rw [hwEq]; exact hwOut
      · have hneA : 26 + a ≠ w := by
          intro heq
          have haEq : a = w - 26 := by omega
          have haAnd : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
            rw [← haEq]
            exact h12a.2.1.2
          rw [hOrW] at haAnd
          cases haAnd
        have hneB : 26 + b ≠ w := by
          intro heq
          have hbEq : b = w - 26 := by omega
          have hbAnd : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
            rw [← hbEq]
            exact h12b.2.1.2
          rw [hOrW] at hbAnd
          cases hbAnd
        rcases Relation.ReflTransGen.cases_tail haW with haEq | ⟨u1, hau1, hu1W⟩
        · exact absurd haEq.symm hneA
        · rcases Relation.ReflTransGen.cases_tail hbW with hbEq | ⟨u2, hbu2, hu2W⟩
          · exact absurd hbEq.symm hneB
          · have hu1W' : x11 u1 (26 + (w - 26)) := by rw [hwEq]; exact hu1W
            have hu2W' : x11 u2 (26 + (w - 26)) := by rw [hwEq]; exact hu2W
            have huEq : u1 = u2 := hOrUnique (w - 26) u1 u2 hk hOrW hu1W' hu2W'
            rw [← huEq] at hbu2
            have hu1Lt : u1 < w := hStepLt u1 w hu1W
            have hu1Ge : 26 ≤ u1 := by
              have hle := hPathLe (26 + a) u1 hau1
              omega
            exact ih u1 hu1Lt hu1Ge (lt_trans hu1Lt hwHi) hau1 hbu2 (Relation.ReflTransGen.head hu1W hwOut)
  obtain ⟨g0, hg0And, haG0, hbG0, hg0Out⟩ := hFindAnd C.output hOutLo hOutHi h12a.1 h12b.1 Relation.ReflTransGen.refl
  by_cases haEq : a = g0
  · subst haEq
    exact hComparable C hSz hOutLo hOut89 hAO hNd hEv' hLS1 hLS2 ⟨a, b, hNe, h12a, h12b, h13f, h14f, Or.inr hbG0⟩
  · by_cases hbEq : b = g0
    · subst hbEq
      exact hComparable C hSz hOutLo hOut89 hAO hNd hEv' hLS1 hLS2 ⟨a, b, hNe, h12a, h12b, h13f, h14f, Or.inl haG0⟩
    · have haLe : 26 + a ≤ 26 + g0 := hPathLe _ _ haG0
      have hbLe : 26 + b ≤ 26 + g0 := hPathLe _ _ hbG0
      have haLt : a < g0 := by omega
      have hbLt : b < g0 := by omega
      exact hStrictJoin C ⟨hSz, hOutLo, hOut89, hAO, hNd⟩ hEv' hLS1 hLS2 g0 hg0And hg0Out
        ⟨a, b, hNe, ⟨haLt, h12a.2.1, h13f, haG0, h12a.2.2⟩, ⟨hbLt, h12b.2.1, h14f, hbG0, h12b.2.2⟩⟩
