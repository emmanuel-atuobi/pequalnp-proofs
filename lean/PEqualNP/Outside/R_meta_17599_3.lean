import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17599_3
    (hOutAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : List ℕ) (x4 : Bool),
        x2 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]] →
        (28 : ℕ) ≤ x1.output ∧ x1.output < (28 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (28 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        have x6 : PEqualNP.CircuitLowerBounds.Gate := if x4 = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x3 : PEqualNP.CircuitLowerBounds.Gate };
        have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x2 : PEqualNP.CircuitLowerBounds.Gate } :: x6 :: x1.gates, output := x1.output : PEqualNP.CircuitLowerBounds.Circuit };
        PEqualNP.MetaComplexity.Monotone2 x7 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x7 →
        (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → x7.eval (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11)) = Bool.false) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x7 (1 : ℕ) →
        (62 : ℕ) ≤ x1.size)
    (hOutOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : List ℕ) (x4 : Bool),
        x2 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]] →
        (28 : ℕ) ≤ x1.output ∧ x1.output < (28 : ℕ) + x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (28 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        have x6 : PEqualNP.CircuitLowerBounds.Gate := if x4 = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x3 : PEqualNP.CircuitLowerBounds.Gate };
        have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x2 : PEqualNP.CircuitLowerBounds.Gate } :: x6 :: x1.gates, output := x1.output : PEqualNP.CircuitLowerBounds.Circuit };
        PEqualNP.MetaComplexity.Monotone2 x7 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x7 →
        (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → x7.eval (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11)) = Bool.false) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x7 (1 : ℕ) →
        (62 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : List ℕ) (x4 : Bool),   x2 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]] →     have x6 : PEqualNP.CircuitLowerBounds.Gate := if x4 = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x3 : PEqualNP.CircuitLowerBounds.Gate };     have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x2 : PEqualNP.CircuitLowerBounds.Gate } :: x6 :: x1.gates, output := x1.output : PEqualNP.CircuitLowerBounds.Circuit };     PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x7 → (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → x7.eval (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11)) = Bool.false) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x7 (1 : ℕ) → (62 : ℕ) ≤ x1.size := by
  classical
  intro C x2 x3 x4 hx2 x6 x7 hMono hRB hRight hQuad hNoDeg
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
  have hAvoidPt : ∀ p0 : Fin 13, ∃ (l : Fin 13) (p : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ p ≠ p0 := by
    decide
  have hAvoidLn : ∀ l0 : Fin 13, ∃ (l : Fin 13) (p : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ l ≠ l0 := by
    decide
  have hAnyInc : ∃ (l : Fin 13) (p : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l := by
    decide
  have hSomeQuad : ∃ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q := by
    refine ⟨{(0 : Fin 13), 1, 2, 5}, ?_⟩
    decide
  have hInBit : ∀ (p l : Fin 13) (k : ℕ), k < 26 →
      (PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13))).getD k false = true →
      k = p.val ∨ k = 13 + l.val := by
    intro p l k hk hv
    change (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13))))).getD k false = true at hv
    by_cases h13 : k < 13
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13), List.getElem?_ofFn] at hv
      simp only [h13, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hv
      left
      exact congrArg Fin.val hv
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at hv
      simp only [List.length_ofFn] at hv
      rw [List.getElem?_ofFn] at hv
      have hsub : k - 13 < 13 := by omega
      simp only [hsub, ↓reduceDIte, Option.getD_some, Finset.mem_singleton, decide_eq_true_eq] at hv
      right
      have := congrArg Fin.val hv
      dsimp only at this
      omega
  have hInLen : ∀ (S T : Finset (Fin 13)), (PEqualNP.GenericRejection.incidenceInput S T).length = 26 := by
    intro S T
    change (List.ofFn (fun a : Fin 13 => decide (a ∈ S)) ++ List.ofFn (fun b : Fin 13 => decide (b ∈ T))).length = 26
    simp only [List.length_append, List.length_ofFn]
  have hX2Mem : ∀ w ∈ x2, w = 0 ∨ w = 1 ∨ w = 13 ∨ w = 14 := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx2
    rcases hx2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hw <;> omega
  have hAvoid4 : ∀ (a b : Fin 13), ∃ (l p : Fin 13),
      p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
      p.val ≠ 0 ∧ p.val ≠ 1 ∧ l.val ≠ 0 ∧ l.val ≠ 1 ∧
      p ≠ a ∧ p ≠ b ∧ l ≠ a ∧ l ≠ b := by
    decide
  have hAvoidWires : ∀ (w1 w2 : ℕ), ∃ (l p : Fin 13),
      p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
      p.val ≠ 0 ∧ p.val ≠ 1 ∧ l.val ≠ 0 ∧ l.val ≠ 1 ∧
      p.val ≠ w1 ∧ 13 + l.val ≠ w1 ∧ p.val ≠ w2 ∧ 13 + l.val ≠ w2 := by
    intro w1 w2
    let a : Fin 13 := ⟨w1 % 13, Nat.mod_lt w1 (by omega)⟩
    let b : Fin 13 := ⟨w2 % 13, Nat.mod_lt w2 (by omega)⟩
    obtain ⟨l, p, hpl, hp0, hp1, hl0, hl1, hpa, hpb, hla, hlb⟩ := hAvoid4 a b
    refine ⟨l, p, hpl, hp0, hp1, hl0, hl1, ?_, ?_, ?_, ?_⟩
    · intro h; apply hpa; apply Fin.ext; dsimp only [a]; rw [← h, Nat.mod_eq_of_lt p.isLt]
    · intro h; apply hla; apply Fin.ext; dsimp only [a]; rw [← h, Nat.add_mod_left, Nat.mod_eq_of_lt l.isLt]
    · intro h; apply hpb; apply Fin.ext; dsimp only [b]; rw [← h, Nat.mod_eq_of_lt p.isLt]
    · intro h; apply hlb; apply Fin.ext; dsimp only [b]; rw [← h, Nat.add_mod_left, Nat.mod_eq_of_lt l.isLt]
  have hOutGe26 : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    by_cases h13 : C.output < 13
    · let p0 : Fin 13 := ⟨C.output, h13⟩
      obtain ⟨l, p, hpl, hpne⟩ := hAvoidPt p0
      have hev := hRight l p hpl
      change (x7.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD C.output false = true at hev
      rw [hPref x7.gates _ C.output (by rw [hInLen]; exact hlt)] at hev
      rcases hInBit p l C.output hlt hev with hp | hl
      · exact hpne (Fin.ext hp.symm)
      · omega
    · let l0 : Fin 13 := ⟨C.output - 13, by omega⟩
      obtain ⟨l, p, hpl, hlne⟩ := hAvoidLn l0
      have hev := hRight l p hpl
      change (x7.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD C.output false = true at hev
      rw [hPref x7.gates _ C.output (by rw [hInLen]; exact hlt)] at hev
      rcases hInBit p l C.output hlt hev with hp | hl
      · omega
      · apply hlne; apply Fin.ext; dsimp only [l0]; omega
  have hGate0Eval : ∀ (p l : Fin 13),
      p.val ≠ 0 → p.val ≠ 1 → l.val ≠ 0 → l.val ≠ 1 →
      (step (PEqualNP.GenericRejection.incidenceInput {p} {l}) { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x2 }).getD 26 false = false := by
    intro p l hp0 hp1 hl0 hl1
    let v := PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13))
    have hvlen : v.length = 26 := hInLen {p} {l}
    have hidx : (v ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (x2.map fun i => v.getD i false)]).getD 26 false =
        PEqualNP.CircuitLowerBounds.GateOp.or.eval (x2.map fun i => v.getD i false) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp only [hvlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    change (v ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (x2.map fun i => v.getD i false)]).getD 26 false = false
    rw [hidx]
    change (x2.map fun i => v.getD i false).any id = false
    rw [List.any_eq_false]
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨w, hwx2, rfl⟩ := hb
    change v.getD w false ≠ true
    intro hwt
    have hwlt : w < 26 := by rcases hX2Mem w hwx2 with rfl | rfl | rfl | rfl <;> omega
    rcases hInBit p l w hwlt hwt with hwp | hwl
    · rcases hX2Mem w hwx2 with rfl | rfl | rfl | rfl
      · exact hp0 hwp.symm
      · exact hp1 hwp.symm
      · omega
      · omega
    · rcases hX2Mem w hwx2 with rfl | rfl | rfl | rfl
      · omega
      · omega
      · exact hl0 (by omega)
      · exact hl1 (by omega)
  have hNe26 : C.output ≠ 26 := by
    intro heq
    obtain ⟨l, p, hpl, hp0, hp1, hl0, hl1, _, _, _, _⟩ := hAvoidWires 0 0
    have hev := hRight l p hpl
    change (((PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or x2) :: x6 :: C.gates).foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD C.output false = true at hev
    rw [List.foldl_cons, heq] at hev
    have hlen1 : (step (PEqualNP.GenericRejection.incidenceInput {p} {l}) { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x2 }).length = 27 := by
      change (PEqualNP.GenericRejection.incidenceInput {p} {l} ++ [_]).length = 27
      rw [List.length_append, List.length_singleton, hInLen]
    rw [hPref (x6 :: C.gates) _ 26 (by omega)] at hev
    rw [hGate0Eval p l hp0 hp1 hl0 hl1] at hev
    exact Bool.noConfusion hev
  have hNe27 : C.output ≠ 27 := by
    intro heq
    cases hx4 : x4
    · have hMono6 := hMono x6 (by rw [show x7.gates = _ from rfl]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hx6eq : x6 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x3 } := by
        dsimp only [x6]
        rw [hx4]
        rfl
      have hlen3 : x3.length ≤ 2 := by
        have h := hMono6.2
        rw [hx6eq] at h
        exact h
      have hRB1 : ∀ w ∈ x3, w < 27 := by
        intro w hw
        have h := hRB 1 (by change 1 < (({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x2 } : PEqualNP.CircuitLowerBounds.Gate) :: x6 :: C.gates).length; simp) w
        have hga1 : PEqualNP.MetaComplexity.NestedCover.gateAt x7 1 = x6 := rfl
        rw [hga1, hx6eq] at h
        exact h hw
      obtain ⟨w1, w2, hsub3⟩ : ∃ w1 w2 : ℕ, ∀ w ∈ x3, w = w1 ∨ w = w2 := by
        rcases x3 with _ | ⟨a, t1⟩
        · exact ⟨0, 0, fun w hw => False.elim (List.not_mem_nil hw)⟩
        · rcases t1 with _ | ⟨b, t2⟩
          · exact ⟨a, a, fun w hw => by simp only [List.mem_singleton] at hw; exact Or.inl hw⟩
          · rcases t2 with _ | ⟨c, t3⟩
            · exact ⟨a, b, fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; exact hw⟩
            · simp at hlen3
      obtain ⟨l, p, hpl, hp0, hp1, hl0, hl1, hpw1, hlw1, hpw2, hlw2⟩ := hAvoidWires w1 w2
      have hev := hRight l p hpl
      change (((PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or x2) :: x6 :: C.gates).foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD C.output false = true at hev
      rw [List.foldl_cons, List.foldl_cons, heq] at hev
      let v1 := step (PEqualNP.GenericRejection.incidenceInput {p} {l}) { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x2 }
      have hv1len : v1.length = 27 := by
        change (PEqualNP.GenericRejection.incidenceInput {p} {l} ++ [_]).length = 27
        rw [List.length_append, List.length_singleton, hInLen]
      have hv2len : (step v1 x6).length = 28 := by
        change (v1 ++ [_]).length = 28
        rw [List.length_append, List.length_singleton, hv1len]
      rw [hPref C.gates (step v1 x6) 27 (by omega)] at hev
      have hidx : (step v1 x6).getD 27 false = x6.op.eval (x6.inputs.map fun i => v1.getD i false) := by
        change (v1 ++ [_]).getD 27 false = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp only [hv1len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hidx, hx6eq] at hev
      change (x3.map fun i => v1.getD i false).any id = true at hev
      rw [List.any_eq_true] at hev
      obtain ⟨b, hb, hbT⟩ := hev
      rw [List.mem_map] at hb
      obtain ⟨w, hwx3, rfl⟩ := hb
      have hwt : v1.getD w false = true := by simpa only [id_eq] using hbT
      have hwlt27 : w < 27 := hRB1 w hwx3
      by_cases hw26 : w = 26
      · rw [hw26, hGate0Eval p l hp0 hp1 hl0 hl1] at hwt
        exact Bool.noConfusion hwt
      · have hwlt26 : w < 26 := by omega
        have hv1w : v1.getD w false = (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD w false := by
          change (PEqualNP.GenericRejection.incidenceInput {p} {l} ++ [_]).getD w false = _
          rw [List.getD_append _ _ _ _ (by rw [hInLen]; exact hwlt26)]
        rw [hv1w] at hwt
        rcases hInBit p l w hwlt26 hwt with hwp | hwl
        · rcases hsub3 w hwx3 with rfl | rfl
          · exact hpw1 hwp.symm
          · exact hpw2 hwp.symm
        · rcases hsub3 w hwx3 with rfl | rfl
          · exact hlw1 hwl.symm
          · exact hlw2 hwl.symm
    · obtain ⟨Q, hQ⟩ := hSomeQuad
      have hev := hQuad Q hQ
      change (((PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or x2) :: x6 :: C.gates).foldl step (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q))).getD C.output false = false at hev
      rw [List.foldl_cons, List.foldl_cons, heq] at hev
      let v1 := step (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x2 }
      have hv1len : v1.length = 27 := by
        change (_ ++ [_]).length = 27
        rw [List.length_append, List.length_singleton, hInLen]
      have hv2len : (step v1 x6).length = 28 := by
        change (v1 ++ [_]).length = 28
        rw [List.length_append, List.length_singleton, hv1len]
      rw [hPref C.gates (step v1 x6) 27 (by omega)] at hev
      have hx6eq : x6 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } := by
        dsimp only [x6]
        rw [hx4]
        rfl
      have hidx : (step v1 x6).getD 27 false = true := by
        change (v1 ++ [x6.op.eval _]).getD 27 false = true
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp only [hv1len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hx6eq]
        rfl
      rw [hidx] at hev
      exact Bool.noConfusion hev
  have hOutGe28 : 28 ≤ C.output := by omega
  have hOutLt : C.output < 28 + C.size := by
    by_contra hge
    have hge : 28 + C.size ≤ C.output := Nat.le_of_not_lt hge
    obtain ⟨l, p, hpl⟩ := hAnyInc
    have hev := hRight l p hpl
    change (x7.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD C.output false = true at hev
    have hl : (x7.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).length = 28 + C.size := by
      rw [hLen, hInLen]
      change 26 + (C.size + 2) = 28 + C.size
      omega
    have hdf : (x7.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
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
    have hmem : C.gates[C.output - 28]'hj ∈ x7.gates :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.getElem_mem hj))
    have hm := (hMono (C.gates[C.output - 28]'hj) hmem).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  rcases hOp with hAnd | hOr
  · exact hOutAnd C x2 x3 x4 hx2 ⟨hOutGe28, hOutLt⟩ hAnd hMono hRB hRight hQuad hNoDeg
  · exact hOutOr C x2 x3 x4 hx2 ⟨hOutGe28, hOutLt⟩ hOr hMono hRB hRight hQuad hNoDeg
