import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18057_3
    (hOutAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        x1.size ≤ (124 : ℕ) →
        (42 : ℕ) ≤ x1.output ∧ PEqualNP.ReadTwo.isAnd x1 (x1.output - (42 : ℕ)) →
        (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true) →
        have x6 : ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (154640061441 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (3436108316976 : ℕ), (1168315262978 : ℕ)].getD ↑x2 (0 : ℕ);
        have x7 : ℕ → Prop := fun (x7 : ℕ) => ∃ (x8 : ℕ), PEqualNP.ReadTwo.isAnd x1 x8 ∧ (PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x8 fun (x9 : Fin (42 : ℕ)) => x7.testBit ↑x9) = Bool.true;
        x7 (148193411399 : ℕ) →
        x7 x6 →
        (33 : ℕ) ≤ {x10 ∈ Finset.range x1.size | (PEqualNP.SharedBlockCost.isOrOp (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op && !PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x10 fun (x11 : Fin (42 : ℕ)) => x6.testBit ↑x11) = Bool.true}.card →
        have x11 : ℕ := if ↑x2 < (4 : ℕ) then (67 : ℕ) else if ↑x2 < (9 : ℕ) then (72 : ℕ) else (76 : ℕ);
        ∃ (x12 : (x12 : Fin x11) → Fin (x1.size - ↑x12)) (x13 : Fin x11 → ℕ), ∀ (x14 : Fin (42 : ℕ) → Bool), (∀ (x15 : Fin (42 : ℕ)), ((148193411399 : ℕ) ||| x6).testBit ↑x15 = Bool.true → x14 x15 = Bool.false) → (List.foldl (fun (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : Fin x11) => PEqualNP.CircuitMoves.eraseGate (42 : ℕ) x16 (↑(x12 x17)) (x13 x17)) x1 (List.finRange x11)).eval (List.ofFn x14) = x1.eval (List.ofFn x14))
    (hOutOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        x1.size ≤ (124 : ℕ) →
        (42 : ℕ) ≤ x1.output ∧ PEqualNP.ReadTwo.isOr x1 (x1.output - (42 : ℕ)) →
        (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true) →
        have x6 : ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (154640061441 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (3436108316976 : ℕ), (1168315262978 : ℕ)].getD ↑x2 (0 : ℕ);
        have x7 : ℕ → Prop := fun (x7 : ℕ) => ∃ (x8 : ℕ), PEqualNP.ReadTwo.isAnd x1 x8 ∧ (PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x8 fun (x9 : Fin (42 : ℕ)) => x7.testBit ↑x9) = Bool.true;
        x7 (148193411399 : ℕ) →
        x7 x6 →
        (33 : ℕ) ≤ {x10 ∈ Finset.range x1.size | (PEqualNP.SharedBlockCost.isOrOp (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op && !PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x10 fun (x11 : Fin (42 : ℕ)) => x6.testBit ↑x11) = Bool.true}.card →
        have x11 : ℕ := if ↑x2 < (4 : ℕ) then (67 : ℕ) else if ↑x2 < (9 : ℕ) then (72 : ℕ) else (76 : ℕ);
        ∃ (x12 : (x12 : Fin x11) → Fin (x1.size - ↑x12)) (x13 : Fin x11 → ℕ), ∀ (x14 : Fin (42 : ℕ) → Bool), (∀ (x15 : Fin (42 : ℕ)), ((148193411399 : ℕ) ||| x6).testBit ↑x15 = Bool.true → x14 x15 = Bool.false) → (List.foldl (fun (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : Fin x11) => PEqualNP.CircuitMoves.eraseGate (42 : ℕ) x16 (↑(x12 x17)) (x13 x17)) x1 (List.finRange x11)).eval (List.ofFn x14) = x1.eval (List.ofFn x14)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (124 : ℕ) →       (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ (fun (x6 : Fin (42 : ℕ) → Bool) => ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true) x5) →         have x6 : ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (154640061441 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (3436108316976 : ℕ), (1168315262978 : ℕ)].getD ↑x2 (0 : ℕ);         have x7 : ℕ → Prop := fun (x7 : ℕ) => ∃ (x8 : ℕ), PEqualNP.ReadTwo.isAnd x1 x8 ∧ (PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x8 fun (x9 : Fin (42 : ℕ)) => x7.testBit ↑x9) = Bool.true;         x7 (148193411399 : ℕ) →           x7 x6 →             (33 : ℕ) ≤ {x10 ∈ Finset.range x1.size | ((Option.map (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x12 : ℕ) => Bool.false) Bool.false x11.op) x1.gates[x10]?).getD Bool.false && !PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x10 fun (x11 : Fin (42 : ℕ)) => x6.testBit ↑x11) = Bool.true}.card →               have x11 : ℕ := if ↑x2 < (4 : ℕ) then (67 : ℕ) else if ↑x2 < (9 : ℕ) then (72 : ℕ) else (76 : ℕ);               ∃ (x12 : (x12 : Fin x11) → Fin (x1.size - ↑x12)) (x13 : Fin x11 → ℕ), ∀ (x14 : Fin (42 : ℕ) → Bool), (∀ (x15 : Fin (42 : ℕ)), ((148193411399 : ℕ) ||| x6).testBit ↑x15 = Bool.true → x14 x15 = Bool.false) → (List.foldl (fun (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : Fin x11) => PEqualNP.CircuitMoves.eraseGate (42 : ℕ) x16 (↑(x12 x17)) (x13 x17)) x1 (List.finRange x11)).eval (List.ofFn x14) = x1.eval (List.ofFn x14) := by
  intro C x2 hM hSz hComp x6 x7 hA1 hA2 hCard x11
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
  let e0 : Fin 42 → Bool := fun k => decide (k = (0 : Fin 42) ∨ k = (21 : Fin 42))
  have hCe0 : C.eval (List.ofFn e0) = true :=
    (hComp e0).mpr ⟨(0 : Fin 42), (21 : Fin 42), by decide, by decide, by decide⟩
  have hOutLt : C.output < 42 + C.size := by
    by_contra hge
    have hge : 42 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hev : (C.gates.foldl step (List.ofFn e0)).getD C.output false = true := hCe0
    have hl : (C.gates.foldl step (List.ofFn e0)).length = 42 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn e0)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hOutGe : 42 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 42 := Nat.lt_of_not_ge hlt
    let w0 : Fin 42 := ⟨C.output, hlt⟩
    let fS : Fin 42 → Bool := fun k => decide (k = w0)
    have hCfS : C.eval (List.ofFn fS) = false := by
      cases h : C.eval (List.ofFn fS)
      · rfl
      · obtain ⟨a, b, hab, ha, hb⟩ := (hComp fS).mp h
        have ha' : a = w0 := of_decide_eq_true ha
        have hb' : b = w0 := of_decide_eq_true hb
        rw [ha', hb'] at hab
        omega
    have hev : (C.gates.foldl step (List.ofFn fS)).getD C.output false = false := hCfS
    rw [hPref C.gates (List.ofFn fS) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
    simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
    change decide (w0 = w0) = false at hev
    rw [decide_eq_true rfl] at hev
    exact Bool.noConfusion hev
  have hFiltEq :
      {x10 ∈ Finset.range C.size | ((Option.map (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false x11.op) C.gates[x10]?).getD Bool.false && !PEqualNP.EdgeOwnership.gateVal (42 : ℕ) C x10 fun (x11 : Fin (42 : ℕ)) => x6.testBit ↑x11) = Bool.true} =
      {x10 ∈ Finset.range C.size | (PEqualNP.SharedBlockCost.isOrOp (PEqualNP.MetaComplexity.NestedCover.gateAt C x10).op && !PEqualNP.EdgeOwnership.gateVal (42 : ℕ) C x10 fun (x11 : Fin (42 : ℕ)) => x6.testBit ↑x11) = Bool.true} := by
    apply Finset.filter_congr
    intro j hj
    have hjLt : j < C.gates.length := Finset.mem_range.mp hj
    have hget : C.gates[j]? = some (C.gates[j]'hjLt) := List.getElem?_eq_getElem hjLt
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j]'hjLt :=
      List.getD_eq_getElem _ _ hjLt
    have hopEq : (Option.map (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false x11.op) C.gates[j]?).getD Bool.false =
        PEqualNP.SharedBlockCost.isOrOp (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op := by
      rw [hget, hga]
      change PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false (C.gates[j]'hjLt).op =
        PEqualNP.SharedBlockCost.isOrOp (C.gates[j]'hjLt).op
      cases (C.gates[j]'hjLt).op <;> rfl
    rw [hopEq]
  have hCard' : (33 : ℕ) ≤ {x10 ∈ Finset.range C.size | (PEqualNP.SharedBlockCost.isOrOp (PEqualNP.MetaComplexity.NestedCover.gateAt C x10).op && !PEqualNP.EdgeOwnership.gateVal (42 : ℕ) C x10 fun (x11 : Fin (42 : ℕ)) => x6.testBit ↑x11) = Bool.true}.card := by
    rw [← hFiltEq]
    exact hCard
  have hkLt : C.output - 42 < C.gates.length := by change C.output - 42 < C.size; omega
  have hgaOut : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 42) = C.gates[C.output - 42]'hkLt :=
    List.getD_eq_getElem _ _ hkLt
  rcases (hM (C.gates[C.output - 42]'hkLt) (List.getElem_mem hkLt)).1 with hAnd | hOr
  · exact hOutAnd C x2 hM hSz ⟨hOutGe, hkLt, by rw [hgaOut]; exact hAnd⟩ hComp hA1 hA2 hCard'
  · exact hOutOr C x2 hM hSz ⟨hOutGe, hkLt, by rw [hgaOut]; exact hOr⟩ hComp hA1 hA2 hCard'
