import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18127_4
    (hSharedAnd :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x7 u v : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        x2 x4 →
        ¬x3 x4 →
        (14 : ℕ) ≤ x4.output ∧ x4.output < (14 : ℕ) + x4.size →
        (14 : ℕ) ≤ x7 ∧ x7 < (14 : ℕ) + x4.size ∧ x7 ≠ x4.output →
        (2 : ℕ) ≤ List.count x7 (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) →
        x4.gates[x7 - (14 : ℕ)]? = Option.some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        g.inputs = [u, v] ∧ u ≠ v ∧ u < x7 ∧ v < x7 →
        (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} →
        (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} →
        ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x2 x10 ∧ x3 x10 ∧ (2 : ℕ) ≤ x10.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x10.lineDeg (14 : ℕ) {(7 : ℕ)})
    (hSharedOr :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x7 u v : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        x2 x4 →
        ¬x3 x4 →
        (14 : ℕ) ≤ x4.output ∧ x4.output < (14 : ℕ) + x4.size →
        (14 : ℕ) ≤ x7 ∧ x7 < (14 : ℕ) + x4.size ∧ x7 ≠ x4.output →
        (2 : ℕ) ≤ List.count x7 (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) →
        x4.gates[x7 - (14 : ℕ)]? = Option.some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
        g.inputs = [u, v] ∧ u ≠ v ∧ u < x7 ∧ v < x7 →
        (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} →
        (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} →
        ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x2 x10 ∧ x3 x10 ∧ (2 : ℕ) ≤ x10.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x10.lineDeg (14 : ℕ) {(7 : ℕ)}) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2 x4 → ¬x3 x4 → (∃ (x7 : ℕ), (14 : ℕ) ≤ x7 ∧ x7 ≠ x4.output ∧ (2 : ℕ) ≤ List.count x7 (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x2 x10 ∧ x3 x10 ∧ (2 : ℕ) ≤ x10.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x10.lineDeg (14 : ℕ) {(7 : ℕ)} := by
  classical
  intro x1 x2 x3 C hValid hNotNodup hShared hDeg0 hDeg7
  have hGates := hValid.2.1
  have hSpec := hValid.2.2
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
  have hOutGe : 14 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 14 := Nat.lt_of_not_ge hlt
    let idx : Fin 14 := ⟨C.output, hlt⟩
    let f : Fin 14 → Bool := fun i => decide (i = idx)
    have hEvTrue : C.eval (List.ofFn f) = true := by
      change (C.gates.foldl step (List.ofFn f)).getD C.output false = true
      rw [hPref C.gates (List.ofFn f) C.output (by simp only [List.length_ofFn]; exact hlt)]
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      have heq : (⟨C.output, hlt⟩ : Fin 14) = idx := rfl
      simp only [f, heq, decide_true]
    obtain ⟨p, l, _, hp, hl⟩ := (hSpec f).mp hEvTrue
    simp only [f, decide_eq_true_eq] at hp hl
    have heq := hp.trans hl.symm
    have hv := congrArg Fin.val heq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hOutLt : C.output < 14 + C.size := by
    by_contra hge
    have hge : 14 + C.size ≤ C.output := Nat.le_of_not_lt hge
    let f : Fin 14 → Bool := fun _ => true
    have hEvTrue : C.eval (List.ofFn f) = true :=
      (hSpec f).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
    change (C.gates.foldl step (List.ofFn f)).getD C.output false = true at hEvTrue
    have hlen : (C.gates.foldl step (List.ofFn f)).length = 14 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn f)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hEvTrue
    exact Bool.noConfusion hEvTrue
  obtain ⟨w, hwGe, hwNe, hwCnt⟩ := hShared
  have hwMemFlat : w ∈ List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨gr, hgrMem, hwInGr⟩ := List.mem_flatMap.mp hwMemFlat
  obtain ⟨ri, hriLt, hgrEq⟩ := List.mem_iff_getElem.mp hgrMem
  have hgrSome : C.gates[ri]? = Option.some gr := by
    rw [List.getElem?_eq_getElem hriLt, hgrEq]
  obtain ⟨_, u0, v0, hgrIn, _, hu0Lt, hv0Lt⟩ := hGates ri gr hgrSome
  rw [hgrIn] at hwInGr
  have hwLt : w < 14 + C.size := by
    change w < 14 + C.gates.length
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwInGr
    rcases hwInGr with rfl | rfl <;> omega
  have hkLt : w - 14 < C.gates.length := by
    change w < 14 + C.gates.length at hwLt
    omega
  let g : PEqualNP.CircuitLowerBounds.Gate := C.gates[w - 14]'hkLt
  have hgSome : C.gates[w - 14]? = Option.some g := List.getElem?_eq_getElem hkLt
  obtain ⟨hgOp, u, v, hgIn, huvNe, huLt, hvLt⟩ := hGates (w - 14) g hgSome
  have huLtW : u < w := by omega
  have hvLtW : v < w := by omega
  rcases hgOp with hAnd | hOr
  · exact hSharedAnd C w u v g hValid hNotNodup ⟨hOutGe, hOutLt⟩ ⟨hwGe, hwLt, hwNe⟩ hwCnt hgSome hAnd ⟨hgIn, huvNe, huLtW, hvLtW⟩ hDeg0 hDeg7
  · exact hSharedOr C w u v g hValid hNotNodup ⟨hOutGe, hOutLt⟩ ⟨hwGe, hwLt, hwNe⟩ hwCnt hgSome hOr ⟨hgIn, huvNe, huLtW, hvLtW⟩ hDeg0 hDeg7
