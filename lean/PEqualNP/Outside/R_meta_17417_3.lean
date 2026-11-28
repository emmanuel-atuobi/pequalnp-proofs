import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17417_3
    (hOutAnd :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
      ∀ (x4 x5 : Fin (7 : ℕ)),
        x1 x4 x5 →
        have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => x2 x7 ∧ (2 : ℕ) ≤ x7.lineDeg (14 : ℕ) {↑x4} ∧ (2 : ℕ) ≤ x7.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x5};
        ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (g0 : ℕ) (u0 v0 : Fin (14 : ℕ)),
          x7 x8 →
          (14 : ℕ) ≤ x8.output ∧ PEqualNP.ReadTwo.isAnd x8 (x8.output - (14 : ℕ)) →
          PEqualNP.ReadTwo.isAnd x8 g0 ∧ (14 : ℕ) + g0 ≠ x8.output →
          have x14 : Fin (14 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput u0 v0;
          PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x8 g0 x14 = Bool.true ∧ x8.eval (List.ofFn x14) = Bool.false →
          (2 : ℕ) ≤ (PEqualNP.MetaComplexity.SingleLevel.andDepths x8 (14 : ℕ)).getD x8.output (0 : ℕ) →
          ¬x3 x8 →
          ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), x7 x13 ∧ x3 x13)
    (hOutOr :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
      ∀ (x4 x5 : Fin (7 : ℕ)),
        x1 x4 x5 →
        have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => x2 x7 ∧ (2 : ℕ) ≤ x7.lineDeg (14 : ℕ) {↑x4} ∧ (2 : ℕ) ≤ x7.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x5};
        ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (g0 : ℕ) (u0 v0 : Fin (14 : ℕ)),
          x7 x8 →
          (14 : ℕ) ≤ x8.output ∧ PEqualNP.ReadTwo.isOr x8 (x8.output - (14 : ℕ)) →
          PEqualNP.ReadTwo.isAnd x8 g0 ∧ (14 : ℕ) + g0 ≠ x8.output →
          have x14 : Fin (14 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput u0 v0;
          PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x8 g0 x14 = Bool.true ∧ x8.eval (List.ofFn x14) = Bool.false →
          (2 : ℕ) ≤ (PEqualNP.MetaComplexity.SingleLevel.andDepths x8 (14 : ℕ)).getD x8.output (0 : ℕ) →
          ¬x3 x8 →
          ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), x7 x13 ∧ x3 x13) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 x5 : Fin (7 : ℕ)),   x1 x4 x5 →     have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => x2 x7 ∧ (2 : ℕ) ≤ x7.lineDeg (14 : ℕ) {↑x4} ∧ (2 : ℕ) ≤ x7.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x5};     ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),       x7 x8 →         (¬∀ (x10 : ℕ),               PEqualNP.ReadTwo.isAnd x8 x10 →                 ∀ (x12 x13 : Fin (14 : ℕ)),                   have x14 : Fin (14 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput x12 x13;                   PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x8 x10 x14 = Bool.true → x8.eval (List.ofFn x14) = Bool.true) →           (2 : ℕ) ≤ (PEqualNP.MetaComplexity.SingleLevel.andDepths x8 (14 : ℕ)).getD x8.output (0 : ℕ) → ¬x3 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), x7 x13 ∧ x3 x13 := by
  classical
  intro x1 x2 x3 p0 l0 hInc x7 C h7 hNotSound hDep hNotNodup
  dsimp only at hNotSound
  push Not at hNotSound
  obtain ⟨g0, hg0And, u0, v0, hg0True, hEvNe⟩ := hNotSound
  have hEvFalse : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput u0 v0)) = Bool.false :=
    Bool.eq_false_of_ne_true hEvNe
  have hg0NeOut : 14 + g0 ≠ C.output := by
    intro hEq
    have h1 : (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u0 v0))).getD (14 + g0) false = true := hg0True
    have h2 : (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u0 v0))).getD C.output false = false := hEvFalse
    rw [hEq] at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
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
  have hGates := h7.1.2.1
  have hSem := h7.1.2.2
  have hOutGe : 14 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 14 := Nat.lt_of_not_ge hlt
    let f : Fin 14 → Bool := fun i => decide (i.val = C.output)
    have hev : C.eval (List.ofFn f) = Bool.true := by
      change (C.gates.foldl step (List.ofFn f)).getD C.output false = true
      rw [hPref C.gates (List.ofFn f) C.output (by simp only [List.length_ofFn]; exact hlt)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hlt, ↓reduceDIte, Option.getD_some, f, decide_eq_true_eq]
    obtain ⟨p, l, _, hpT, hlT⟩ := (hSem f).mp hev
    have hpEq : p.val = C.output := by
      simp only [f, Fin.val_castAdd, decide_eq_true_eq] at hpT
      exact hpT
    have hlEq : 7 + l.val = C.output := by
      simp only [f, Fin.val_natAdd, decide_eq_true_eq] at hlT
      exact hlT
    omega
  have hOutLt : C.output < 14 + C.size := by
    by_contra hge
    have hge : 14 + C.size ≤ C.output := Nat.le_of_not_lt hge
    let f : Fin 14 → Bool := fun _ => Bool.true
    have hev : C.eval (List.ofFn f) = Bool.true :=
      (hSem f).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
    change (C.gates.foldl step (List.ofFn f)).getD C.output false = true at hev
    have hl : (C.gates.foldl step (List.ofFn f)).length = 14 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn f)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hj : C.output - 14 < C.gates.length := by
    change C.output - 14 < C.size
    omega
  have hSome : C.gates[C.output - 14]? = Option.some (C.gates[C.output - 14]'hj) :=
    List.getElem?_eq_getElem hj
  have hOp0 := (hGates (C.output - 14) (C.gates[C.output - 14]'hj) hSome).1
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 14) = C.gates[C.output - 14]'hj := by
    change C.gates.getD (C.output - 14) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ hj
  rw [← hge] at hOp0
  rcases hOp0 with hAnd | hOr
  · exact hOutAnd p0 l0 hInc C g0 u0 v0 h7 ⟨hOutGe, hj, hAnd⟩ ⟨hg0And, hg0NeOut⟩ ⟨hg0True, hEvFalse⟩ hDep hNotNodup
  · exact hOutOr p0 l0 hInc C g0 u0 v0 h7 ⟨hOutGe, hj, hOr⟩ ⟨hg0And, hg0NeOut⟩ ⟨hg0True, hEvFalse⟩ hDep hNotNodup
