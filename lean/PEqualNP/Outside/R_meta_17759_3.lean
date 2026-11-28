import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17759_3
    (hSingleWire :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        (26 : ℕ) ≤ u ∧ u < (26 : ℕ) + x1.size →
        (∀ (x5 x6 : Finset (Fin (13 : ℕ))),
          (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD u Bool.false = Bool.true ↔
          ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
        (63 : ℕ) ≤ x1.size)
    (hTwoWires :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        (26 : ℕ) ≤ u ∧ u < v ∧ v < (26 : ℕ) + x1.size →
        (∀ (x5 x6 : Finset (Fin (13 : ℕ))),
          have w : List Bool := x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6));
          (w.getD u Bool.false && w.getD v Bool.false) = Bool.true ↔
          ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
        (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (1 : ℕ) ≤ x1.size → (63 : ℕ) ≤ x1.size := by
  intro C xs hM hLenLe hSpec _
  let inp : Finset (Fin 13) → Finset (Fin 13) → List Bool := fun A B =>
    List.ofFn fun (x8 : Fin 26) =>
      if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat 13 ↑x8 ∈ A) else Decidable.decide (Fin.ofNat 13 ↑x8 ∈ B)
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
  have hInpLen : ∀ A B : Finset (Fin 13), (inp A B).length = 26 := by
    intro A B
    exact List.length_ofFn
  have hWireBounds : ∀ w : ℕ,
      (∀ A B : Finset (Fin 13),
        (∃ p ∈ A, ∃ l ∈ B, (p.val + l.val) % 13 ∈ [(0 : ℕ), 1, 3, 9]) →
        (C.wires (inp A B)).getD w false = true) →
      26 ≤ w ∧ w < 26 + C.size := by
    intro w hw
    have h00 : ∃ p ∈ ({(0 : Fin 13)} : Finset (Fin 13)), ∃ l ∈ ({(0 : Fin 13)} : Finset (Fin 13)),
        (p.val + l.val) % 13 ∈ [(0 : ℕ), 1, 3, 9] :=
      ⟨0, Finset.mem_singleton_self _, 0, Finset.mem_singleton_self _, by decide⟩
    have h10 : ∃ p ∈ ({(1 : Fin 13)} : Finset (Fin 13)), ∃ l ∈ ({(0 : Fin 13)} : Finset (Fin 13)),
        (p.val + l.val) % 13 ∈ [(0 : ℕ), 1, 3, 9] :=
      ⟨1, Finset.mem_singleton_self _, 0, Finset.mem_singleton_self _, by decide⟩
    have h01 : ∃ p ∈ ({(0 : Fin 13)} : Finset (Fin 13)), ∃ l ∈ ({(1 : Fin 13)} : Finset (Fin 13)),
        (p.val + l.val) % 13 ∈ [(0 : ℕ), 1, 3, 9] :=
      ⟨0, Finset.mem_singleton_self _, 1, Finset.mem_singleton_self _, by decide⟩
    have hLt : w < 26 + C.size := by
      by_contra hge
      have hge : 26 + C.size ≤ w := Nat.le_of_not_lt hge
      have hT := hw {0} {0} h00
      change (C.gates.foldl step (inp {0} {0})).getD w false = true at hT
      have hL : (C.gates.foldl step (inp {0} {0})).length = 26 + C.size := by
        rw [hLen, hInpLen]
        rfl
      have hF : (C.gates.foldl step (inp {0} {0})).getD w false = false :=
        List.getD_eq_default _ _ (by omega)
      rw [hF] at hT
      exact Bool.noConfusion hT
    have hGe : 26 ≤ w := by
      by_contra hlt
      have hlt : w < 26 := Nat.lt_of_not_ge hlt
      by_cases h13 : w < 13
      · by_cases h0 : w = 0
        · have hT := hw {1} {0} h10
          change (C.gates.foldl step (inp {1} {0})).getD w false = true at hT
          rw [hPref C.gates _ w (by rw [hInpLen]; exact hlt), h0] at hT
          have hF : (inp {1} {0}).getD 0 false = false := by decide
          rw [hF] at hT
          exact Bool.noConfusion hT
        · have hT := hw {0} {0} h00
          change (C.gates.foldl step (inp {0} {0})).getD w false = true at hT
          rw [hPref C.gates _ w (by rw [hInpLen]; exact hlt)] at hT
          have hF : ∀ i : Fin 13, i.val ≠ 0 → (inp {0} {0}).getD i.val false = false := by decide
          rw [hF ⟨w, h13⟩ h0] at hT
          exact Bool.noConfusion hT
      · by_cases h13eq : w = 13
        · have hT := hw {0} {1} h01
          change (C.gates.foldl step (inp {0} {1})).getD w false = true at hT
          rw [hPref C.gates _ w (by rw [hInpLen]; exact hlt), h13eq] at hT
          have hF : (inp {0} {1}).getD 13 false = false := by decide
          rw [hF] at hT
          exact Bool.noConfusion hT
        · have hT := hw {0} {0} h00
          change (C.gates.foldl step (inp {0} {0})).getD w false = true at hT
          rw [hPref C.gates _ w (by rw [hInpLen]; exact hlt)] at hT
          have hF : ∀ i : Fin 26, 13 < i.val → (inp {0} {0}).getD i.val false = false := by decide
          rw [hF ⟨w, hlt⟩ (by show 13 < w; omega)] at hT
          exact Bool.noConfusion hT
    exact ⟨hGe, hLt⟩
  cases xs with
  | nil =>
    have hEmp := (hSpec ∅ ∅).mp (by rfl)
    obtain ⟨p, hp, _⟩ := hEmp
    exact False.elim (Finset.notMem_empty p hp)
  | cons u rest =>
    cases rest with
    | nil =>
      have hSpec1 : ∀ A B : Finset (Fin 13),
          (C.wires (inp A B)).getD u false = true ↔
          ∃ p ∈ A, ∃ l ∈ B, (p.val + l.val) % 13 ∈ [(0 : ℕ), 1, 3, 9] := by
        intro A B
        have h1 := hSpec A B
        change ([((C.wires (inp A B)).getD u false)].all id = true) ↔ _ at h1
        have heq : ([((C.wires (inp A B)).getD u false)].all id) = (C.wires (inp A B)).getD u false := by
          cases (C.wires (inp A B)).getD u false <;> rfl
        rw [heq] at h1
        exact h1
      have hu := hWireBounds u (fun A B h => (hSpec1 A B).mpr h)
      exact hSingleWire C u hM hu hSpec1
    | cons v tail =>
      cases tail with
      | cons _ _ =>
        simp only [List.length_cons] at hLenLe
        omega
      | nil =>
        have hSpec2 : ∀ A B : Finset (Fin 13),
            ((C.wires (inp A B)).getD u false && (C.wires (inp A B)).getD v false) = true ↔
            ∃ p ∈ A, ∃ l ∈ B, (p.val + l.val) % 13 ∈ [(0 : ℕ), 1, 3, 9] := by
          intro A B
          have h1 := hSpec A B
          change ([((C.wires (inp A B)).getD u false), ((C.wires (inp A B)).getD v false)].all id = true) ↔ _ at h1
          have heq : ([((C.wires (inp A B)).getD u false), ((C.wires (inp A B)).getD v false)].all id) =
              ((C.wires (inp A B)).getD u false && (C.wires (inp A B)).getD v false) := by
            cases (C.wires (inp A B)).getD u false <;> cases (C.wires (inp A B)).getD v false <;> rfl
          rw [heq] at h1
          exact h1
        have hu := hWireBounds u (fun A B h => (Bool.and_eq_true _ _ |>.mp ((hSpec2 A B).mpr h)).1)
        have hv := hWireBounds v (fun A B h => (Bool.and_eq_true _ _ |>.mp ((hSpec2 A B).mpr h)).2)
        rcases lt_trichotomy u v with huv | huv | hvu
        · exact hTwoWires C u v hM ⟨hu.1, huv, hv.2⟩ hSpec2
        · subst huv
          have hSpec1 : ∀ A B : Finset (Fin 13),
              (C.wires (inp A B)).getD u false = true ↔
              ∃ p ∈ A, ∃ l ∈ B, (p.val + l.val) % 13 ∈ [(0 : ℕ), 1, 3, 9] := by
            intro A B
            have h1 := hSpec2 A B
            rw [Bool.and_self] at h1
            exact h1
          exact hSingleWire C u hM hu hSpec1
        · refine hTwoWires C v u hM ⟨hv.1, hvu, hu.2⟩ ?_
          intro A B
          dsimp only
          rw [Bool.and_comm]
          exact hSpec2 A B
