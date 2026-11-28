import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17744_3
    (hHasAndOut :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      ∀ (x2 x3 : Fin (13 : ℕ)) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit),
        x2 ∈ x1 x3 →
        x4.gates = x5.gates →
        PEqualNP.MetaComplexity.Monotone2 x4 →
        (26 : ℕ) ≤ x4.output ∧ x4.output < (26 : ℕ) + x4.size →
        (26 : ℕ) ≤ x5.output ∧ x5.output < (26 : ℕ) + x4.size →
        x4.output ≠ x5.output →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x9 x10 : Fin (13 : ℕ)), x9 ≠ x2 → x10 ≠ x3 → x9 ∈ x1 x10 → ∀ x14 ∈ [x4, x5], x14.eval (PEqualNP.GenericRejection.incidenceInput {x9} {x10}) = Bool.true) →
        have x10 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Finset (Fin (13 : ℕ))) := fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) => {x11 ∈ PEqualNP.HeptadCover.quadrangles x1 | x10.eval (PEqualNP.GenericRejection.incidenceInput (x11.erase x2) ((PEqualNP.HeptadCover.missLines x1 x11).erase x3)) = Bool.true};
        Disjoint (x10 x4) (x10 x5) →
        (x10 x4).Nonempty →
        (x10 x5).Nonempty →
        (56 : ℕ) ≤ x4.size)
    (hBothOrOut :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      ∀ (x2 x3 : Fin (13 : ℕ)) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit),
        x2 ∈ x1 x3 →
        x4.gates = x5.gates →
        PEqualNP.MetaComplexity.Monotone2 x4 →
        (26 : ℕ) ≤ x4.output ∧ x4.output < x5.output ∧ x5.output < (26 : ℕ) + x4.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x5.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x9 x10 : Fin (13 : ℕ)), x9 ≠ x2 → x10 ≠ x3 → x9 ∈ x1 x10 → ∀ x14 ∈ [x4, x5], x14.eval (PEqualNP.GenericRejection.incidenceInput {x9} {x10}) = Bool.true) →
        have x10 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Finset (Fin (13 : ℕ))) := fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) => {x11 ∈ PEqualNP.HeptadCover.quadrangles x1 | x10.eval (PEqualNP.GenericRejection.incidenceInput (x11.erase x2) ((PEqualNP.HeptadCover.missLines x1 x11).erase x3)) = Bool.true};
        Disjoint (x10 x4) (x10 x5) →
        (x10 x4).Nonempty →
        (x10 x5).Nonempty →
        (56 : ℕ) ≤ x4.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; ∀ (x2 x3 : Fin (13 : ℕ)) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit),   x2 ∈ x1 x3 →     x4.gates = x5.gates →       PEqualNP.MetaComplexity.Monotone2 x4 →         (∀ (x9 x10 : Fin (13 : ℕ)), x9 ≠ x2 → x10 ≠ x3 → x9 ∈ x1 x10 → ∀ x14 ∈ [x4, x5], x14.eval (PEqualNP.GenericRejection.incidenceInput {x9} {x10}) = Bool.true) →           have x10 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Finset (Fin (13 : ℕ))) := fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) => {x11 ∈ PEqualNP.HeptadCover.quadrangles x1 | x10.eval (PEqualNP.GenericRejection.incidenceInput (x11.erase x2) ((PEqualNP.HeptadCover.missLines x1 x11).erase x3)) = Bool.true};           Disjoint (x10 x4) (x10 x5) → (x10 x4).Nonempty → (x10 x5).Nonempty → (56 : ℕ) ≤ x4.size := by
  classical
  intro x1 x2 x3 x4 x5 hIn hEqG hMono hInc x10 hDisj hNE4 hNE5
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
  let pt : Fin 13 → ℕ → Fin 13 := fun l d => ⟨(l.val + d) % 13, Nat.mod_lt _ (by decide)⟩
  have hPtMem : ∀ l : Fin 13, pt l 0 ∈ x1 l ∧ pt l 1 ∈ x1 l ∧ pt l 3 ∈ x1 l := by
    change ∀ l : Fin 13, pt l 0 ∈ PEqualNP.HeptadCover.singerLines3 l ∧
      pt l 1 ∈ PEqualNP.HeptadCover.singerLines3 l ∧ pt l 3 ∈ PEqualNP.HeptadCover.singerLines3 l
    decide
  have hPtNe : ∀ l : Fin 13, pt l 0 ≠ pt l 1 ∧ pt l 0 ≠ pt l 3 ∧ pt l 1 ≠ pt l 3 := by
    decide
  have hPickLine : ∀ a b : Fin 13, ∃ l : Fin 13, l ≠ a ∧ l ≠ b := by
    intro a b
    by_cases h0 : (0 : Fin 13) ≠ a ∧ (0 : Fin 13) ≠ b
    · exact ⟨0, h0⟩
    · by_cases h1 : (1 : Fin 13) ≠ a ∧ (1 : Fin 13) ≠ b
      · exact ⟨1, h1⟩
      · refine ⟨2, ?_, ?_⟩ <;> intro h <;> have hv := congrArg Fin.val h <;>
          simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at * <;> omega
  have hPickPt : ∀ (l a b : Fin 13), ∃ p : Fin 13, p ∈ x1 l ∧ p ≠ a ∧ p ≠ b := by
    intro l a b
    have hm := hPtMem l
    have hn := hPtNe l
    by_cases h0 : pt l 0 ≠ a ∧ pt l 0 ≠ b
    · exact ⟨pt l 0, hm.1, h0⟩
    · by_cases h1 : pt l 1 ≠ a ∧ pt l 1 ≠ b
      · exact ⟨pt l 1, hm.2.1, h1⟩
      · refine ⟨pt l 3, hm.2.2, ?_, ?_⟩
        · intro heq
          by_cases h0a : pt l 0 = a
          · exact hn.2.1 (h0a.trans heq.symm)
          · have h0b : pt l 0 = b := by tauto
            by_cases h1a : pt l 1 = a
            · exact hn.2.2 (h1a.trans heq.symm)
            · have h1b : pt l 1 = b := by tauto
              exact hn.1 (h0b.trans h1b.symm)
        · intro heq
          by_cases h0b : pt l 0 = b
          · exact hn.2.1 (h0b.trans heq.symm)
          · have h0a : pt l 0 = a := by tauto
            by_cases h1b : pt l 1 = b
            · exact hn.2.2 (h1b.trans heq.symm)
            · have h1a : pt l 1 = a := by tauto
              exact hn.1 (h0a.trans h1a.symm)
  have hInpLen : ∀ (X Y : Finset (Fin 13)), (PEqualNP.GenericRejection.incidenceInput X Y).length = 26 := by
    intro X Y
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y))).length = 26
    simp only [List.length_append, List.length_ofFn]
  have hBounds : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      C ∈ [x4, x5] → 26 ≤ C.output ∧ C.output < 26 + C.size := by
    intro C hC
    constructor
    · by_contra hlt
      have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
      by_cases h13 : C.output < 13
      · let p0 : Fin 13 := ⟨C.output, h13⟩
        obtain ⟨l, hlx3, _⟩ := hPickLine x3 x3
        obtain ⟨p, hpl, hpx2, hpp0⟩ := hPickPt l x2 p0
        have hev := hInc p l hpx2 hlx3 hpl C hC
        change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD C.output false = true at hev
        rw [hPref C.gates _ C.output (by rw [hInpLen]; exact hlt)] at hev
        change ((List.ofFn (fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn (fun m : Fin 13 => decide (m ∈ ({l} : Finset (Fin 13))))).getD C.output false) = true at hev
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13)] at hev
        rw [List.getElem?_ofFn] at hev
        simp only [h13, ↓reduceDIte, Option.getD_some, decide_eq_true_eq, Finset.mem_singleton] at hev
        exact hpp0 hev.symm
      · let l0 : Fin 13 := ⟨C.output - 13, by omega⟩
        obtain ⟨l, hlx3, hll0⟩ := hPickLine x3 l0
        obtain ⟨p, hpl, hpx2, _⟩ := hPickPt l x2 x2
        have hev := hInc p l hpx2 hlx3 hpl C hC
        change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD C.output false = true at hev
        rw [hPref C.gates _ C.output (by rw [hInpLen]; exact hlt)] at hev
        change ((List.ofFn (fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) ++ List.ofFn (fun m : Fin 13 => decide (m ∈ ({l} : Finset (Fin 13))))).getD C.output false) = true at hev
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at hev
        simp only [List.length_ofFn] at hev
        rw [List.getElem?_ofFn] at hev
        have hsub : C.output - 13 < 13 := by omega
        simp only [hsub, ↓reduceDIte, Option.getD_some, decide_eq_true_eq, Finset.mem_singleton] at hev
        exact hll0 hev.symm
    · by_contra hge
      have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
      obtain ⟨l, hlx3, _⟩ := hPickLine x3 x3
      obtain ⟨p, hpl, hpx2, _⟩ := hPickPt l x2 x2
      have hev := hInc p l hpx2 hlx3 hpl C hC
      change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD C.output false = true at hev
      have hl : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).length = 26 + C.size := by
        rw [hLen, hInpLen]
        rfl
      have hdf : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD C.output false = false :=
        List.getD_eq_default _ _ (by omega)
      rw [hdf] at hev
      exact Bool.noConfusion hev
  have hB4 : 26 ≤ x4.output ∧ x4.output < 26 + x4.size := hBounds x4 (by simp)
  have hSzEq : x5.size = x4.size := by
    change x5.gates.length = x4.gates.length
    rw [hEqG]
  have hB5 : 26 ≤ x5.output ∧ x5.output < 26 + x4.size := by
    have h := hBounds x5 (by simp)
    rw [hSzEq] at h
    exact h
  have hOutNe : x4.output ≠ x5.output := by
    intro heq
    have hCEq : x4 = x5 := by
      cases x4
      cases x5
      simp only [PEqualNP.CircuitLowerBounds.Circuit.mk.injEq] at *
      exact ⟨hEqG, heq⟩
    obtain ⟨Q, hQ⟩ := hNE4
    have hQ5 : Q ∈ x10 x5 := by rw [← hCEq]; exact hQ
    exact Finset.disjoint_left.mp hDisj hQ hQ5
  have hOp : ∀ j, j < x4.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro j hj
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt x4 j = x4.gates[j] :=
      List.getD_eq_getElem _ _ hj
    rw [hge]
    have hmem : x4.gates[j] ∈ x4.gates := List.getElem_mem hj
    have hm := (hMono x4.gates[j] hmem).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  have hIncSwap : ∀ (x9 x10_1 : Fin (13 : ℕ)), x9 ≠ x2 → x10_1 ≠ x3 → x9 ∈ x1 x10_1 →
      ∀ x14 ∈ [x5, x4], x14.eval (PEqualNP.GenericRejection.incidenceInput {x9} {x10_1}) = Bool.true := by
    intro p l hp hl hpl C hC
    apply hInc p l hp hl hpl C
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC ⊢
    exact hC.symm
  have hMono5 : PEqualNP.MetaComplexity.Monotone2 x5 := by
    intro g hg
    rw [← hEqG] at hg
    exact hMono g hg
  rcases hOp (x4.output - 26) (by omega) with h4And | h4Or
  · exact hHasAndOut x2 x3 x4 x5 hIn hEqG hMono hB4 hB5 hOutNe h4And hInc hDisj hNE4 hNE5
  · rcases hOp (x5.output - 26) (by omega) with h5And | h5Or
    · have h5And' : (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
        change (x5.gates.getD (x5.output - 26) _).op = _
        rw [← hEqG]
        exact h5And
      rw [← hSzEq]
      exact hHasAndOut x2 x3 x5 x4 hIn hEqG.symm hMono5 (by rw [hSzEq]; exact hB5) (by rw [hSzEq]; exact hB4) hOutNe.symm h5And' hIncSwap hDisj.symm hNE5 hNE4
    · rcases Nat.lt_or_gt_of_ne hOutNe with hlt | hgt
      · exact hBothOrOut x2 x3 x4 x5 hIn hEqG hMono ⟨hB4.1, hlt, hB5.2⟩ h4Or h5Or hInc hDisj hNE4 hNE5
      · have h5Or' : (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
          change (x5.gates.getD (x5.output - 26) _).op = _
          rw [← hEqG]
          exact h5Or
        have h4Or' : (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x4.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
          change (x5.gates.getD (x4.output - 26) _).op = _
          rw [← hEqG]
          exact h4Or
        rw [← hSzEq]
        exact hBothOrOut x2 x3 x5 x4 hIn hEqG.symm hMono5 ⟨hB5.1, hgt, by rw [hSzEq]; exact hB4.2⟩ h5Or' h4Or' hIncSwap hDisj.symm hNE5 hNE4
