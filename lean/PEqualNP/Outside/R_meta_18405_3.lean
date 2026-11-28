import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18405_3
    (hOutAnd :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C →
        (26 : ℕ) ≤ C.output →
        C.output < (26 : ℕ) + C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 C →
        (∀ (Q : Finset (Fin (13 : ℕ))),
          PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
          C.eval (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) = Bool.false) →
        (64 : ℕ) ≤ C.size)
    (hOutOr :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        (∃ (x3 : Fin C.gates.length), (C.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C →
        (26 : ℕ) ≤ C.output →
        C.output < (26 : ℕ) + C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 C →
        (∀ (Q : Finset (Fin (13 : ℕ))),
          PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
          C.eval (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) = Bool.false) →
        (64 : ℕ) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → (∀ (x5 x6 : Fin (13 : ℕ)), x5 - x6 = (0 : Fin (13 : ℕ)) ∨ x5 - x6 = (1 : Fin (13 : ℕ)) ∨ x5 - x6 = (3 : Fin (13 : ℕ)) ∨ x5 - x6 = (9 : Fin (13 : ℕ)) → x1.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) → (∀ (x6 : Finset (Fin (13 : ℕ))), x6.card = (4 : ℕ) → (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x9 - x8 = (0 : Fin (13 : ℕ)) ∨ x9 - x8 = (1 : Fin (13 : ℕ)) ∨ x9 - x8 = (3 : Fin (13 : ℕ)) ∨ x9 - x8 = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) → x1.eval ((List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x6, ¬(x10 - x9 = (0 : Fin (13 : ℕ)) ∨ x10 - x9 = (1 : Fin (13 : ℕ)) ∨ x10 - x9 = (3 : Fin (13 : ℕ)) ∨ x10 - x9 = (9 : Fin (13 : ℕ))))) = Bool.false) → (64 : ℕ) ≤ x1.size := by
  intro C hMono hHasAnd hRB hTrue hFalse
  have hSingerMem : ∀ (p l : Fin (13 : ℕ)),
      (p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨ p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ))) ↔
      p ∈ PEqualNP.HeptadCover.singerLines3 l := by
    decide
  have hRight : PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 C := by
    intro l p hp
    have hIn : PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) =
        (List.ofFn fun (x8 : Fin 13) => Decidable.decide (x8 = p)) ++
        List.ofFn fun (x8 : Fin 13) => Decidable.decide (x8 = l) := by
      change (List.ofFn fun k : Fin 13 => decide (k ∈ ({p} : Finset (Fin 13)))) ++
        List.ofFn (fun k : Fin 13 => decide (k ∈ ({l} : Finset (Fin 13)))) = _
      exact congrArg₂ (· ++ ·)
        (congrArg List.ofFn (funext fun k => decide_eq_decide.mpr Finset.mem_singleton))
        (congrArg List.ofFn (funext fun k => decide_eq_decide.mpr Finset.mem_singleton))
    rw [hIn]
    exact hTrue p l ((hSingerMem p l).mpr hp)
  have hQuad : ∀ (Q : Finset (Fin 13)),
      PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
      C.eval (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) = Bool.false := by
    intro Q hQ
    obtain ⟨hcard, hsec⟩ := hQ
    have hsec' : ∀ (l : Fin 13),
        {p ∈ Q | p - l = (0 : Fin 13) ∨ p - l = (1 : Fin 13) ∨ p - l = (3 : Fin 13) ∨ p - l = (9 : Fin 13)}.card ≤ 2 := by
      intro l
      have hEq : {p ∈ Q | p - l = (0 : Fin 13) ∨ p - l = (1 : Fin 13) ∨ p - l = (3 : Fin 13) ∨ p - l = (9 : Fin 13)} =
          Q ∩ PEqualNP.HeptadCover.singerLines3 l := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_inter, hSingerMem p l]
      rw [hEq]
      exact hsec l
    have hIn : PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) =
        (List.ofFn fun (x9 : Fin 13) => Decidable.decide (x9 ∈ Q)) ++
        List.ofFn fun (x9 : Fin 13) => Decidable.decide (∀ x10 ∈ Q, ¬(x10 - x9 = (0 : Fin 13) ∨ x10 - x9 = (1 : Fin 13) ∨ x10 - x9 = (3 : Fin 13) ∨ x10 - x9 = (9 : Fin 13))) := by
      change (List.ofFn fun (x9 : Fin 13) => Decidable.decide (x9 ∈ Q)) ++
        List.ofFn (fun (x9 : Fin 13) => Decidable.decide (x9 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) = _
      refine congrArg ((List.ofFn fun (x9 : Fin 13) => Decidable.decide (x9 ∈ Q)) ++ ·) ?_
      refine congrArg List.ofFn (funext fun l => decide_eq_decide.mpr ?_)
      change l ∈ Finset.univ.filter (fun l' => Disjoint (PEqualNP.HeptadCover.singerLines3 l') Q) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right, hSingerMem]
    rw [hIn]
    exact hFalse Q hcard hsec'
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
  have hInpLen : ∀ (X Y : Finset (Fin 13)), (PEqualNP.GenericRejection.incidenceInput X Y).length = 26 := by
    intro X Y
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y))).length = 26
    simp only [List.length_append, List.length_ofFn]
  have houtGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    by_cases h13 : C.output < 13
    · let p0 : Fin 13 := ⟨C.output, h13⟩
      let p1 : Fin 13 := if p0 = 0 then 1 else 0
      have hp1ne : p1 ≠ p0 := by
        by_cases h0 : p0 = 0
        · simp only [p1, h0, ↓reduceIte]; decide
        · simp only [p1, h0, ↓reduceIte]; exact Ne.symm h0
      have hp1mem : p1 ∈ PEqualNP.HeptadCover.singerLines3 p1 :=
        (hSingerMem p1 p1).mp (Or.inl (sub_self p1))
      have hev := hRight p1 p1 hp1mem
      change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {p1} {p1})).getD C.output false = true at hev
      rw [hPref C.gates _ C.output (by rw [hInpLen]; exact hlt)] at hev
      change ((List.ofFn (fun q : Fin 13 => decide (q ∈ ({p1} : Finset (Fin 13)))) ++ List.ofFn (fun m : Fin 13 => decide (m ∈ ({p1} : Finset (Fin 13))))).getD C.output false) = true at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp only [List.length_ofFn]; exact h13)] at hev
      rw [List.getElem?_ofFn] at hev
      simp only [h13, ↓reduceDIte, Option.getD_some, decide_eq_true_eq, Finset.mem_singleton] at hev
      exact hp1ne hev.symm
    · let l0 : Fin 13 := ⟨C.output - 13, by omega⟩
      let l1 : Fin 13 := if l0 = 0 then 1 else 0
      have hl1ne : l1 ≠ l0 := by
        by_cases h0 : l0 = 0
        · simp only [l1, h0, ↓reduceIte]; decide
        · simp only [l1, h0, ↓reduceIte]; exact Ne.symm h0
      have hl1mem : l1 ∈ PEqualNP.HeptadCover.singerLines3 l1 :=
        (hSingerMem l1 l1).mp (Or.inl (sub_self l1))
      have hev := hRight l1 l1 hl1mem
      change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput {l1} {l1})).getD C.output false = true at hev
      rw [hPref C.gates _ C.output (by rw [hInpLen]; exact hlt)] at hev
      change ((List.ofFn (fun q : Fin 13 => decide (q ∈ ({l1} : Finset (Fin 13)))) ++ List.ofFn (fun m : Fin 13 => decide (m ∈ ({l1} : Finset (Fin 13))))).getD C.output false) = true at hev
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at hev
      simp only [List.length_ofFn] at hev
      rw [List.getElem?_ofFn] at hev
      have hsub : C.output - 13 < 13 := by omega
      simp only [hsub, ↓reduceDIte, Option.getD_some, decide_eq_true_eq, Finset.mem_singleton] at hev
      exact hl1ne hev.symm
  have houtLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have h0mem : (0 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 :=
      (hSingerMem 0 0).mp (Or.inl (sub_self 0))
    have hev := hRight 0 0 h0mem
    change (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) ({(0 : Fin 13)} : Finset (Fin 13)))).getD C.output false = true at hev
    have hl : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) ({(0 : Fin 13)} : Finset (Fin 13)))).length = 26 + C.size := by
      rw [hLen, hInpLen]
      rfl
    have hdf : (C.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) ({(0 : Fin 13)} : Finset (Fin 13)))).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hk_lt : C.output - 26 < C.gates.length := by
    change C.output - 26 < C.size
    omega
  have hOp : (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26) = C.gates[C.output - 26] :=
      List.getD_eq_getElem _ _ hk_lt
    rw [hge]
    have hm := (hMono C.gates[C.output - 26] (List.getElem_mem hk_lt)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  rcases hOp with hAnd | hOr
  · exact hOutAnd C hMono hRB houtGe houtLt hAnd hRight hQuad
  · exact hOutOr C hMono hHasAnd hRB houtGe houtLt hOr hRight hQuad
