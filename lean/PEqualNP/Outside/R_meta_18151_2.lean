import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18151_2
    (hFirstAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (a0 b0 : ℕ),
        (1 : ℕ) ≤ x1.size →
        (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size →
        a0 < (26 : ℕ) ∧ b0 < (26 : ℕ) →
        x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a0, b0] : PEqualNP.CircuitLowerBounds.Gate } →
        (26 : ℕ) * Min.min a0 b0 + Max.max a0 b0 ∈ [(0 : ℕ), (1 : ℕ), (13 : ℕ), (14 : ℕ), (27 : ℕ), (28 : ℕ), (29 : ℕ), (39 : ℕ), (40 : ℕ), (41 : ℕ), (43 : ℕ), (351 : ℕ), (352 : ℕ), (355 : ℕ), (378 : ℕ), (379 : ℕ)] →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) →
        (59 : ℕ) ≤ x1.size)
    (hFirstOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (a0 b0 : ℕ),
        (1 : ℕ) ≤ x1.size →
        (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size →
        a0 < (26 : ℕ) ∧ b0 < (26 : ℕ) →
        x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a0, b0] : PEqualNP.CircuitLowerBounds.Gate } →
        (26 : ℕ) * Min.min a0 b0 + Max.max a0 b0 ∈ [(0 : ℕ), (1 : ℕ), (13 : ℕ), (14 : ℕ), (27 : ℕ), (28 : ℕ), (29 : ℕ), (39 : ℕ), (40 : ℕ), (41 : ℕ), (43 : ℕ), (351 : ℕ), (352 : ℕ), (355 : ℕ), (378 : ℕ), (379 : ℕ)] →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
        (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) →
        (59 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : PEqualNP.CircuitLowerBounds.GateOp) (x3 x4 : ℕ), x1.gates[(0 : ℕ)]? = Option.some { op := x2, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } → (26 : ℕ) * Min.min x3 x4 + Max.max x3 x4 ∈ [(0 : ℕ), (1 : ℕ), (13 : ℕ), (14 : ℕ), (27 : ℕ), (28 : ℕ), (29 : ℕ), (39 : ℕ), (40 : ℕ), (41 : ℕ), (43 : ℕ), (351 : ℕ), (352 : ℕ), (355 : ℕ), (378 : ℕ), (379 : ℕ)]) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → (59 : ℕ) ≤ x1.size := by
  intro C hCanon hAO hSpec
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
  let f1 : Fin 26 → Bool := fun i => decide (i = 1 ∨ i = 14)
  have hCf1 : C.eval (List.ofFn f1) = true :=
    (hSpec f1).mpr ⟨1, 1, Or.inl rfl, by decide, by decide, by decide⟩
  have hOutLt : C.output < 26 + C.size := by
    by_contra hge
    have hge : 26 + C.size ≤ C.output := Nat.le_of_not_lt hge
    have hev : (C.gates.foldl step (List.ofFn f1)).getD C.output false = true := hCf1
    have hl : (C.gates.foldl step (List.ofFn f1)).length = 26 + C.size := by
      rw [hLen, List.length_ofFn]
      rfl
    have hdf : (C.gates.foldl step (List.ofFn f1)).getD C.output false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdf] at hev
    exact Bool.noConfusion hev
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hlt : C.output < 26 := Nat.lt_of_not_ge hlt
    let w0 : Fin 26 := ⟨C.output, hlt⟩
    let fS : Fin 26 → Bool := fun i => decide (i = w0)
    have hNotT : C.eval (List.ofFn fS) = false := by
      cases h : C.eval (List.ofFn fS)
      · rfl
      · obtain ⟨p, l, _, _, hp, hl⟩ := (hSpec fS).mp h
        have hp' : Fin.castAdd 13 p = w0 := of_decide_eq_true hp
        have hl' : Fin.natAdd 13 l = w0 := of_decide_eq_true hl
        have hval := congrArg Fin.val (hp'.trans hl'.symm)
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
    have hev : (C.gates.foldl step (List.ofFn fS)).getD C.output false = false := hNotT
    rw [hPref C.gates (List.ofFn fS) C.output (by rw [List.length_ofFn]; exact hlt)] at hev
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hev
    simp only [hlt, ↓reduceDIte, Option.getD_some] at hev
    change decide (w0 = w0) = false at hev
    rw [decide_eq_true rfl] at hev
    exact Bool.noConfusion hev
  have hSzPos : 1 ≤ C.size := by omega
  have h0lt : 0 < C.gates.length := hSzPos
  let g0 : PEqualNP.CircuitLowerBounds.Gate := C.gates[0]'h0lt
  have hg0Mem : g0 ∈ C.gates := List.getElem_mem h0lt
  have hg0Len : g0.inputs.length = 2 := hAO.2.2 g0 hg0Mem
  obtain ⟨a0, b0, hab0⟩ : ∃ a0 b0 : ℕ, g0.inputs = [a0, b0] := by
    rcases hin : g0.inputs with _ | ⟨a0, t1⟩
    · rw [hin] at hg0Len; cases hg0Len
    · rcases t1 with _ | ⟨b0, t2⟩
      · rw [hin] at hg0Len; cases hg0Len
      · rcases t2 with _ | ⟨c0, t3⟩
        · exact ⟨a0, b0, rfl⟩
        · rw [hin] at hg0Len; cases hg0Len
  have hga0 : PEqualNP.MetaComplexity.NestedCover.gateAt C 0 = g0 := by
    change C.gates.getD 0 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = _
    exact List.getD_eq_getElem _ _ h0lt
  have ha0Lt : a0 < 26 := by
    have h1 := hAO.2.1 0 h0lt a0 (by rw [hga0, hab0]; exact List.mem_cons_self)
    omega
  have hb0Lt : b0 < 26 := by
    have h1 := hAO.2.1 0 h0lt b0 (by rw [hga0, hab0]; exact List.mem_cons_of_mem a0 List.mem_cons_self)
    omega
  have hg0Eq : C.gates[0]? = Option.some { op := g0.op, inputs := [a0, b0] : PEqualNP.CircuitLowerBounds.Gate } := by
    rw [List.getElem?_eq_getElem h0lt]
    congr 1
    rw [← hab0]
  have hCode := hCanon g0.op a0 b0 hg0Eq
  rcases hAO.1 g0 hg0Mem with hAnd | hOr
  · rw [hAnd] at hg0Eq
    exact hFirstAnd C a0 b0 hSzPos ⟨hOutGe, hOutLt⟩ ⟨ha0Lt, hb0Lt⟩ hg0Eq hCode hAO hSpec
  · rw [hOr] at hg0Eq
    exact hFirstOr C a0 b0 hSzPos ⟨hOutGe, hOutLt⟩ ⟨ha0Lt, hb0Lt⟩ hg0Eq hCode hAO hSpec
