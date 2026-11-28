import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7909_3
    (hOrSub :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
        (400 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
        PEqualNP.MetaComplexity.Monotone2 x5 →
        x2 + x2 ≤ w →
        w < x2 + x2 + x5.size →
        (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x5.gates[w - (x2 + x2)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) →
        (∀ (x15 x16 : Fin x2), x3 x15 x16 → (x5.wires (List.ofFn fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16))).getD w Bool.false = Bool.true) →
        (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → (x5.wires (List.ofFn x16)).getD w Bool.false = Bool.false) →
        x2 * x1 ≤ (100 : ℕ) * x5.size)
    (hIrredAnd :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        let FalseIn : (Fin (x2 + x2) → Bool) → Prop := fun x16 =>
          Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 ∧
          ¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true;
        (400 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
        PEqualNP.MetaComplexity.Monotone2 x5 →
        x2 + x2 ≤ a →
        a < b →
        b < x2 + x2 + x5.size →
        (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) →
        (∀ (x15 x16 : Fin x2), x3 x15 x16 →
          (x5.wires (List.ofFn fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16))).getD a Bool.false = Bool.true ∧
          (x5.wires (List.ofFn fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16))).getD b Bool.false = Bool.true) →
        (∀ (x16 : Fin (x2 + x2) → Bool), FalseIn x16 →
          (x5.wires (List.ofFn x16)).getD a Bool.false = Bool.false ∨ (x5.wires (List.ofFn x16)).getD b Bool.false = Bool.false) →
        (∃ (x16 : Fin (x2 + x2) → Bool), FalseIn x16 ∧ (x5.wires (List.ofFn x16)).getD a Bool.false = Bool.true) →
        (∃ (x16 : Fin (x2 + x2) → Bool), FalseIn x16 ∧ (x5.wires (List.ofFn x16)).getD b Bool.false = Bool.true) →
        x2 * x1 ≤ (100 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (400 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N inc _ C hq hN hLine hUniq hMono houtLo houtHi hOutAnd hStrict hPos hNeg
  have hN2 : 2 ≤ N := by
    have hq2 : 1 ≤ q ^ 2 := by
      have : 1 * 1 ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
      simpa only [sq] using this
    rw [hN]
    omega
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have run_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (gs ++ [g]).foldl step x = gs.foldl step x ++ [g.op.eval (g.inputs.map fun i => (gs.foldl step x).getD i false)] := by
    intro gs g x
    simp only [step, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (gs.foldl step x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [run_snoc]
      simp only [List.length_append, List.length_singleton, ih]
      omega
  have run_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length →
      ((gs ++ hs).foldl step x).getD i false = (gs.foldl step x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => simp
    | append_singleton hs g ih =>
      rw [← List.append_assoc, run_snoc]
      have hlen : ((gs ++ hs).foldl step x).length = x.length + (gs ++ hs).length := run_length (gs ++ hs) x
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen, List.length_append]; omega), ← List.getD_eq_getElem?_getD]
      exact ih
  have run_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (gs.foldl step x).getD i false = x.getD i false := by
    intro gs x i hi
    have h := run_prefix [] gs x i (by simpa only [List.length_nil, Nat.add_zero] using hi)
    simpa only [List.nil_append, List.foldl_nil] using h
  have run_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl step x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (gs.foldl step x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; simp at hj
    | append_singleton gs g ih =>
      intro j hj
      have hlen : (gs.foldl step x).length = x.length + gs.length := run_length gs x
      have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
          (l.map fun i => if i < x.length + k then ((gs ++ [g]).foldl step x).getD i false else false) =
          l.map fun i => if i < x.length + k then (gs.foldl step x).getD i false else false := by
        intro k hk l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · exact run_prefix gs [g] x i (by omega)
        · rfl
      rcases Nat.lt_or_ge j gs.length with h | h
      · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
        exact ih j h
      · have hjj : j = gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
        subst hjj
        have hg : (gs ++ [g])[gs.length] = g := by simp
        rw [hg, same _ le_rfl, run_snoc, ← hlen]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hAndEval : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [u, v] = (u && v) := by
    intro u v
    cases u <;> cases v <;> rfl
  have hNotRaw : ∀ w : ℕ,
      (∀ (p l : Fin N), inc p l →
        (C.wires (List.ofFn fun u : Fin (N + N) => Decidable.decide (u = Fin.castAdd N p ∨ u = Fin.natAdd N l))).getD w Bool.false = Bool.true) →
      N + N ≤ w := by
    intro w hpw
    by_contra hlt
    have hlt : w < N + N := Nat.lt_of_not_ge hlt
    by_cases h1 : w < N
    · let p0 : Fin N := ⟨w, h1⟩
      let l0 : Fin N := ⟨0, by omega⟩
      have hsub : (Finset.univ.filter fun p : Fin N => inc p l0) ⊆ {p0} := by
        intro p hp
        have hmem := hpw p l0 (Finset.mem_filter.mp hp).2
        change (C.gates.foldl step (List.ofFn _)).getD w false = true at hmem
        rw [run_input C.gates _ w (by rw [List.length_ofFn]; exact hlt)] at hmem
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hmem
        simp only [hlt, ↓reduceDIte, Option.getD_some, decide_eq_true_eq] at hmem
        rcases hmem with heq | heq
        · have hv := congrArg Fin.val heq
          simp only [Fin.val_castAdd] at hv
          exact Finset.mem_singleton.mpr (Fin.ext hv.symm)
        · have hv := congrArg Fin.val heq
          simp only [Fin.val_natAdd] at hv
          omega
      have hc1 : (Finset.univ.filter fun p : Fin N => inc p l0).card ≤ 1 :=
        le_trans (Finset.card_le_card hsub) (by simp only [Finset.card_singleton]; rfl)
      have hc2 : (Finset.univ.filter fun p : Fin N => inc p l0).card = Fintype.card { p : Fin N // inc p l0 } := by
        rw [Fintype.card_subtype]
      have hc3 := hLine l0
      omega
    · let l0 : Fin N := ⟨w - N, by omega⟩
      let l1 : Fin N := if l0.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hne : l1 ≠ l0 := by
        intro heq
        have hv := congrArg Fin.val heq
        by_cases h0 : l0.val = 0
        · simp only [l1, h0, ↓reduceIte] at hv
          omega
        · simp only [l1, h0, ↓reduceIte] at hv
          exact h0 hv.symm
      have hpos1 : 0 < Fintype.card { p : Fin N // inc p l1 } := by
        rw [hLine l1]
        omega
      obtain ⟨⟨p1, hp1⟩⟩ := Fintype.card_pos_iff.mp hpos1
      have hmem := hpw p1 l1 hp1
      change (C.gates.foldl step (List.ofFn _)).getD w false = true at hmem
      rw [run_input C.gates _ w (by rw [List.length_ofFn]; exact hlt)] at hmem
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hmem
      simp only [hlt, ↓reduceDIte, Option.getD_some, decide_eq_true_eq] at hmem
      rcases hmem with heq | heq
      · have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd] at hv
        omega
      · have hv := congrArg Fin.val heq
        simp only [Fin.val_natAdd] at hv
        apply hne
        ext
        change l1.val = w - N
        omega
  let Pos : ℕ → Prop := fun w =>
    ∀ (p l : Fin N), inc p l →
      (C.wires (List.ofFn fun u : Fin (N + N) => Decidable.decide (u = Fin.castAdd N p ∨ u = Fin.natAdd N l))).getD w Bool.false = Bool.true
  let Neg : ℕ → Prop := fun w =>
    ∀ (f : Fin (N + N) → Bool),
      Fintype.card { l : Fin N // f (Fin.natAdd N l) = Bool.true } ≤ q →
      (¬∃ (p l : Fin N), inc p l ∧ f (Fin.castAdd N p) = Bool.true ∧ f (Fin.natAdd N l) = Bool.true) →
      (C.wires (List.ofFn f)).getD w Bool.false = Bool.false
  have hMain : ∀ w : ℕ,
      N + N ≤ w → w < N + N + C.size → Pos w → Neg w → N * q ≤ 100 * C.size := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwLo hwHi hPw hNw
      let j : ℕ := w - (N + N)
      have hj : j < C.gates.length := by change w - (N + N) < C.size; omega
      have hwEq : N + N + j = w := by omega
      have hSome : C.gates[j]? = Option.some C.gates[j] := List.getElem?_eq_getElem hj
      have hOp := (hMono C.gates[j] (List.getElem_mem hj)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hOp
      rcases hOp with hAnd | hOr
      · obtain ⟨a, b, hab, hlt, hblt⟩ := hStrict j C.gates[j] hSome
        have haLt : a < w := by omega
        have hbLt : b < w := by omega
        have hEvalW : ∀ f : Fin (N + N) → Bool,
            (C.wires (List.ofFn f)).getD w Bool.false =
            ((C.wires (List.ofFn f)).getD a Bool.false && (C.wires (List.ofFn f)).getD b Bool.false) := by
          intro f
          change (C.gates.foldl step (List.ofFn f)).getD w false = _
          have hlen : (List.ofFn f).length = N + N := List.length_ofFn
          have hg := run_gate C.gates (List.ofFn f) j hj
          rw [hlen] at hg
          rw [← hwEq, hg, hAnd, hab, List.map_cons, List.map_cons, List.map_nil, hAndEval]
          rw [if_pos (by omega), if_pos (by omega)]
          rfl
        have hPa : Pos a := fun p l hpl => by
          have h := hPw p l hpl
          rw [hEvalW] at h
          exact (Bool.and_eq_true _ _ |>.mp h).1
        have hPb : Pos b := fun p l hpl => by
          have h := hPw p l hpl
          rw [hEvalW] at h
          exact (Bool.and_eq_true _ _ |>.mp h).2
        have haLo : N + N ≤ a := hNotRaw a hPa
        have hbLo : N + N ≤ b := by omega
        by_cases hNa : Neg a
        · exact ih a haLt haLo (by omega) hPa hNa
        · by_cases hNb : Neg b
          · exact ih b hbLt hbLo (by omega) hPb hNb
          · have hDirtyA : ∃ (f : Fin (N + N) → Bool),
                (Fintype.card { l : Fin N // f (Fin.natAdd N l) = Bool.true } ≤ q ∧
                ¬∃ (p l : Fin N), inc p l ∧ f (Fin.castAdd N p) = Bool.true ∧ f (Fin.natAdd N l) = Bool.true) ∧
                (C.wires (List.ofFn f)).getD a Bool.false = Bool.true := by
              by_contra hno
              apply hNa
              intro f hcard hfalse
              by_cases ht : (C.wires (List.ofFn f)).getD a Bool.false = Bool.true
              · exact False.elim (hno ⟨f, ⟨hcard, hfalse⟩, ht⟩)
              · exact Bool.eq_false_iff.mpr ht
            have hDirtyB : ∃ (f : Fin (N + N) → Bool),
                (Fintype.card { l : Fin N // f (Fin.natAdd N l) = Bool.true } ≤ q ∧
                ¬∃ (p l : Fin N), inc p l ∧ f (Fin.castAdd N p) = Bool.true ∧ f (Fin.natAdd N l) = Bool.true) ∧
                (C.wires (List.ofFn f)).getD b Bool.false = Bool.true := by
              by_contra hno
              apply hNb
              intro f hcard hfalse
              by_cases ht : (C.wires (List.ofFn f)).getD b Bool.false = Bool.true
              · exact False.elim (hno ⟨f, ⟨hcard, hfalse⟩, ht⟩)
              · exact Bool.eq_false_iff.mpr ht
            refine @hIrredAnd q N inc _ C a b hq hN hLine hUniq hMono haLo hlt (by omega) hStrict
              (fun p l hpl => ⟨hPa p l hpl, hPb p l hpl⟩) ?_ hDirtyA hDirtyB
            intro f hF
            obtain ⟨hcard, hfalse⟩ := hF
            have hf := hNw f hcard hfalse
            rw [hEvalW] at hf
            exact Bool.and_eq_false_iff.mp hf
      · exact @hOrSub q N inc _ C w hq hN hLine hUniq hMono hwLo hwHi ⟨C.gates[j], hSome, hOr⟩ hStrict hPw hNw
  exact hMain C.output houtLo houtHi hPos hNeg
