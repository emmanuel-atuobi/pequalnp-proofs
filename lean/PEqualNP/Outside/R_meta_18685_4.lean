import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18685_4
    (hLastOr :
      ∀ (x1 : ℕ → ℕ) (x2 x3 : Fin (21 : ℕ)),
        x2 ≤ x3 →
        (∀ (x4 : Fin (11 : ℕ)), x1 ↑x4 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x4 (0 : ℕ)) →
        (∀ (x5 : Fin (21 : ℕ)), ∃ (x6 : Fin ((11 : ℕ) + ↑x5)) (x7 : Fin ((11 : ℕ) + ↑x5)),
          x1 ((11 : ℕ) + ↑x5) = x1 ↑x6 ||| x1 ↑x7 ∨
          x1 ((11 : ℕ) + ↑x5) = x1 ↑x6 &&& x1 ↑x7 ∧
            (x5 = x2 ∨ x5 = x3 ∨ ∀ (x8 : Fin (24 : ℕ)), (x1 ((11 : ℕ) + ↑x5)).testBit ((16 : ℕ) + ↑x8) = Bool.false)) →
        (∃ (u v : Fin (31 : ℕ)), x1 ↑u ||| x1 ↑v = (65535 : ℕ) ∧
          (∀ (k : Fin (24 : ℕ)), (x1 ↑u).testBit ((16 : ℕ) + ↑k) = Bool.false ∧ (x1 ↑v).testBit ((16 : ℕ) + ↑k) = Bool.false)) →
        x1 (31 : ℕ) ≠ (65535 : ℕ))
    (hLastAnd :
      ∀ (x1 : ℕ → ℕ) (x2 x3 : Fin (21 : ℕ)),
        x2 ≤ x3 →
        (∀ (x4 : Fin (11 : ℕ)), x1 ↑x4 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x4 (0 : ℕ)) →
        (∀ (x5 : Fin (21 : ℕ)), ∃ (x6 : Fin ((11 : ℕ) + ↑x5)) (x7 : Fin ((11 : ℕ) + ↑x5)),
          x1 ((11 : ℕ) + ↑x5) = x1 ↑x6 ||| x1 ↑x7 ∨
          x1 ((11 : ℕ) + ↑x5) = x1 ↑x6 &&& x1 ↑x7 ∧
            (x5 = x2 ∨ x5 = x3 ∨ ∀ (x8 : Fin (24 : ℕ)), (x1 ((11 : ℕ) + ↑x5)).testBit ((16 : ℕ) + ↑x8) = Bool.false)) →
        (∃ (u v : Fin (31 : ℕ)), x1 ↑u &&& x1 ↑v = (65535 : ℕ) ∧
          (∀ (k : Fin (16 : ℕ)), (x1 ↑u).testBit ↑k = Bool.true ∧ (x1 ↑v).testBit ↑k = Bool.true)) →
        x1 (31 : ℕ) ≠ (65535 : ℕ)) :
    ∀ (x1 : ℕ → ℕ) (x2 x3 : Fin (21 : ℕ)), (∀ (x4 : Fin (11 : ℕ)), x1 ↑x4 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x4 (0 : ℕ)) → (∀ (x5 : Fin (21 : ℕ)), ∃ (x6 : Fin ((11 : ℕ) + ↑x5)) (x7 : Fin ((11 : ℕ) + ↑x5)), x1 ((11 : ℕ) + ↑x5) = x1 ↑x6 ||| x1 ↑x7 ∨ x1 ((11 : ℕ) + ↑x5) = x1 ↑x6 &&& x1 ↑x7 ∧ (x5 = x2 ∨ x5 = x3 ∨ ∀ (x8 : Fin (24 : ℕ)), (x1 ((11 : ℕ) + ↑x5)).testBit ((16 : ℕ) + ↑x8) = Bool.false)) → ∀ (x6 : Fin (32 : ℕ)), x1 ↑x6 ≠ (65535 : ℕ) := by
  intro x1 x2 x3 hInit hStep x6 hEq
  by_cases hlt11 : x6.val < 11
  · have hi := hInit ⟨x6.val, hlt11⟩
    change x1 x6.val = _ at hi
    rw [hEq] at hi
    have h11 : ∀ i : Fin 11, (65535 : ℕ) ≠ [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑i (0 : ℕ) := by decide
    exact h11 ⟨x6.val, hlt11⟩ hi
  · let x1' : ℕ → ℕ := fun k => if k ≤ x6.val then x1 k else (65535 : ℕ)
    have hInit' : ∀ (x4 : Fin (11 : ℕ)), x1' ↑x4 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x4 (0 : ℕ) := by
      intro x4
      have hle : (x4 : ℕ) ≤ x6.val := by omega
      simp only [x1', hle, ↓reduceIte]
      exact hInit x4
    have h31 : x1' (31 : ℕ) = (65535 : ℕ) := by
      by_cases h31le : 31 ≤ x6.val
      · have heq31 : x6.val = 31 := by omega
        simp only [x1', ← heq31, le_refl, ↓reduceIte, hEq]
      · simp only [x1', h31le, ↓reduceIte]
    let y2 : Fin 21 := if x2.val ≤ x3.val then x2 else x3
    let y3 : Fin 21 := if x2.val ≤ x3.val then x3 else x2
    have hy23 : y2 ≤ y3 := by
      dsimp only [y2, y3]
      split_ifs <;> exact Fin.le_def.mpr (by omega)
    have hStep' : ∀ (x5 : Fin (21 : ℕ)), ∃ (u : Fin ((11 : ℕ) + ↑x5)) (v : Fin ((11 : ℕ) + ↑x5)),
        x1' ((11 : ℕ) + ↑x5) = x1' ↑u ||| x1' ↑v ∨
        x1' ((11 : ℕ) + ↑x5) = x1' ↑u &&& x1' ↑v ∧
          (x5 = y2 ∨ x5 = y3 ∨ ∀ (x8 : Fin (24 : ℕ)), (x1' ((11 : ℕ) + ↑x5)).testBit ((16 : ℕ) + ↑x8) = Bool.false) := by
      intro x5
      by_cases hle : 11 + x5.val ≤ x6.val
      · obtain ⟨u, v, huv⟩ := hStep x5
        have hu : (u : ℕ) ≤ x6.val := by omega
        have hv : (v : ℕ) ≤ x6.val := by omega
        refine ⟨u, v, ?_⟩
        simp only [x1', if_pos hle, if_pos hu, if_pos hv]
        rcases huv with hor | ⟨hand, hclean⟩
        · exact Or.inl hor
        · refine Or.inr ⟨hand, ?_⟩
          dsimp only [y2, y3]
          split_ifs
          · exact hclean
          · rcases hclean with h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
      · let w : Fin (11 + x5.val) := ⟨x6.val, by omega⟩
        refine ⟨w, w, Or.inl ?_⟩
        have hwle : (w : ℕ) ≤ x6.val := le_refl _
        simp only [x1', if_neg hle, if_pos hwle, w, hEq, Nat.or_self]
    obtain ⟨u, v, huv⟩ := hStep' ⟨20, by omega⟩
    rcases huv with hor | ⟨hand, _⟩
    · have hor65 : x1' ↑u ||| x1' ↑v = (65535 : ℕ) := by
        have h1 : x1' 31 = x1' ↑u ||| x1' ↑v := hor
        exact h1.symm.trans h31
      apply hLastOr x1' y2 y3 hy23 hInit' hStep' _ h31
      refine ⟨u, v, hor65, ?_⟩
      intro k
      have hbit : (x1' ↑u ||| x1' ↑v).testBit (16 + k.val) = (65535 : ℕ).testBit (16 + k.val) :=
        congrArg (fun n => n.testBit (16 + k.val)) hor65
      have hzero : (65535 : ℕ).testBit (16 + k.val) = false := by
        apply Nat.testBit_lt_two_pow
        have hpow : (2 : ℕ) ^ 16 ≤ 2 ^ (16 + k.val) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      rw [Nat.testBit_or, hzero, Bool.or_eq_false_iff] at hbit
      exact hbit
    · have hand65 : x1' ↑u &&& x1' ↑v = (65535 : ℕ) := by
        have h1 : x1' 31 = x1' ↑u &&& x1' ↑v := hand
        exact h1.symm.trans h31
      apply hLastAnd x1' y2 y3 hy23 hInit' hStep' _ h31
      refine ⟨u, v, hand65, ?_⟩
      intro k
      have hbit : (x1' ↑u &&& x1' ↑v).testBit k.val = (65535 : ℕ).testBit k.val :=
        congrArg (fun n => n.testBit k.val) hand65
      have hone : (65535 : ℕ).testBit k.val = true := by
        fin_cases k <;> decide
      rw [Nat.testBit_and, hone, Bool.and_eq_true] at hbit
      exact hbit
