import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8063_3
    (hBothChildOr :
      ∀ (x1 : ℕ) (x2 : ℕ → Bool) (x3 x4 : ℕ → ℕ) (x5 : ℕ → BitVec (60 : ℕ)),
        x1 ≤ (27 : ℕ) →
        (∀ x7 < (14 : ℕ), x5 x7 = BitVec.ofNat (60 : ℕ) ([(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)].getD x7 (0 : ℕ))) →
        (∀ x8 < x1, x3 x8 ≠ x4 x8 ∧ x3 x8 < (14 : ℕ) + x8 ∧ x4 x8 < (14 : ℕ) + x8 ∧ (x2 x8 = Bool.false → (0 : ℕ) < x8) ∧ x5 ((14 : ℕ) + x8) = if x2 x8 = Bool.true then x5 (x3 x8) ||| x5 (x4 x8) else x5 (x3 x8) &&& x5 (x4 x8)) →
        ∀ x9 < x1,
          x5 ((14 : ℕ) + x9) = (2097151 : BitVec (60 : ℕ)) →
          (2 : ℕ) ≤ x9 ∧ (14 : ℕ) ≤ x3 x9 ∧ (14 : ℕ) ≤ x4 x9 →
          x2 (x3 x9 - (14 : ℕ)) = Bool.true ∧ x2 (x4 x9 - (14 : ℕ)) = Bool.true →
          ∃ (x12 : Bool),
            have x13 : ℕ := if x12 = Bool.true then (58 : ℕ) else (59 : ℕ);
            Relation.ReflTransGen (fun (x14 x15 : ℕ) => ∃ x16 < x1, x15 = (14 : ℕ) + x16 ∧ (x14 = x3 x16 ∧ (x2 x16 || (x5 (x4 x16)).getLsbD x13) = Bool.true ∨ x14 = x4 x16 ∧ (x2 x16 || (x5 (x3 x16)).getLsbD x13) = Bool.true)) (if x12 = Bool.true then (7 : ℕ) else (0 : ℕ)) ((14 : ℕ) + x9))
    (hHasChildAnd :
      ∀ (x1 : ℕ) (x2 : ℕ → Bool) (x3 x4 : ℕ → ℕ) (x5 : ℕ → BitVec (60 : ℕ)),
        x1 ≤ (27 : ℕ) →
        (∀ x7 < (14 : ℕ), x5 x7 = BitVec.ofNat (60 : ℕ) ([(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)].getD x7 (0 : ℕ))) →
        (∀ x8 < x1, x3 x8 ≠ x4 x8 ∧ x3 x8 < (14 : ℕ) + x8 ∧ x4 x8 < (14 : ℕ) + x8 ∧ (x2 x8 = Bool.false → (0 : ℕ) < x8) ∧ x5 ((14 : ℕ) + x8) = if x2 x8 = Bool.true then x5 (x3 x8) ||| x5 (x4 x8) else x5 (x3 x8) &&& x5 (x4 x8)) →
        ∀ x9 < x1,
          x5 ((14 : ℕ) + x9) = (2097151 : BitVec (60 : ℕ)) →
          (2 : ℕ) ≤ x9 ∧ (14 : ℕ) ≤ x3 x9 ∧ (14 : ℕ) ≤ x4 x9 →
          x2 (x3 x9 - (14 : ℕ)) = Bool.false ∨ x2 (x4 x9 - (14 : ℕ)) = Bool.false →
          ∃ (x12 : Bool),
            have x13 : ℕ := if x12 = Bool.true then (58 : ℕ) else (59 : ℕ);
            Relation.ReflTransGen (fun (x14 x15 : ℕ) => ∃ x16 < x1, x15 = (14 : ℕ) + x16 ∧ (x14 = x3 x16 ∧ (x2 x16 || (x5 (x4 x16)).getLsbD x13) = Bool.true ∨ x14 = x4 x16 ∧ (x2 x16 || (x5 (x3 x16)).getLsbD x13) = Bool.true)) (if x12 = Bool.true then (7 : ℕ) else (0 : ℕ)) ((14 : ℕ) + x9)) :
    ∀ (x1 : ℕ) (x2 : ℕ → Bool) (x3 x4 : ℕ → ℕ) (x5 : ℕ → BitVec (60 : ℕ)),   x1 ≤ (27 : ℕ) →     (∀ x7 < (14 : ℕ), x5 x7 = BitVec.ofNat (60 : ℕ) ([(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)].getD x7 (0 : ℕ))) →       (∀ x8 < x1, x3 x8 ≠ x4 x8 ∧ x3 x8 < (14 : ℕ) + x8 ∧ x4 x8 < (14 : ℕ) + x8 ∧ (x2 x8 = Bool.false → (0 : ℕ) < x8) ∧ x5 ((14 : ℕ) + x8) = if x2 x8 = Bool.true then x5 (x3 x8) ||| x5 (x4 x8) else x5 (x3 x8) &&& x5 (x4 x8)) →         ∀ x9 < x1,           x5 ((14 : ℕ) + x9) = (2097151 : BitVec (60 : ℕ)) →             ∃ (x12 : Bool),               have x13 : ℕ := if x12 = Bool.true then (58 : ℕ) else (59 : ℕ);               Relation.ReflTransGen (fun (x14 x15 : ℕ) => ∃ x16 < x1, x15 = (14 : ℕ) + x16 ∧ (x14 = x3 x16 ∧ (x2 x16 || (x5 (x4 x16)).getLsbD x13) = Bool.true ∨ x14 = x4 x16 ∧ (x2 x16 || (x5 (x3 x16)).getLsbD x13) = Bool.true)) (if x12 = Bool.true then (7 : ℕ) else (0 : ℕ)) ((14 : ℕ) + x9) := by
  intro s op l r val hs hInit hGates g hg hVal
  let L14 : List ℕ := [2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916]
  have hHiBit : ∀ i : Fin 14, ∃ j : Fin 60,
      (BitVec.ofNat 60 (L14.getD i.val 0)).getLsbD j.val = true ∧
      ((2097151 : BitVec 60)).getLsbD j.val = false := by
    decide
  have hLoZero : ∀ i : Fin 14, ∃ j : Fin 60,
      (BitVec.ofNat 60 (L14.getD i.val 0)).getLsbD j.val = false ∧
      ((2097151 : BitVec 60)).getLsbD j.val = true := by
    decide
  obtain ⟨hNe, hLtL, hLtR, _, hEq⟩ := hGates g hg
  rw [hVal] at hEq
  have hNotRaw : ∀ w1 w2 : ℕ,
      (2097151 : BitVec 60) = (if op g = true then val w1 ||| val w2 else val w1 &&& val w2) →
      14 ≤ w1 := by
    intro w1 w2 hcomb
    by_contra hlt
    have hlt : w1 < 14 := Nat.lt_of_not_ge hlt
    cases hop : op g
    · rw [hop] at hcomb
      simp only [Bool.false_eq_true, ↓reduceIte] at hcomb
      obtain ⟨j, hF, hT⟩ := hLoZero ⟨w1, hlt⟩
      have hb := congrArg (fun bv : BitVec 60 => bv.getLsbD j.val) hcomb
      rw [BitVec.getLsbD_and, hInit w1 hlt] at hb
      change ((2097151 : BitVec 60)).getLsbD j.val = ((BitVec.ofNat 60 (L14.getD w1 0)).getLsbD j.val && (val w2).getLsbD j.val) at hb
      rw [hT, hF, Bool.false_and] at hb
      exact Bool.noConfusion hb
    · rw [hop] at hcomb
      simp only [↓reduceIte] at hcomb
      obtain ⟨j, hT, hF⟩ := hHiBit ⟨w1, hlt⟩
      have hb := congrArg (fun bv : BitVec 60 => bv.getLsbD j.val) hcomb
      rw [BitVec.getLsbD_or, hInit w1 hlt] at hb
      change ((2097151 : BitVec 60)).getLsbD j.val = ((BitVec.ofNat 60 (L14.getD w1 0)).getLsbD j.val || (val w2).getLsbD j.val) at hb
      rw [hF, hT, Bool.true_or] at hb
      exact Bool.noConfusion hb
  have hlGe : 14 ≤ l g := hNotRaw (l g) (r g) hEq
  have hrGe : 14 ≤ r g := by
    apply hNotRaw (r g) (l g)
    cases hop : op g
    · rw [hop] at hEq
      simp only [Bool.false_eq_true, ↓reduceIte] at hEq ⊢
      rw [BitVec.and_comm]
      exact hEq
    · rw [hop] at hEq
      simp only [↓reduceIte] at hEq ⊢
      rw [BitVec.or_comm]
      exact hEq
  have hgGe2 : 2 ≤ g := by omega
  cases h1 : op (l g - 14)
  · exact hHasChildAnd s op l r val hs hInit hGates g hg hVal ⟨hgGe2, hlGe, hrGe⟩ (Or.inl h1)
  · cases h2 : op (r g - 14)
    · exact hHasChildAnd s op l r val hs hInit hGates g hg hVal ⟨hgGe2, hlGe, hrGe⟩ (Or.inr h2)
    · exact hBothChildOr s op l r val hs hInit hGates g hg hVal ⟨hgGe2, hlGe, hrGe⟩ ⟨h1, h2⟩
