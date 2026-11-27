import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8811_4
    (hTopUnion :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        let V : Type := Fin x2 → Bool;
        (199 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
        ∀ (x9 w a b : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set (V × V)),
          have x13 : ℕ := x2 + x2;
          have x14 : Fin x2 → V := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);
          have Pos : ℕ → Prop := fun u => ∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 u;
          have Neg : ℕ → Prop := fun u => ∀ (x19 : V), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 u;
          x13 ≤ w →
          w < x13 + x9 →
          a < w →
          b < w →
          (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : V × V | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : V × V | x17.2 x16 = Bool.true}) →
          (∀ x17 < x9, ∃ x19 < x13 + x17, ∃ x20 < x13 + x17, have x21 : Set (V × V) := x12 (x13 + x17); x21 = x12 x19 ∪ x12 x20 ∨ x21 = x12 x19 ∨ x21 = ∅ ∨ x21 = x12 x19 ∩ x12 x20 ∧ (x17 ∈ x11 ∨ ∃ (x22 : Set V) (x23 : Set V), x12 x19 = x22 ×ˢ Set.univ ∧ x12 x20 = Set.univ ×ˢ x23)) →
          x12 w = x12 a ∪ x12 b →
          Pos w →
          Neg a ∧ Neg b ∧ ¬Pos a ∧ ¬Pos b →
          (∀ u < w, ¬(Pos u ∧ Neg u)) →
          (100 : ℕ) * x11.card < x2 * x1 →
          x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9)
    (hTopInter :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        let V : Type := Fin x2 → Bool;
        (199 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
        ∀ (x9 w a b : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set (V × V)),
          have x13 : ℕ := x2 + x2;
          have x14 : Fin x2 → V := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);
          have Pos : ℕ → Prop := fun u => ∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 u;
          have Neg : ℕ → Prop := fun u => ∀ (x19 : V), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 u;
          x13 ≤ w →
          w < x13 + x9 →
          a < w →
          b < w →
          (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : V × V | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : V × V | x17.2 x16 = Bool.true}) →
          (∀ x17 < x9, ∃ x19 < x13 + x17, ∃ x20 < x13 + x17, have x21 : Set (V × V) := x12 (x13 + x17); x21 = x12 x19 ∪ x12 x20 ∨ x21 = x12 x19 ∨ x21 = ∅ ∨ x21 = x12 x19 ∩ x12 x20 ∧ (x17 ∈ x11 ∨ ∃ (x22 : Set V) (x23 : Set V), x12 x19 = x22 ×ˢ Set.univ ∧ x12 x20 = Set.univ ×ˢ x23)) →
          x12 w = x12 a ∩ x12 b →
          Neg w →
          Pos a ∧ Pos b ∧ ¬Neg a ∧ ¬Neg b →
          (∀ u < w, ¬(Pos u ∧ Neg u)) →
          (100 : ℕ) * x11.card < x2 * x1 →
          x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (199 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x13 : ℕ := x2 + x2;             have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);             x10 < x13 + x9 →               (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                 (∀ x17 < x9,                     ∃ x19 < x13 + x17,                       ∃ x20 < x13 + x17,                         have x21 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x13 + x17);                         x21 = x12 x19 ∪ x12 x20 ∨ x21 = x12 x19 ∨ x21 = ∅ ∨ x21 = x12 x19 ∩ x12 x20 ∧ (x17 ∈ x11 ∨ ∃ (x22 : Set (Fin x2 → Bool)) (x23 : Set (Fin x2 → Bool)), x12 x19 = x22 ×ˢ Set.univ ∧ x12 x20 = Set.univ ×ˢ x23)) →                   (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x10) → (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9 := by
  classical
  intro q N inc _ hq hN hCard hProj s out B W base ind houtLt hInit hSteps hPosOut hNegOut hBcard
  have hN2 : 2 ≤ N := by
    have hq2 : 1 ≤ q ^ 2 := by
      have : 1 * 1 ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
      simpa only [sq] using this
    rw [hN]
    omega
  let Pos : ℕ → Prop := fun u => ∀ (p l : Fin N), inc p l → (ind p, ind l) ∈ W u
  let Neg : ℕ → Prop := fun u => ∀ (Y : Fin N → Bool), Fintype.card { l : Fin N // Y l = Bool.true } ≤ q →
    (fun p : Fin N => Decidable.decide ¬∃ l : Fin N, inc p l ∧ Y l = Bool.true, Y) ∉ W u
  have hex : ∃ u, Pos u ∧ Neg u := ⟨out, hPosOut, hNegOut⟩
  let w : ℕ := Nat.find hex
  have hwPN : Pos w ∧ Neg w := Nat.find_spec hex
  have hwLe : w ≤ out := Nat.find_min' hex ⟨hPosOut, hNegOut⟩
  have hwMin : ∀ u < w, ¬(Pos u ∧ Neg u) := fun u hu => Nat.find_min hex hu
  have hwGe : base ≤ w := by
    by_contra hlt
    have hlt : w < N + N := Nat.lt_of_not_ge hlt
    by_cases h1 : w < N
    · let p0 : Fin N := ⟨w, h1⟩
      let Y : Fin N → Bool := fun _ => Bool.false
      have hYcard : Fintype.card { l : Fin N // Y l = Bool.true } ≤ q := by
        have hEmpty : IsEmpty { l : Fin N // Y l = Bool.true } := ⟨fun x => Bool.noConfusion x.2⟩
        rw [Fintype.card_eq_zero]
        omega
      have hnot := hwPN.2 Y hYcard
      have hW := (hInit p0).1
      change W w = {z : (Fin N → Bool) × (Fin N → Bool) | z.1 p0 = Bool.true} at hW
      rw [hW] at hnot
      apply hnot
      simp only [Set.mem_setOf_eq, Y, Bool.false_eq_true, and_false, exists_false, not_false_eq_true, decide_true]
    · let l0 : Fin N := ⟨w - N, by omega⟩
      let Y : Fin N → Bool := fun l => Decidable.decide (l = l0)
      have hYcard : Fintype.card { l : Fin N // Y l = Bool.true } ≤ q := by
        rw [Fintype.card_subtype]
        have hsub : (Finset.univ.filter fun l : Fin N => Y l = Bool.true) ⊆ {l0} := by
          intro l hl
          have hm := (Finset.mem_filter.mp hl).2
          simp only [Y, decide_eq_true_eq] at hm
          exact Finset.mem_singleton.mpr hm
        have hc := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at hc
        omega
      have hnot := hwPN.2 Y hYcard
      have hw_eq : N + l0.val = w := by change N + (w - N) = w; omega
      have hW := (hInit l0).2
      rw [hw_eq] at hW
      rw [hW] at hnot
      apply hnot
      simp only [Set.mem_setOf_eq, Y, decide_true]
  have hwLt : w < base + s := lt_of_le_of_lt hwLe houtLt
  have hgLt : w - base < s := by omega
  have hwEq : base + (w - base) = w := by omega
  obtain ⟨a, ha, b, hb, hSt⟩ := hSteps (w - base) hgLt
  rw [hwEq] at ha hb hSt
  rcases hSt with hU | hCopy | hEmpty | ⟨hI, _⟩
  · have hNegA : Neg a := fun Y hY hmem => hwPN.2 Y hY (by rw [hU]; exact Or.inl hmem)
    have hNegB : Neg b := fun Y hY hmem => hwPN.2 Y hY (by rw [hU]; exact Or.inr hmem)
    have hnPosA : ¬Pos a := fun hpa => hwMin a ha ⟨hpa, hNegA⟩
    have hnPosB : ¬Pos b := fun hpb => hwMin b hb ⟨hpb, hNegB⟩
    exact @hTopUnion q N inc _ hq hN hCard hProj s w a b B W hwGe hwLt ha hb hInit hSteps hU hwPN.1 ⟨hNegA, hNegB, hnPosA, hnPosB⟩ hwMin hBcard
  · exact False.elim (hwMin a ha ⟨fun p l hpl => by rw [← hCopy]; exact hwPN.1 p l hpl, fun Y hY hmem => hwPN.2 Y hY (by rw [hCopy]; exact hmem)⟩)
  · let l0 : Fin N := ⟨0, by omega⟩
    have hpos0 : 0 < Fintype.card { p : Fin N // inc p l0 } := by rw [hCard l0]; omega
    obtain ⟨⟨p0, hp0⟩⟩ := Fintype.card_pos_iff.mp hpos0
    have hmem := hwPN.1 p0 l0 hp0
    rw [hEmpty] at hmem
    exact False.elim hmem
  · have hPosA : Pos a := fun p l hpl => by have hm := hwPN.1 p l hpl; rw [hI] at hm; exact hm.1
    have hPosB : Pos b := fun p l hpl => by have hm := hwPN.1 p l hpl; rw [hI] at hm; exact hm.2
    have hnNegA : ¬Neg a := fun hna => hwMin a ha ⟨hPosA, hna⟩
    have hnNegB : ¬Neg b := fun hnb => hwMin b hb ⟨hPosB, hnb⟩
    exact @hTopInter q N inc _ hq hN hCard hProj s w a b B W hwGe hwLt ha hb hInit hSteps hI hwPN.2 ⟨hPosA, hPosB, hnNegA, hnNegB⟩ hwMin hBcard
