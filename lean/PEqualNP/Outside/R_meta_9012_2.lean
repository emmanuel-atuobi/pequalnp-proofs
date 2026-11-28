import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_9012_2
    (hTopUnion :
      ∀ (x1 w a b : ℕ) (x3 : ℕ → Finset (Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)))),
        (26 : ℕ) ≤ a →
        a < b →
        b < w →
        w < (26 : ℕ) + x1 →
        (∀ x5 < (26 : ℕ), ∃ (x7 : Fin (13 : ℕ) ⊕ Fin (13 : ℕ)), x3 x5 = {Finset.univ.erase x7}) →
        (∀ x6 < x1, ∃ x8 < (26 : ℕ) + x6, ∃ x9 < (26 : ℕ) + x6, x3 ((26 : ℕ) + x6) = x3 x8 ∪ x3 x9 ∨ x3 ((26 : ℕ) + x6) = Finset.image₂ (fun (x10 x11 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x10 ∩ x11) (x3 x8) (x3 x9)) →
        x3 w = x3 a ∪ x3 b →
        (∀ x7 ∈ x3 w, PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) x7) →
        (∀ x8 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x8 ∈ x3 w) →
        (∃ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 Q ∉ x3 a) →
        (∃ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 Q ∉ x3 b) →
        (64 : ℕ) ≤ x1)
    (hTopInter :
      ∀ (x1 w a b : ℕ) (x3 : ℕ → Finset (Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)))),
        (26 : ℕ) ≤ w →
        a ≤ b →
        b < w →
        w < (26 : ℕ) + x1 →
        (∀ x5 < (26 : ℕ), ∃ (x7 : Fin (13 : ℕ) ⊕ Fin (13 : ℕ)), x3 x5 = {Finset.univ.erase x7}) →
        (∀ x6 < x1, ∃ x8 < (26 : ℕ) + x6, ∃ x9 < (26 : ℕ) + x6, x3 ((26 : ℕ) + x6) = x3 x8 ∪ x3 x9 ∨ x3 ((26 : ℕ) + x6) = Finset.image₂ (fun (x10 x11 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x10 ∩ x11) (x3 x8) (x3 x9)) →
        x3 w = Finset.image₂ (fun (x10 x11 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x10 ∩ x11) (x3 a) (x3 b) →
        (∀ x7 ∈ x3 w, PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) x7) →
        (∀ x8 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x8 ∈ x3 w) →
        (∀ u < w, ¬((∀ x7 ∈ x3 u, PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) x7) ∧ (∀ x8 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x8 ∈ x3 u))) →
        (64 : ℕ) ≤ x1) :
    ∀ (x1 x2 : ℕ) (x3 : ℕ → Finset (Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)))), x2 < (26 : ℕ) + x1 → (∀ x5 < (26 : ℕ), ∃ (x7 : Fin (13 : ℕ) ⊕ Fin (13 : ℕ)), x3 x5 = {Finset.univ.erase x7}) → (∀ x6 < x1, ∃ x8 < (26 : ℕ) + x6, ∃ x9 < (26 : ℕ) + x6, x3 ((26 : ℕ) + x6) = x3 x8 ∪ x3 x9 ∨ x3 ((26 : ℕ) + x6) = Finset.image₂ (fun (x10 x11 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x10 ∩ x11) (x3 x8) (x3 x9)) → (∀ x7 ∈ x3 x2, PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) x7) → (∀ x8 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x8 ∈ x3 x2) → (64 : ℕ) ≤ x1 := by
  classical
  intro x1 x2 x3 hlt hInit hStep hFree hCov
  have hInc0 : ((0 : Fin 13), (0 : Fin 13)) ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3 := by
    decide
  have hInc1 : ((1 : Fin 13), (1 : Fin 13)) ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3 := by
    decide
  have hNotRaw : ∀ u, (∀ V ∈ x3 u, PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) V) → 26 ≤ u := by
    intro u hu
    by_contra h
    have hlt26 : u < 26 := Nat.lt_of_not_ge h
    obtain ⟨v, hv⟩ := hInit u hlt26
    have hf := hu (Finset.univ.erase v) (by rw [hv]; exact Finset.mem_singleton_self _)
    by_cases h0 : v ≠ Sum.inl (0 : Fin 13) ∧ v ≠ Sum.inr (0 : Fin 13)
    · apply hf ((0 : Fin 13), (0 : Fin 13)) hInc0
      exact ⟨Finset.mem_erase.mpr ⟨h0.1.symm, Finset.mem_univ _⟩, Finset.mem_erase.mpr ⟨h0.2.symm, Finset.mem_univ _⟩⟩
    · apply hf ((1 : Fin 13), (1 : Fin 13)) hInc1
      have h1 : v ≠ Sum.inl (1 : Fin 13) ∧ v ≠ Sum.inr (1 : Fin 13) := by
        cases v with
        | inl p =>
          have hp0 : p = 0 := by
            by_contra hne
            exact h0 ⟨fun heq => hne (Sum.inl.inj heq), Sum.inl_ne_inr⟩
          subst hp0
          exact ⟨fun heq => by have := Sum.inl.inj heq; exact absurd this (by decide), Sum.inl_ne_inr⟩
        | inr l =>
          have hl0 : l = 0 := by
            by_contra hne
            exact h0 ⟨Sum.inr_ne_inl, fun heq => hne (Sum.inr.inj heq)⟩
          subst hl0
          exact ⟨Sum.inr_ne_inl, fun heq => by have := Sum.inr.inj heq; exact absurd this (by decide)⟩
      exact ⟨Finset.mem_erase.mpr ⟨h1.1.symm, Finset.mem_univ _⟩, Finset.mem_erase.mpr ⟨h1.2.symm, Finset.mem_univ _⟩⟩
  let Good : ℕ → Prop := fun u =>
    (∀ V ∈ x3 u, PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) V) ∧
    (∀ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 Q ∈ x3 u)
  have hex : ∃ u, Good u := ⟨x2, hFree, hCov⟩
  let w : ℕ := Nat.find hex
  have hwGood : Good w := Nat.find_spec hex
  have hwLe : w ≤ x2 := Nat.find_min' hex ⟨hFree, hCov⟩
  have hwMin : ∀ u < w, ¬Good u := fun u hu => Nat.find_min hex hu
  have hwGe : 26 ≤ w := hNotRaw w hwGood.1
  have hwLt : w < 26 + x1 := lt_of_le_of_lt hwLe hlt
  have hgLt : w - 26 < x1 := by omega
  have hwEq : 26 + (w - 26) = w := by omega
  obtain ⟨a, ha, b, hb, hOp⟩ := hStep (w - 26) hgLt
  rw [hwEq] at ha hb hOp
  rcases hOp with hU | hI
  · have hFreeA : ∀ V ∈ x3 a, PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) V :=
      fun V hV => hwGood.1 V (by rw [hU]; exact Finset.mem_union_left _ hV)
    have hFreeB : ∀ V ∈ x3 b, PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) V :=
      fun V hV => hwGood.1 V (by rw [hU]; exact Finset.mem_union_right _ hV)
    have haGe : 26 ≤ a := hNotRaw a hFreeA
    have hbGe : 26 ≤ b := hNotRaw b hFreeB
    have hMissA : ∃ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 Q ∉ x3 a := by
      by_contra hall
      push Not at hall
      exact hwMin a ha ⟨hFreeA, hall⟩
    have hMissB : ∃ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 Q ∉ x3 b := by
      by_contra hall
      push Not at hall
      exact hwMin b hb ⟨hFreeB, hall⟩
    have habNe : a ≠ b := by
      intro heq
      subst heq
      have hsame : x3 w = x3 a := by rw [hU, Finset.union_idempotent]
      exact hwMin a ha ⟨hFreeA, fun Q hQ => by rw [← hsame]; exact hwGood.2 Q hQ⟩
    rcases Nat.lt_or_gt_of_ne habNe with hab | hba
    · exact hTopUnion x1 w a b x3 haGe hab hb hwLt hInit hStep hU hwGood.1 hwGood.2 hMissA hMissB
    · exact hTopUnion x1 w b a x3 hbGe hba ha hwLt hInit hStep (hU.trans (Finset.union_comm _ _)) hwGood.1 hwGood.2 hMissB hMissA
  · rcases le_total a b with hab | hba
    · exact hTopInter x1 w a b x3 hwGe hab hb hwLt hInit hStep hI hwGood.1 hwGood.2 hwMin
    · have hI' : x3 w = Finset.image₂ (fun (x10 x11 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x10 ∩ x11) (x3 b) (x3 a) := by
        rw [hI]
        ext Z
        simp only [Finset.mem_image₂]
        constructor
        · rintro ⟨A, hA, B, hB, rfl⟩
          exact ⟨B, hB, A, hA, Finset.inter_comm B A⟩
        · rintro ⟨B, hB, A, hA, rfl⟩
          exact ⟨A, hA, B, hB, Finset.inter_comm A B⟩
      exact hTopInter x1 w b a x3 hwGe hba ha hwLt hInit hStep hI' hwGood.1 hwGood.2 hwMin
