import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8869_4
    (hOutAnd :
      ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit) (E : Finset (Fin N × Fin N)),
        (87 : ℕ) ≤ q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, (S l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        N + N ≤ C.output ∧ C.output < N + N + C.size →
        have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
        have wv := PEqualNP.CleanedNonEdge.wireVal (N + N) C;
        have ic := PEqualNP.EdgeOwnership.InCone (N + N) C;
        have pi : Fin N × Fin N → Fin (N + N) → Bool := fun e => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2);
        have hit : Fin N × Fin N → Fin (N + N) → ℕ → Prop := fun e v g => g < C.size ∧ (ga g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ Relation.ReflTransGen (fun a b => ∃ k < C.size, b = N + N + k ∧ a ∈ (ga k).inputs ∧ wv a (pi e) = Bool.true ∧ wv b (pi e) = Bool.true) (N + N + g) C.output ∧ ∀ i : Fin (2 : ℕ), (wv (PEqualNP.TopForm.opnd C g i) fun j => decide (j = v)) = Bool.false;
        (ga (C.output - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ P Q : Finset (Fin N), Q.card ≤ q → PEqualNP.GenericRejection.IsFalseInput S P Q → C.eval (PEqualNP.GenericRejection.incidenceInput P Q) = Bool.false) →
        (∀ e ∈ E, e.1 ∈ S e.2 ∧ wv C.output (pi e) = Bool.true ∧ ∃ g1 g2 : ℕ, g1 ≠ g2 ∧ ¬ic g1 g2 ∧ ¬ic g2 g1 ∧ hit e (Fin.castAdd N e.1) g1 ∧ hit e (Fin.natAdd N e.2) g2) →
        E.card ≤ (8 : ℕ) * C.size)
    (hOutOr :
      ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit) (E : Finset (Fin N × Fin N)),
        (87 : ℕ) ≤ q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, (S l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        N + N ≤ C.output ∧ C.output < N + N + C.size →
        have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
        have wv := PEqualNP.CleanedNonEdge.wireVal (N + N) C;
        have ic := PEqualNP.EdgeOwnership.InCone (N + N) C;
        have pi : Fin N × Fin N → Fin (N + N) → Bool := fun e => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2);
        have hit : Fin N × Fin N → Fin (N + N) → ℕ → Prop := fun e v g => g < C.size ∧ (ga g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ Relation.ReflTransGen (fun a b => ∃ k < C.size, b = N + N + k ∧ a ∈ (ga k).inputs ∧ wv a (pi e) = Bool.true ∧ wv b (pi e) = Bool.true) (N + N + g) C.output ∧ ∀ i : Fin (2 : ℕ), (wv (PEqualNP.TopForm.opnd C g i) fun j => decide (j = v)) = Bool.false;
        (ga (C.output - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ P Q : Finset (Fin N), Q.card ≤ q → PEqualNP.GenericRejection.IsFalseInput S P Q → C.eval (PEqualNP.GenericRejection.incidenceInput P Q) = Bool.false) →
        (∀ e ∈ E, e.1 ∈ S e.2 ∧ wv C.output (pi e) = Bool.true ∧ ∃ g1 g2 : ℕ, g1 ≠ g2 ∧ ¬ic g1 g2 ∧ ¬ic g2 g1 ∧ hit e (Fin.castAdd N e.1) g1 ∧ hit e (Fin.natAdd N e.2) g2) →
        E.card ≤ (8 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             have x12 : ℕ → (Fin (x2 + x2) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (x2 + x2) x5;             have x13 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (x2 + x2) x5;             have x14 : Fin x2 × Fin x2 → Fin (x2 + x2) → Bool := fun (x14 : Fin x2 × Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x14.1 ∨ x15 = Fin.natAdd x2 x14.2);             have x15 : Fin x2 × Fin x2 → Fin (x2 + x2) → ℕ → Prop := fun (x15 : Fin x2 × Fin x2) (x16 : Fin (x2 + x2)) (x17 : ℕ) => x17 < x5.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ Relation.ReflTransGen (fun (x18 x19 : ℕ) => ∃ x20 < x5.size, x19 = x2 + x2 + x20 ∧ x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x20).inputs ∧ x12 x18 (x14 x15) = Bool.true ∧ x12 x19 (x14 x15) = Bool.true) (x2 + x2 + x17) x5.output ∧ ∀ (x18 : Fin (2 : ℕ)), (x12 (PEqualNP.TopForm.opnd x5 x17 x18) fun (x19 : Fin (x2 + x2)) => Decidable.decide (x19 = x16)) = Bool.false;             (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → x12 x5.output x16 = Bool.false) → (∀ x17 ∈ x6, x3 x17.1 x17.2 ∧ x12 x5.output (x14 x17) = Bool.true ∧ ∃ (x19 : ℕ) (x20 : ℕ), x19 ≠ x20 ∧ ¬x13 x19 x20 ∧ ¬x13 x20 x19 ∧ x15 x17 (Fin.castAdd x2 x17.1) x19 ∧ x15 x17 (Fin.natAdd x2 x17.2) x20) → x6.card ≤ (8 : ℕ) * x5.size := by
  intro q N R _ C E hq hN hCard hUnique hAO x12 x13 x14 x15 hFalse hE
  by_cases hEmp : E = ∅
  · rw [hEmp, Finset.card_empty]
    exact Nat.zero_le _
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hEmp
    obtain ⟨_, _, g1, _, _, _, _, hhit1, _⟩ := hE e0 he0
    have hg1 : g1 < C.size := hhit1.1
    have hOutBounds : N + N ≤ C.output ∧ C.output < N + N + C.size := by
      rcases Relation.ReflTransGen.cases_tail hhit1.2.2.1 with hEq | ⟨_, _, hStep⟩
      · exact ⟨by omega, by omega⟩
      · obtain ⟨k, hk, hEq, _⟩ := hStep
        exact ⟨by omega, by omega⟩
    let S : Fin N → Finset (Fin N) := fun l => Finset.univ.filter (fun p => R p l)
    have hMemS : ∀ p l : Fin N, p ∈ S l ↔ R p l := by
      intro p l
      constructor
      · intro h; exact (Finset.mem_filter.mp h).2
      · intro h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, h⟩
    have hCardS : ∀ l : Fin N, (S l).card = q + 1 := by
      intro l
      have h1 : (S l).card = Fintype.card { p : Fin N // R p l } := (Fintype.card_subtype (fun p => R p l)).symm
      rw [h1]
      exact hCard l
    have hUniqueS : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l := by
      intro p1 p2 hne
      obtain ⟨l, ⟨h1, h2⟩, hU⟩ := hUnique p1 p2 hne
      refine ⟨l, ⟨(hMemS p1 l).mpr h1, (hMemS p2 l).mpr h2⟩, ?_⟩
      intro l' hl'
      exact hU l' ⟨(hMemS p1 l').mp hl'.1, (hMemS p2 l').mp hl'.2⟩
    have hFalseS : ∀ P Q : Finset (Fin N), Q.card ≤ q →
        PEqualNP.GenericRejection.IsFalseInput S P Q →
        C.eval (PEqualNP.GenericRejection.incidenceInput P Q) = false := by
      intro P Q hQcard hFI
      let f : Fin (N + N) → Bool := fun i =>
        if h : i.val < N then decide ((⟨i.val, h⟩ : Fin N) ∈ P)
        else decide ((⟨i.val - N, by omega⟩ : Fin N) ∈ Q)
      have hListEq : List.ofFn f = PEqualNP.GenericRejection.incidenceInput P Q := by
        change List.ofFn f = List.ofFn (fun p : Fin N => decide (p ∈ P)) ++ List.ofFn (fun l : Fin N => decide (l ∈ Q))
        apply List.ext_getElem
        · simp only [List.length_ofFn, List.length_append]
        · intro i h1 h2
          simp only [List.length_ofFn] at h1
          rw [List.getElem_ofFn]
          by_cases hi : i < N
          · rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact hi), List.getElem_ofFn]
            change (if h : i < N then decide ((⟨i, h⟩ : Fin N) ∈ P) else _) = _
            simp only [hi, ↓reduceDIte]
          · rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
            simp only [List.length_ofFn]
            change (if h : i < N then _ else decide ((⟨i - N, _⟩ : Fin N) ∈ Q)) = _
            simp only [hi, ↓reduceDIte]
      have hCardF : Fintype.card { l : Fin N // f (Fin.natAdd N l) = true } = Q.card := by
        rw [Fintype.card_subtype]
        congr 1
        ext l
        constructor
        · intro hl
          have h2 := (Finset.mem_filter.mp hl).2
          change (if h : N + l.val < N then _ else decide ((⟨N + l.val - N, _⟩ : Fin N) ∈ Q)) = true at h2
          have hnot : ¬(N + l.val < N) := by omega
          simp only [hnot, ↓reduceDIte] at h2
          have heq : (⟨N + l.val - N, by omega⟩ : Fin N) = l := Fin.ext (Nat.add_sub_cancel_left N l.val)
          rw [heq] at h2
          exact of_decide_eq_true h2
        · intro hl
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ l, ?_⟩
          change (if h : N + l.val < N then _ else decide ((⟨N + l.val - N, _⟩ : Fin N) ∈ Q)) = true
          have hnot : ¬(N + l.val < N) := by omega
          simp only [hnot, ↓reduceDIte]
          have heq : (⟨N + l.val - N, by omega⟩ : Fin N) = l := Fin.ext (Nat.add_sub_cancel_left N l.val)
          rw [heq]
          exact decide_eq_true hl
      have hNoEdge : ¬∃ p l : Fin N, R p l ∧ f (Fin.castAdd N p) = true ∧ f (Fin.natAdd N l) = true := by
        rintro ⟨p, l, hRpl, hfp, hfl⟩
        change (if h : p.val < N then decide ((⟨p.val, h⟩ : Fin N) ∈ P) else _) = true at hfp
        simp only [p.isLt, ↓reduceDIte] at hfp
        have hpP : p ∈ P := of_decide_eq_true hfp
        change (if h : N + l.val < N then _ else decide ((⟨N + l.val - N, _⟩ : Fin N) ∈ Q)) = true at hfl
        have hnot : ¬(N + l.val < N) := by omega
        simp only [hnot, ↓reduceDIte] at hfl
        have heq : (⟨N + l.val - N, by omega⟩ : Fin N) = l := Fin.ext (Nat.add_sub_cancel_left N l.val)
        rw [heq] at hfl
        have hlQ : l ∈ Q := of_decide_eq_true hfl
        exact Finset.disjoint_left.mp (hFI l hlQ) ((hMemS p l).mpr hRpl) hpP
      have hEv := hFalse f (by rw [hCardF]; exact hQcard) hNoEdge
      change C.eval (List.ofFn f) = false at hEv
      rw [hListEq] at hEv
      exact hEv
    have hES : ∀ e ∈ E, e.1 ∈ S e.2 ∧ x12 C.output (x14 e) = true ∧
        ∃ g1 g2 : ℕ, g1 ≠ g2 ∧ ¬x13 g1 g2 ∧ ¬x13 g2 g1 ∧
        x15 e (Fin.castAdd N e.1) g1 ∧ x15 e (Fin.natAdd N e.2) g2 := by
      intro e he
      obtain ⟨hR, hOut, hG⟩ := hE e he
      exact ⟨(hMemS e.1 e.2).mpr hR, hOut, hG⟩
    have houtLt : C.output - (N + N) < C.gates.length := by change C.output - (N + N) < C.size; omega
    have hgaOut : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - (N + N)) = C.gates[C.output - (N + N)]'houtLt :=
      List.getD_eq_getElem _ _ houtLt
    rcases hAO.1 (C.gates[C.output - (N + N)]'houtLt) (List.getElem_mem houtLt) with hAnd | hOr
    · exact hOutAnd q N S C E hq hN hCardS hUniqueS hAO hOutBounds (by rw [hgaOut]; exact hAnd) hFalseS hES
    · exact hOutOr q N S C E hq hN hCardS hUniqueS hAO hOutBounds (by rw [hgaOut]; exact hOr) hFalseS hES
