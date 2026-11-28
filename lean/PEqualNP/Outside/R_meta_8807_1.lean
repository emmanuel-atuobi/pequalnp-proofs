import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8807_1
    (hInputChild :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (g a b : ℕ) (S : Finset (Fin N)),
        have f : Finset (Fin N) → Finset (Fin N) → List Bool := PEqualNP.GenericRejection.incidenceInput;
        have w : ℕ → Finset (Fin N) → Finset (Fin N) → Bool := fun u A B => PEqualNP.CircuitLowerBounds.wireValue C (f A B) u;
        have pts : Fin N → Finset (Fin N) := fun l => (L l).filter fun p => w (N + N + g) {p} {l} = Bool.true;
        (300 : ℕ) ≤ q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, (L l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        C.output < N + N + C.size →
        PEqualNP.GenericRejection.RightOnIncidentPairs L C →
        (∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B → C.eval (f A B) = Bool.false) →
        g < C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [a, b] →
        a < N + N + g →
        b < N + N + g →
        (a < N + N ∨ b < N + N) →
        (100 : ℕ) < S.card →
        Set.InjOn pts ↑S →
        (∀ l ∈ S, (1 : ℕ) < (pts l).card ∧ w (N + N + g) (L l)ᶜ {l} = Bool.false) →
        N * q ≤ (100 : ℕ) * C.size)
    (hGateChildren :
      ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (g a b : ℕ) (S : Finset (Fin N)),
        have f : Finset (Fin N) → Finset (Fin N) → List Bool := PEqualNP.GenericRejection.incidenceInput;
        have w : ℕ → Finset (Fin N) → Finset (Fin N) → Bool := fun u A B => PEqualNP.CircuitLowerBounds.wireValue C (f A B) u;
        have pts : Fin N → Finset (Fin N) := fun l => (L l).filter fun p => w (N + N + g) {p} {l} = Bool.true;
        (300 : ℕ) ≤ q →
        N = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin N, (L l).card = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        C.output < N + N + C.size →
        PEqualNP.GenericRejection.RightOnIncidentPairs L C →
        (∀ A B : Finset (Fin N), B.card ≤ q → PEqualNP.GenericRejection.IsFalseInput L A B → C.eval (f A B) = Bool.false) →
        g < C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [a, b] →
        N + N ≤ a →
        a < N + N + g →
        N + N ≤ b →
        b < N + N + g →
        (100 : ℕ) < S.card →
        Set.InjOn pts ↑S →
        (∀ l ∈ S, (1 : ℕ) < (pts l).card ∧ w (N + N + g) (L l)ᶜ {l} = Bool.false) →
        N * q ≤ (100 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (300 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →             x4.output < x2 + x2 + x4.size →               PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →                 (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) →                   (∃ x13 < x4.size,                       (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                         ∃ (x14 : Finset (Fin x2)),                           (100 : ℕ) < x14.card ∧                             have x15 : Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2) => {x16 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16} {x15}) (x2 + x2 + x13) = Bool.true};                             Set.InjOn x15 ↑x14 ∧ ∀ x16 ∈ x14, (1 : ℕ) < (x15 x16).card ∧ x15 x16 ⊆ x3 x16 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x16)ᶜ {x16}) (x2 + x2 + x13) = Bool.false) →                     x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q N L C hq hN hLcard hProj hAO hout hRight hFalse hWit
  obtain ⟨g, hglt, hgop, S, hScard, hInj, hSprop⟩ := hWit
  have hgmem : PEqualNP.MetaComplexity.NestedCover.gateAt C g ∈ C.gates := by
    change C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hglt]
    exact List.getElem_mem hglt
  have hlen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.length = 2 := hAO.2.2 _ hgmem
  cases hinp : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs with
  | nil => rw [hinp] at hlen2; simp at hlen2
  | cons a rest =>
    cases rest with
    | nil => rw [hinp] at hlen2; simp at hlen2
    | cons b tail =>
      cases tail with
      | cons _ _ => rw [hinp] at hlen2; simp at hlen2
      | nil =>
        have ha_lt : a < N + N + g := hAO.2.1 g hglt a (by rw [hinp]; simp)
        have hb_lt : b < N + N + g := hAO.2.1 g hglt b (by rw [hinp]; simp)
        have hpts_eq : ∀ l ∈ S,
            (L l).filter (fun p => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) (N + N + g) = Bool.true) =
            Finset.univ.filter (fun p => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) (N + N + g) = Bool.true) := by
          intro l hl
          ext p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact fun h => h.2
          · intro hp
            exact ⟨(hSprop l hl).2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩), hp⟩
        have hInj' : Set.InjOn (fun l => (L l).filter fun p => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) (N + N + g) = Bool.true) ↑S := by
          intro l1 hl1 l2 hl2 heq
          dsimp only at heq
          rw [hpts_eq l1 hl1, hpts_eq l2 hl2] at heq
          exact hInj hl1 hl2 heq
        have hSprop' : ∀ l ∈ S,
            (1 : ℕ) < ((L l).filter fun p => PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput {p} {l}) (N + N + g) = Bool.true).card ∧
            PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput (L l)ᶜ {l}) (N + N + g) = Bool.false := by
          intro l hl
          rw [hpts_eq l hl]
          exact ⟨(hSprop l hl).1, (hSprop l hl).2.2⟩
        by_cases hIn : a < N + N ∨ b < N + N
        · exact hInputChild q N L C g a b S hq hN hLcard hProj hAO hout hRight hFalse hglt hgop hinp ha_lt hb_lt hIn hScard hInj' hSprop'
        · push Not at hIn
          exact hGateChildren q N L C g a b S hq hN hLcard hProj hAO hout hRight hFalse hglt hgop hinp hIn.1 ha_lt hIn.2 hb_lt hScard hInj' hSprop'
