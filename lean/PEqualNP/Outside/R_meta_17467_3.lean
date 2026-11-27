import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17467_3
    (hLowDeg :
      ∀ (a b : ℕ),
        let T : Type := Finset (Fin a × Fin b);
        have comp : T → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun F C => PEqualNP.TopForm.IsAO2 (a + b) C ∧ PEqualNP.MetaComplexity.circuitFun (a + b) C = PEqualNP.ReadTwo.fpl a fun i j => (i, j) ∈ F;
        have leaf : T → Fin a × Fin b → Prop := fun F e => (∀ f ∈ F, f.1 = e.1 → f = e) ∨ ∀ f ∈ F, f.2 = e.2 → f = e;
        have P : T → Prop := fun E =>
          have G : SimpleGraph (Fin (a + b)) := SimpleGraph.fromRel fun u v => ∃ e ∈ E, u = Fin.castAdd b e.1 ∧ v = Fin.natAdd a e.2;
          (6 : ℕ) ≤ E.card ∧
            ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
              have S : Set (Fin a × Fin b) := {e | e ∈ E ∧ (leaf E e ∨ ∃ D, D.size < C.size ∧ comp (E.erase e) D)};
              C.size + (3 : ℕ) ≤ (2 : ℕ) * E.card ∧ comp E C ∧
              (PEqualNP.ReadTwo.Lin fun i j => (i, j) ∈ E) ∧ ¬G.IsAcyclic ∧
              (∀ (v : Fin (a + b)),
                have d : ℕ := (G.neighborSet v).ncard;
                have R : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) C ↑v;
                (2 : ℕ) ≤ d → R.card ≤ d ∧ (d = R.card → ∀ k ∈ R, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (a + b) C k ⊆ R)) ∧
              Set.InjOn Prod.fst S ∧ Set.InjOn Prod.snd S;
        ∀ (E : T), (7 : ℕ) ≤ E.card → P E →
          (∃ e ∈ E, leaf E e ∧ (E.filter fun f => f.1 = e.1).card ≤ (2 : ℕ) ∧ (E.filter fun f => f.2 = e.2).card ≤ (2 : ℕ)) →
          ∃ E' ⊂ E, P E')
    (hHighDeg :
      ∀ (a b : ℕ),
        let T : Type := Finset (Fin a × Fin b);
        have comp : T → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun F C => PEqualNP.TopForm.IsAO2 (a + b) C ∧ PEqualNP.MetaComplexity.circuitFun (a + b) C = PEqualNP.ReadTwo.fpl a fun i j => (i, j) ∈ F;
        have leaf : T → Fin a × Fin b → Prop := fun F e => (∀ f ∈ F, f.1 = e.1 → f = e) ∨ ∀ f ∈ F, f.2 = e.2 → f = e;
        have P : T → Prop := fun E =>
          have G : SimpleGraph (Fin (a + b)) := SimpleGraph.fromRel fun u v => ∃ e ∈ E, u = Fin.castAdd b e.1 ∧ v = Fin.natAdd a e.2;
          (6 : ℕ) ≤ E.card ∧
            ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
              have S : Set (Fin a × Fin b) := {e | e ∈ E ∧ (leaf E e ∨ ∃ D, D.size < C.size ∧ comp (E.erase e) D)};
              C.size + (3 : ℕ) ≤ (2 : ℕ) * E.card ∧ comp E C ∧
              (PEqualNP.ReadTwo.Lin fun i j => (i, j) ∈ E) ∧ ¬G.IsAcyclic ∧
              (∀ (v : Fin (a + b)),
                have d : ℕ := (G.neighborSet v).ncard;
                have R : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) C ↑v;
                (2 : ℕ) ≤ d → R.card ≤ d ∧ (d = R.card → ∀ k ∈ R, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (a + b) C k ⊆ R)) ∧
              Set.InjOn Prod.fst S ∧ Set.InjOn Prod.snd S;
        ∀ (E : T), (7 : ℕ) ≤ E.card → P E → (∃ e ∈ E, leaf E e) →
          (∀ e ∈ E, leaf E e → (3 : ℕ) ≤ (E.filter fun f => f.1 = e.1).card ∨ (3 : ℕ) ≤ (E.filter fun f => f.2 = e.2).card) →
          ∃ E' ⊂ E, P E') :
    ∀ (x1 x2 : ℕ),   have x3 : Finset (Fin x1 × Fin x2) → SimpleGraph (Fin (x1 + x2)) := fun (x3 : Finset (Fin x1 × Fin x2)) => SimpleGraph.fromRel fun (x4 x5 : Fin (x1 + x2)) => ∃ x6 ∈ x3, x4 = Fin.castAdd x2 x6.1 ∧ x5 = Fin.natAdd x1 x6.2;   have x4 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = PEqualNP.ReadTwo.fpl x1 fun (x6 : Fin x1) (x7 : Fin x2) => (x6, x7) ∈ x4;   have x5 : Finset (Fin x1 × Fin x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Finset (Fin x1 × Fin x2)) (x6 : Fin x1 × Fin x2) => (∀ x7 ∈ x5, x7.1 = x6.1 → x7 = x6) ∨ ∀ x7 ∈ x5, x7.2 = x6.2 → x7 = x6;   have x6 : Finset (Fin x1 × Fin x2) → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) =>     (6 : ℕ) ≤ x6.card ∧       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         have x8 : Set (Fin x1 × Fin x2) := {x8 : Fin x1 × Fin x2 | x8 ∈ x6 ∧ (x5 x6 x8 ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size < x7.size ∧ x4 (x6.erase x8) x9)};         x7.size + (3 : ℕ) ≤ (2 : ℕ) * x6.card ∧           x4 x6 x7 ∧             (PEqualNP.ReadTwo.Lin fun (x9 : Fin x1) (x10 : Fin x2) => (x9, x10) ∈ x6) ∧               ¬(x3 x6).IsAcyclic ∧                 (∀ (x9 : Fin (x1 + x2)),                     have x10 : ℕ := ((x3 x6).neighborSet x9).ncard;                     have x11 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x7 ↑x9;                     (2 : ℕ) ≤ x10 → x11.card ≤ x10 ∧ (x10 = x11.card → ∀ x14 ∈ x11, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (x1 + x2) x7 x14 ⊆ x11)) ∧                   Set.InjOn Prod.fst x8 ∧ Set.InjOn Prod.snd x8;   ∀ (x7 : Finset (Fin x1 × Fin x2)), x6 x7 → (∃ x9 ∈ x7, x5 x7 x9) → ∃ x10 ⊂ x7, x6 x10 := by
  classical
  intro a b Gf compf leaff Pf E hP hLeaf
  rcases hP with ⟨hCard6, C, hSz, hComp, hLin, hNA, hR, hInj1, hInj2⟩
  have hCard7 : (7 : ℕ) ≤ E.card := by
    let G : SimpleGraph (Fin (a + b)) := Gf E
    have hAdj_bip : ∀ u v : Fin (a + b), G.Adj u v →
        (∃ e ∈ E, (u = Fin.castAdd b e.1 ∧ v = Fin.natAdd a e.2) ∨ (v = Fin.castAdd b e.1 ∧ u = Fin.natAdd a e.2)) := by
      intro u v huv
      rcases huv with ⟨_, ⟨e, he, h1, h2⟩ | ⟨e, he, h1, h2⟩⟩
      · exact ⟨e, he, Or.inl ⟨h1, h2⟩⟩
      · exact ⟨e, he, Or.inr ⟨h1, h2⟩⟩
    have hSide_flip : ∀ u v : Fin (a + b), G.Adj u v → (u.val < a ↔ ¬ v.val < a) := by
      intro u v huv
      obtain ⟨e, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hAdj_bip u v huv
      · simp only [Fin.val_castAdd, Fin.val_natAdd, e.1.isLt, true_iff]; omega
      · simp only [Fin.val_castAdd, Fin.val_natAdd, e.1.isLt, not_true_eq_false, iff_false]; omega
    have hWalk_parity : ∀ {u v : Fin (a + b)} (w : G.Walk u v),
        Even w.length ↔ (u.val < a ↔ v.val < a) := by
      intro u v w
      induction w with
      | nil => simp
      | cons h ih =>
        have hfl := hSide_flip _ _ h
        simp only [SimpleGraph.Walk.length_cons, Nat.even_add_one]
        tauto
    have hNotAcyc : ∃ v : Fin (a + b), ∃ c : G.Walk v v, c.IsCycle := by
      by_contra hall
      push Not at hall
      exact hNA hall
    obtain ⟨v0, c, hc⟩ := hNotAcyc
    have hEven : Even c.length := (hWalk_parity c).mpr Iff.rfl
    have hGe3 : 3 ≤ c.length := hc.three_le_length
    have hNe4 : c.length ≠ 4 := by
      intro hlen4
      cases c with
      | nil => simp at hlen4
      | cons h01 w1 =>
        rename_i v1
        cases w1 with
        | nil => simp at hlen4
        | cons h12 w2 =>
          rename_i v2
          cases w2 with
          | nil => simp at hlen4
          | cons h23 w3 =>
            rename_i v3
            cases w3 with
            | nil => simp at hlen4
            | cons h34 w4 =>
              cases w4 with
              | cons _ _ => simp at hlen4
              | nil =>
                have hnd := hc.support_nodup
                simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
                  List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
                rcases hnd with ⟨h1_ne, h2_ne, h3_ne, _⟩
                have hne02 : v0 ≠ v2 := fun heq => h2_ne (Or.inr heq.symm)
                have hne13 : v1 ≠ v3 := fun heq => h1_ne (Or.inr (Or.inl heq))
                have hEdgeMem : ∀ {x y : Fin (a + b)}, G.Adj x y →
                    (x.val < a → ∃ (i : Fin a) (j : Fin b), (i, j) ∈ E ∧ x = Fin.castAdd b i ∧ y = Fin.natAdd a j) ∧
                    (¬ x.val < a → ∃ (i : Fin a) (j : Fin b), (i, j) ∈ E ∧ y = Fin.castAdd b i ∧ x = Fin.natAdd a j) := by
                  intro x y hxy
                  obtain ⟨⟨i, j⟩, hij, ⟨hx, hy⟩ | ⟨hy, hx⟩⟩ := hAdj_bip x y hxy
                  · constructor
                    · intro _; exact ⟨i, j, hij, hx, hy⟩
                    · intro hno; exfalso; rw [hx] at hno; exact hno i.isLt
                  · constructor
                    · intro hyes; exfalso; rw [hx] at hyes; simp only [Fin.val_natAdd] at hyes; omega
                    · intro _; exact ⟨i, j, hij, hy, hx⟩
                have hNatInj : ∀ {x y : Fin b}, Fin.natAdd a x = Fin.natAdd a y → x = y := fun h =>
                  Fin.ext (by have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; omega)
                by_cases hv0L : v0.val < a
                · obtain ⟨i0, j1, he01, hv0, hv1⟩ := (hEdgeMem h01).1 hv0L
                  have hv1R : ¬ v1.val < a := (hSide_flip _ _ h01).mp hv0L
                  obtain ⟨i2, j1', he21, hv2, hv1'⟩ := (hEdgeMem h12).2 hv1R
                  have hj1 : j1' = j1 := hNatInj (hv1'.symm.trans hv1)
                  rw [hj1] at he21
                  have hv2L : v2.val < a := by rw [hv2]; exact i2.isLt
                  obtain ⟨i2', j3, he23, hv2', hv3⟩ := (hEdgeMem h23).1 hv2L
                  have hi2 : i2' = i2 := Fin.castAdd_inj.mp (hv2'.symm.trans hv2)
                  rw [hi2] at he23
                  have hv3R : ¬ v3.val < a := (hSide_flip _ _ h23).mp hv2L
                  obtain ⟨i0', j3', he03, hv0', hv3'⟩ := (hEdgeMem h34).2 hv3R
                  have hi0 : i0' = i0 := Fin.castAdd_inj.mp (hv0'.symm.trans hv0)
                  have hj3 : j3' = j3 := hNatInj (hv3'.symm.trans hv3)
                  rw [hi0, hj3] at he03
                  have hi_ne : i0 ≠ i2 := fun heq => hne02 (hv0.trans (by rw [heq, ← hv2]))
                  have hj_ne : j1 ≠ j3 := fun heq => hne13 (hv1.trans (by rw [heq, ← hv3]))
                  exact hLin i0 i2 j1 j3 hi_ne hj_ne ⟨he01, he21, he03, he23⟩
                · obtain ⟨i1, j0, he10, hv1, hv0⟩ := (hEdgeMem h01).2 hv0L
                  have hv1L : v1.val < a := by rw [hv1]; exact i1.isLt
                  obtain ⟨i1', j2, he12, hv1', hv2⟩ := (hEdgeMem h12).1 hv1L
                  have hi1 : i1' = i1 := Fin.castAdd_inj.mp (hv1'.symm.trans hv1)
                  rw [hi1] at he12
                  have hv2R : ¬ v2.val < a := (hSide_flip _ _ h12).mp hv1L
                  obtain ⟨i3, j2', he32, hv3, hv2'⟩ := (hEdgeMem h23).2 hv2R
                  have hj2 : j2' = j2 := hNatInj (hv2'.symm.trans hv2)
                  rw [hj2] at he32
                  have hv3L : v3.val < a := by rw [hv3]; exact i3.isLt
                  obtain ⟨i3', j0', he30, hv3', hv0'⟩ := (hEdgeMem h34).1 hv3L
                  have hi3 : i3' = i3 := Fin.castAdd_inj.mp (hv3'.symm.trans hv3)
                  have hj0 : j0' = j0 := hNatInj (hv0'.symm.trans hv0)
                  rw [hi3, hj0] at he30
                  have hi_ne : i1 ≠ i3 := fun heq => hne13 (hv1.trans (by rw [heq, ← hv3]))
                  have hj_ne : j0 ≠ j2 := fun heq => hne02 (hv0.trans (by rw [heq, ← hv2]))
                  exact hLin i1 i3 j0 j2 hi_ne hj_ne ⟨he10, he30, he12, he32⟩
    have hGe6 : 6 ≤ c.length := by
      rcases hEven with ⟨k, hk⟩
      omega
    obtain ⟨e0, he0E, he0Leaf⟩ := hLeaf
    let s0 : Sym2 (Fin (a + b)) := s(Fin.castAdd b e0.1, Fin.natAdd a e0.2)
    have hs0_not_in : s0 ∉ c.edges := by
      intro hs0mem
      have hNatInj2 : ∀ {x y : Fin b}, Fin.natAdd a x = Fin.natAdd a y → x = y := fun h =>
        Fin.ext (by have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; omega)
      have hDeg2 : ∀ u : Fin (a + b), u ∈ c.support → ∃ v1 v2 : Fin (a + b), v1 ≠ v2 ∧ G.Adj u v1 ∧ G.Adj u v2 := by
        intro u hu
        let c' := c.rotate u hu
        have hc' : c'.IsCycle := hc.rotate hu
        cases hc'_eq : c' with
        | nil =>
          have hlen := hc'.three_le_length
          rw [hc'_eq] at hlen
          simp at hlen
        | cons h1 w1 =>
          rename_i v1
          have hrev := (hc'.reverse)
          cases hrev_eq : c'.reverse with
          | nil =>
            have hlen := hrev.three_le_length
            rw [hrev_eq] at hlen
            simp at hlen
          | cons h2 w2 =>
            rename_i v2
            refine ⟨v1, v2, ?_, h1, h2⟩
            intro hveq
            have hnd := hc'.edges_nodup
            have hlen_c' : 2 ≤ c'.edges.length := by
              rw [SimpleGraph.Walk.length_edges]
              have := hc'.three_le_length
              omega
            have hhead_c' : c'.edges.head? = some s(u, v1) := by
              rw [hc'_eq]
              rfl
            have hgetLast : c'.edges.getLast? = some s(u, v2) := by
              have hre := SimpleGraph.Walk.edges_reverse c'
              have hr : c'.edges.reverse.head? = some s(u, v2) := by
                rw [← hre, hrev_eq]
                rfl
              rwa [List.head?_reverse] at hr
            cases he : c'.edges with
            | nil => rw [he] at hlen_c'; simp at hlen_c'
            | cons e1 es =>
              cases es with
              | nil => rw [he] at hlen_c'; simp at hlen_c'
              | cons e2 rest =>
                rw [he] at hhead_c' hgetLast hnd
                simp only [List.head?_cons, Option.some.injEq] at hhead_c'
                have hgl : (e2 :: rest).getLast (List.cons_ne_nil _ _) = s(u, v2) := by
                  have := hgetLast
                  simp only [List.getLast?_cons_cons] at this
                  simpa only [List.getLast?_eq_some_getLast (List.cons_ne_nil e2 rest), Option.some.injEq] using this
                have hmem_tail : s(u, v2) ∈ e2 :: rest := by
                  rw [← hgl]
                  exact List.getLast_mem _
                rw [hhead_c', hveq] at hnd
                exact (List.nodup_cons.mp hnd).1 hmem_tail
      rcases he0Leaf with hL | hR
      · have hu_sup : Fin.castAdd b e0.1 ∈ c.support :=
          SimpleGraph.Walk.fst_mem_support_of_mem_edges c hs0mem
        obtain ⟨v1, v2, hvne, hv1, hv2⟩ := hDeg2 _ hu_sup
        obtain ⟨f1, hf1E, ⟨h11, h12⟩ | ⟨h11, h12⟩⟩ := hAdj_bip _ _ hv1
        · have hf1eq : f1 = e0 := hL f1 hf1E (Fin.castAdd_inj.mp h11.symm)
          obtain ⟨f2, hf2E, ⟨h21, h22⟩ | ⟨h21, h22⟩⟩ := hAdj_bip _ _ hv2
          · have hf2eq : f2 = e0 := hL f2 hf2E (Fin.castAdd_inj.mp h21.symm)
            exact hvne (h12.trans (by rw [hf1eq, ← hf2eq, ← h22]))
          · have hlt := congrArg Fin.val h22
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hlt
            omega
        · have hlt := congrArg Fin.val h12
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hlt
          omega
      · have hu_sup : Fin.natAdd a e0.2 ∈ c.support :=
          SimpleGraph.Walk.snd_mem_support_of_mem_edges c hs0mem
        obtain ⟨v1, v2, hvne, hv1, hv2⟩ := hDeg2 _ hu_sup
        obtain ⟨f1, hf1E, ⟨h11, h12⟩ | ⟨h11, h12⟩⟩ := hAdj_bip _ _ hv1
        · have hlt := congrArg Fin.val h11
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hlt
          omega
        · have hf1eq : f1 = e0 := hR f1 hf1E (hNatInj2 h12.symm)
          obtain ⟨f2, hf2E, ⟨h21, h22⟩ | ⟨h21, h22⟩⟩ := hAdj_bip _ _ hv2
          · have hlt := congrArg Fin.val h21
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hlt
            omega
          · have hf2eq : f2 = e0 := hR f2 hf2E (hNatInj2 h22.symm)
            exact hvne (h11.trans (by rw [hf1eq, ← hf2eq, ← h21]))
    let φ : Fin a × Fin b → Sym2 (Fin (a + b)) := fun e => s(Fin.castAdd b e.1, Fin.natAdd a e.2)
    have hSub : insert s0 c.edges.toFinset ⊆ E.image φ := by
      intro s hs
      simp only [Finset.mem_insert, List.mem_toFinset] at hs
      rcases hs with rfl | hsc
      · exact Finset.mem_image.mpr ⟨e0, he0E, rfl⟩
      · have hse : s ∈ G.edgeSet := SimpleGraph.Walk.edges_subset_edgeSet c hsc
        refine Sym2.ind (fun u v huv => ?_) s hse
        obtain ⟨e, heE, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hAdj_bip u v huv
        · exact Finset.mem_image.mpr ⟨e, heE, rfl⟩
        · exact Finset.mem_image.mpr ⟨e, heE, Sym2.eq_swap⟩
    have hcard1 : (insert s0 c.edges.toFinset).card = c.edges.toFinset.card + 1 :=
      Finset.card_insert_of_notMem (by simpa only [List.mem_toFinset] using hs0_not_in)
    have hcard2 : c.edges.toFinset.card = c.length := by
      rw [List.toFinset_card_of_nodup hc.edges_nodup, SimpleGraph.Walk.length_edges]
    have hcard3 : (insert s0 c.edges.toFinset).card ≤ (E.image φ).card := Finset.card_le_card hSub
    have hcard4 : (E.image φ).card ≤ E.card := Finset.card_image_le
    omega
  have hP' : Pf E := ⟨hCard6, C, hSz, hComp, hLin, hNA, hR, hInj1, hInj2⟩
  by_cases hLow : ∃ e ∈ E, leaff E e ∧ (E.filter fun f => f.1 = e.1).card ≤ (2 : ℕ) ∧ (E.filter fun f => f.2 = e.2).card ≤ (2 : ℕ)
  · exact hLowDeg a b E hCard7 hP' hLow
  · apply hHighDeg a b E hCard7 hP' hLeaf
    intro e he hle
    by_contra hno
    push Not at hno
    exact hLow ⟨e, he, hle, by omega, by omega⟩
