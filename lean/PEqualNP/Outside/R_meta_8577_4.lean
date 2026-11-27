import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8577_4
    (hIrred :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ n →
        n + (1 : ℕ) < E.card →
        (∀ u : Fin n, (u, u) ∈ E) →
        (∀ u v : Fin n, u.val = (0 : ℕ) → (u, v) ∈ E → v.val = (0 : ℕ)) →
        (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + n) C →
        (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C x =
          Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ C.size ∧
          PEqualNP.TopForm.IsAO2 (n + n) D ∧
          (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x =
            Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) ∧
          (∀ g ∈ D.gates, g.inputs.Nodup) ∧
          (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (n + n) → Bool,
            (D.wires (List.ofFn x)).getD (n + n + i.val) Bool.false ≠
            (D.wires (List.ofFn x)).getD (n + n + j.val) Bool.false))
    (hCover :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ n →
        n + (1 : ℕ) < E.card →
        (∀ u : Fin n, (u, u) ∈ E) →
        (∀ u v : Fin n, u.val = (0 : ℕ) → (u, v) ∈ E → v.val = (0 : ℕ)) →
        (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + n) D →
        (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x =
          Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (n + n) → Bool,
          (D.wires (List.ofFn x)).getD (n + n + i.val) Bool.false ≠
          (D.wires (List.ofFn x)).getD (n + n + j.val) Bool.false) →
        ∃ (L R : Finset (Fin n)), (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 + (1 : ℕ) < x2.card → x1 + x1 ≤ x4.size → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x11, x12) ∈ x2 → x12 = x3 x11) ∨ ∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x12, x11) ∈ x2 → x3 x12 = x11) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  intro n E p C hdense _hsize hc4 hmatch hAO hfun hleaf
  have hn2 : (2 : ℕ) ≤ n := by
    by_contra hlt
    have h01 : n = 0 ∨ n = 1 := by omega
    rcases h01 with rfl | rfl
    · have hE0 : E = ∅ := Finset.eq_empty_of_forall_notMem fun e _ => Fin.elim0 e.1
      rw [hE0, Finset.card_empty] at hdense
      omega
    · have hle : E.card ≤ (Finset.univ : Finset (Fin 1 × Fin 1)).card :=
        Finset.card_le_card (Finset.subset_univ E)
      have h1 : (Finset.univ : Finset (Fin 1 × Fin 1)).card = 1 := by decide
      omega
  have hremap :
      ∀ (π : Equiv.Perm (Fin (n + n))) (C0 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (n + n) C0 →
        ∃ C1 : PEqualNP.CircuitLowerBounds.Circuit,
          C1.size = C0.size ∧
          PEqualNP.TopForm.IsAO2 (n + n) C1 ∧
          ∀ x : Fin (n + n) → Bool,
            PEqualNP.MetaComplexity.circuitFun (n + n) C1 x =
              PEqualNP.MetaComplexity.circuitFun (n + n) C0 (fun k => x (π k)) := by
    intro π C0 hAO0
    let σ : ℕ → ℕ := fun w => if hw : w < n + n then (π ⟨w, hw⟩).val else w
    have hσ_lt : ∀ w k : ℕ, w < n + n + k → σ w < n + n + k := by
      intro w k hw
      dsimp only [σ]
      split_ifs with h1
      · have := (π ⟨w, h1⟩).isLt
        omega
      · exact hw
    let rg : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
      fun g => ⟨g.op, g.inputs.map σ⟩
    let C1 : PEqualNP.CircuitLowerBounds.Circuit := ⟨C0.gates.map rg, σ C0.output⟩
    refine ⟨C1, List.length_map _, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg
        rw [List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        exact hAO0.1 g0 hg0
      · intro i hi w hw
        have hi0 : i < C0.size := by
          change i < (C0.gates.map rg).length at hi
          rw [List.length_map] at hi
          exact hi
        have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C1 i =
            rg (PEqualNP.MetaComplexity.NestedCover.gateAt C0 i) := by
          change C1.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
            rg (C0.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
          rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi0]
          change (C0.gates.map rg)[i]'hi = rg (C0.gates[i]'hi0)
          exact List.getElem_map _
        rw [hget, List.mem_map] at hw
        obtain ⟨w0, hw0, rfl⟩ := hw
        exact hσ_lt w0 i (hAO0.2.1 i hi0 w0 hw0)
      · intro g hg
        rw [List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        change (g0.inputs.map σ).length = 2
        rw [List.length_map]
        exact hAO0.2.2 g0 hg0
    · intro x
      let y : Fin (n + n) → Bool := fun k => x (π k)
      have hbase_len : (List.ofFn x).length = n + n := List.length_ofFn
      have hbase_len_y : (List.ofFn y).length = n + n := List.length_ofFn
      have hbase_get : ∀ w : ℕ, w < n + n →
          (List.ofFn x).getD (σ w) Bool.false = (List.ofFn y).getD w Bool.false := by
        intro w hw
        have hsw : σ w < n + n := by
          have := hσ_lt w 0 (by omega)
          omega
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
        simp only [List.getElem_ofFn, y]
        dsimp only [σ]
        simp only [hw, ↓reduceDIte]
      have hstep : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (wx wy : List Bool),
          wx.length = wy.length →
          n + n ≤ wx.length →
          (∀ w : ℕ, w < wx.length → wx.getD (σ w) Bool.false = wy.getD w Bool.false) →
          (gs.map rg).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) wx =
            wx ++ ((gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) wy).drop wy.length) := by
        intro gs
        induction gs with
        | nil =>
          intro wx wy _ _ _
          simp only [List.map_nil, List.foldl_nil, List.drop_length, List.append_nil]
        | cons g rest ih =>
          intro wx wy hlen hge hagree
          have hσ_ge : ∀ w : ℕ, n + n ≤ w → σ w = w := by
            intro w hw
            dsimp only [σ]
            split_ifs with h1 <;> omega
          have heval_eq : g.op.eval ((g.inputs.map σ).map fun i => wx.getD i Bool.false) =
              g.op.eval (g.inputs.map fun i => wy.getD i Bool.false) := by
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro w _
            by_cases hw : w < wx.length
            · exact hagree w hw
            · rw [Function.comp_apply, hσ_ge w (by omega)]
              rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
          set b : Bool := g.op.eval (g.inputs.map fun i => wy.getD i Bool.false)
          have hwx1 : (wx ++ [b]).length = (wy ++ [b]).length := by
            simp only [List.length_append, List.length_singleton, hlen]
          have hagree1 : ∀ w : ℕ, w < (wx ++ [b]).length →
              (wx ++ [b]).getD (σ w) Bool.false = (wy ++ [b]).getD w Bool.false := by
            intro w hw
            simp only [List.length_append, List.length_singleton] at hw
            by_cases hlt : w < wx.length
            · have hsw : σ w < wx.length := by
                have := hσ_lt w (wx.length - (n + n)) (by omega)
                omega
              rw [List.getD_append _ _ _ _ hsw, List.getD_append _ _ _ _ (by omega)]
              exact hagree w hlt
            · have hweq : w = wx.length := by omega
              subst hweq
              rw [hσ_ge wx.length hge]
              rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (by omega)]
              simp only [Nat.sub_self, hlen]
          have hrec := ih (wx ++ [b]) (wy ++ [b]) hwx1
            (by simp only [List.length_append, List.length_singleton]; omega) hagree1
          have hfold_append : ∀ (gs0 : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
              ∃ tail : List Bool, gs0.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) init = init ++ tail := by
            intro gs0
            induction gs0 with
            | nil => intro init; exact ⟨[], by simp⟩
            | cons g0 rs0 ih0 =>
              intro init
              obtain ⟨t, ht⟩ := ih0 (init ++ [g0.op.eval (g0.inputs.map fun i => init.getD i Bool.false)])
              exact ⟨g0.op.eval (g0.inputs.map fun i => init.getD i Bool.false) :: t,
                by simpa [List.foldl_cons, List.append_assoc] using ht⟩
          obtain ⟨t, ht⟩ := hfold_append rest (wy ++ [b])
          simp only [List.map_cons, List.foldl_cons, rg]
          rw [heval_eq]
          change (rest.map rg).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (wx ++ [b]) =
            wx ++ ((rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (wy ++ [b])).drop wy.length)
          rw [hrec, ht]
          have hdrop1 : ((wy ++ [b]) ++ t).drop (wy ++ [b]).length = t := List.drop_left
          have hdrop2 : ((wy ++ [b]) ++ t).drop wy.length = [b] ++ t := by
            rw [List.append_assoc, List.drop_left]
          rw [hdrop1, hdrop2, List.append_assoc]
      have hfold_len : ∀ (gs0 : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
          (gs0.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) init).length = init.length + gs0.length := by
        intro gs0
        induction gs0 with
        | nil => intro init; simp
        | cons g0 rs0 ih0 =>
          intro init
          simp only [List.foldl_cons, ih0, List.length_append, List.length_cons, List.length_nil]
          omega
      have hfold_prefix : ∀ (gs0 : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (k : ℕ),
          k < init.length →
          (gs0.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) init).getD k Bool.false = init.getD k Bool.false := by
        intro gs0
        induction gs0 with
        | nil => intro init k _; rfl
        | cons g0 rs0 ih0 =>
          intro init k hk
          simp only [List.foldl_cons]
          rw [ih0 _ k (by simp only [List.length_append, List.length_singleton]; omega)]
          exact List.getD_append _ _ _ _ hk
      have hwires_eq := hstep C0.gates (List.ofFn x) (List.ofFn y)
        (by rw [hbase_len, hbase_len_y]) (by rw [hbase_len])
        (fun w hw => hbase_get w (by rw [hbase_len] at hw; exact hw))
      change ((C0.gates.map rg).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (List.ofFn x)).getD (σ C0.output) Bool.false =
        (C0.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (List.ofFn y)).getD C0.output Bool.false
      rw [hwires_eq]
      by_cases hout : C0.output < n + n
      · have hsout : σ C0.output < (List.ofFn x).length := by
          rw [hbase_len]
          have := hσ_lt C0.output 0 (by omega)
          omega
        rw [List.getD_append _ _ _ _ hsout]
        rw [hfold_prefix C0.gates (List.ofFn y) C0.output (by rw [hbase_len_y]; exact hout)]
        exact hbase_get C0.output hout
      · have hsout : σ C0.output = C0.output := by
          dsimp only [σ]
          split_ifs with h1 <;> omega
        rw [hsout]
        rw [List.getD_append_right _ _ _ _ (by rw [hbase_len]; omega)]
        rw [hbase_len, hbase_len_y]
        have hleny := hfold_len C0.gates (List.ofFn y)
        rw [hbase_len_y] at hleny
        by_cases hlt : C0.output < n + n + C0.gates.length
        · have h1 : C0.output - (n + n) < ((C0.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (List.ofFn y)).drop (n + n)).length := by
            rw [List.length_drop, hleny]
            omega
          rw [List.getD_eq_getElem _ _ h1, List.getElem_drop, List.getD_eq_getElem _ _ (by omega)]
          congr 1
          omega
        · rw [List.getD_eq_default _ _ (by rw [List.length_drop, hleny]; omega)]
          rw [List.getD_eq_default _ _ (by omega)]
  have hnorm :
      ∃ (E1 : Finset (Fin n × Fin n)) (C1 : PEqualNP.CircuitLowerBounds.Circuit),
        E1.card = E.card ∧
        C1.size = C.size ∧
        (∀ u : Fin n, (u, u) ∈ E1) ∧
        (∀ v : Fin n, (⟨0, by omega⟩, v) ∈ E1 → v = ⟨0, by omega⟩) ∧
        (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E1 ∧ (a, d) ∈ E1 ∧ (b, c) ∈ E1 ∧ (b, d) ∈ E1)) ∧
        PEqualNP.TopForm.IsAO2 (n + n) C1 ∧
        (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C1 x =
          Decidable.decide (∃ u v : Fin n, (u, v) ∈ E1 ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) := by
    let z0 : Fin n := ⟨0, by omega⟩
    rcases hleaf with ⟨u0, hu0⟩ | ⟨v0, hv0⟩
    · let q : Equiv.Perm (Fin n) := Equiv.swap z0 u0
      have hqq : ∀ t : Fin n, q (q t) = t := Equiv.swap_apply_self z0 u0
      let E1 : Finset (Fin n × Fin n) := E.image (fun e => (q e.1, q (p.symm e.2)))
      have hcard1 : E1.card = E.card := by
        apply Finset.card_image_of_injective
        intro e1 e2 heq
        exact Prod.ext (q.injective (Prod.mk.inj heq).1) (p.symm.injective (q.injective (Prod.mk.inj heq).2))
      have hmem1 : ∀ a b : Fin n, (a, b) ∈ E1 ↔ (q a, p (q b)) ∈ E := by
        intro a b
        simp only [E1, Finset.mem_image]
        constructor
        · rintro ⟨⟨u, v⟩, huv, heq⟩
          have h1 : q u = a := (Prod.mk.inj heq).1
          have h2 : q (p.symm v) = b := (Prod.mk.inj heq).2
          have hu : u = q a := by rw [← h1, hqq]
          have hv : v = p (q b) := by
            have hqb : p.symm v = q b := by rw [← h2, hqq]
            rw [← hqb, Equiv.apply_symm_apply]
          rw [← hu, ← hv]
          exact huv
        · intro h
          refine ⟨(q a, p (q b)), h, Prod.ext ?_ ?_⟩
          · exact hqq a
          · rw [Equiv.symm_apply_apply]
            exact hqq b
      let π : Equiv.Perm (Fin (n + n)) :=
        { toFun := Fin.addCases (fun a => Fin.castAdd n (q a)) (fun b => Fin.natAdd n (q (p.symm b)))
          invFun := Fin.addCases (fun a => Fin.castAdd n (q a)) (fun b => Fin.natAdd n (p (q b)))
          left_inv := by
            intro k
            induction k using Fin.addCases with
            | left a => simp only [Fin.addCases_left, hqq]
            | right b => simp only [Fin.addCases_right, hqq, Equiv.apply_symm_apply]
          right_inv := by
            intro k
            induction k using Fin.addCases with
            | left a => simp only [Fin.addCases_left, hqq]
            | right b => simp only [Fin.addCases_right, Equiv.symm_apply_apply, hqq] }
      obtain ⟨C1, hC1sz, hC1AO, hC1fun⟩ := hremap π C hAO
      refine ⟨E1, C1, hcard1, hC1sz, ?_, ?_, ?_, hC1AO, ?_⟩
      · intro u
        exact (hmem1 u u).mpr (hmatch (q u))
      · intro v hv
        have h1 : (q z0, p (q v)) ∈ E := (hmem1 z0 v).mp hv
        have hqz : q z0 = u0 := Equiv.swap_apply_left z0 u0
        rw [hqz] at h1
        have h2 : p (q v) = p u0 := hu0 (p (q v)) h1
        have h3 : q v = u0 := p.injective h2
        have h4 : q (q v) = q u0 := congrArg q h3
        rw [hqq, Equiv.swap_apply_right] at h4
        exact h4
      · intro a b c d hab hcd h
        exact hc4 (q a) (q b) (p (q c)) (p (q d))
          (fun h' => hab (q.injective h'))
          (fun h' => hcd (q.injective (p.injective h')))
          ⟨(hmem1 _ _).mp h.1, (hmem1 _ _).mp h.2.1, (hmem1 _ _).mp h.2.2.1, (hmem1 _ _).mp h.2.2.2⟩
      · intro x
        rw [hC1fun x, hfun (fun k => x (π k))]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨u, v, huv, hu, hv⟩
          refine ⟨q u, q (p.symm v), (hmem1 _ _).mpr ?_, ?_, ?_⟩
          · simpa only [hqq, Equiv.apply_symm_apply] using huv
          · simpa only [π, Equiv.coe_fn_mk, Fin.addCases_left] using hu
          · simpa only [π, Equiv.coe_fn_mk, Fin.addCases_right] using hv
        · rintro ⟨a, b, hab, ha, hb⟩
          refine ⟨q a, p (q b), (hmem1 a b).mp hab, ?_, ?_⟩
          · simpa only [π, Equiv.coe_fn_mk, Fin.addCases_left, hqq] using ha
          · simpa only [π, Equiv.coe_fn_mk, Fin.addCases_right, Equiv.symm_apply_apply, hqq] using hb
    · let u0 : Fin n := p.symm v0
      let q : Equiv.Perm (Fin n) := Equiv.swap z0 u0
      have hqq : ∀ t : Fin n, q (q t) = t := Equiv.swap_apply_self z0 u0
      let E1 : Finset (Fin n × Fin n) := E.image (fun e => (q (p.symm e.2), q e.1))
      have hcard1 : E1.card = E.card := by
        apply Finset.card_image_of_injective
        intro e1 e2 heq
        exact Prod.ext (q.injective (Prod.mk.inj heq).2) (p.symm.injective (q.injective (Prod.mk.inj heq).1))
      have hmem1 : ∀ a b : Fin n, (a, b) ∈ E1 ↔ (q b, p (q a)) ∈ E := by
        intro a b
        simp only [E1, Finset.mem_image]
        constructor
        · rintro ⟨⟨u, v⟩, huv, heq⟩
          have h1 : q (p.symm v) = a := (Prod.mk.inj heq).1
          have h2 : q u = b := (Prod.mk.inj heq).2
          have hu : u = q b := by rw [← h2, hqq]
          have hv : v = p (q a) := by
            have hqa : p.symm v = q a := by rw [← h1, hqq]
            rw [← hqa, Equiv.apply_symm_apply]
          rw [← hu, ← hv]
          exact huv
        · intro h
          refine ⟨(q b, p (q a)), h, Prod.ext ?_ ?_⟩
          · rw [Equiv.symm_apply_apply]
            exact hqq a
          · exact hqq b
      let π : Equiv.Perm (Fin (n + n)) :=
        { toFun := Fin.addCases (fun a => Fin.natAdd n (q a)) (fun b => Fin.castAdd n (q (p.symm b)))
          invFun := Fin.addCases (fun a => Fin.natAdd n (p (q a))) (fun b => Fin.castAdd n (q b))
          left_inv := by
            intro k
            induction k using Fin.addCases with
            | left a => simp only [Fin.addCases_left, Fin.addCases_right, hqq]
            | right b => simp only [Fin.addCases_right, Fin.addCases_left, hqq, Equiv.apply_symm_apply]
          right_inv := by
            intro k
            induction k using Fin.addCases with
            | left a => simp only [Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply, hqq]
            | right b => simp only [Fin.addCases_right, Fin.addCases_left, hqq] }
      obtain ⟨C1, hC1sz, hC1AO, hC1fun⟩ := hremap π C hAO
      refine ⟨E1, C1, hcard1, hC1sz, ?_, ?_, ?_, hC1AO, ?_⟩
      · intro u
        exact (hmem1 u u).mpr (hmatch (q u))
      · intro v hv
        have h1 : (q v, p (q z0)) ∈ E := (hmem1 z0 v).mp hv
        have hqz : p (q z0) = v0 := by
          rw [Equiv.swap_apply_left]
          exact Equiv.apply_symm_apply p v0
        rw [hqz] at h1
        have h2 : p (q v) = v0 := hv0 (q v) h1
        have h3 : q v = u0 := by
          have := congrArg p.symm h2
          simpa only [Equiv.symm_apply_apply] using this
        have h4 : q (q v) = q u0 := congrArg q h3
        rw [hqq, Equiv.swap_apply_right] at h4
        exact h4
      · intro a b c d hab hcd h
        exact hc4 (q c) (q d) (p (q a)) (p (q b))
          (fun h' => hcd (q.injective h'))
          (fun h' => hab (q.injective (p.injective h')))
          ⟨(hmem1 _ _).mp h.1, (hmem1 _ _).mp h.2.2.1, (hmem1 _ _).mp h.2.1, (hmem1 _ _).mp h.2.2.2⟩
      · intro x
        rw [hC1fun x, hfun (fun k => x (π k))]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨u, v, huv, hu, hv⟩
          refine ⟨q (p.symm v), q u, (hmem1 _ _).mpr ?_, ?_, ?_⟩
          · simpa only [hqq, Equiv.apply_symm_apply] using huv
          · simpa only [π, Equiv.coe_fn_mk, Fin.addCases_right] using hv
          · simpa only [π, Equiv.coe_fn_mk, Fin.addCases_left] using hu
        · rintro ⟨a, b, hab, ha, hb⟩
          refine ⟨q b, p (q a), (hmem1 a b).mp hab, ?_, ?_⟩
          · simpa only [π, Equiv.coe_fn_mk, Fin.addCases_left, hqq] using hb
          · simpa only [π, Equiv.coe_fn_mk, Fin.addCases_right, Equiv.symm_apply_apply, hqq] using ha
  obtain ⟨E1, C1, hE1card, hC1size, hmatch1, hleaf1, hc41, hAO1, hfun1⟩ := hnorm
  have hdense1 : n + (1 : ℕ) < E1.card := by omega
  have hleaf1' : ∀ u v : Fin n, u.val = (0 : ℕ) → (u, v) ∈ E1 → v.val = (0 : ℕ) := by
    intro u v hu huv
    have hu0 : u = ⟨0, by omega⟩ := Fin.ext hu
    rw [hu0] at huv
    exact congrArg Fin.val (hleaf1 v huv)
  obtain ⟨D, hDle, hDAO, hDfun, hDnd, hDdist⟩ :=
    hIrred n E1 C1 hn2 hdense1 hmatch1 hleaf1' hc41 hAO1 hfun1
  obtain ⟨L, R, hcov, hcard⟩ :=
    hCover n E1 D hn2 hdense1 hmatch1 hleaf1' hc41 hDAO hDfun hDnd hDdist
  have hLR : n ≤ L.card + R.card := by
    have hunion : (Finset.univ : Finset (Fin n)) ⊆ L ∪ R := by
      intro u _
      exact Finset.mem_union.mpr (hcov (u, u) (hmatch1 u))
    have h1 : n ≤ (L ∪ R).card := by
      have := Finset.card_le_card hunion
      simpa only [Finset.card_univ, Fintype.card_fin] using this
    exact le_trans h1 (Finset.card_union_le L R)
  omega
