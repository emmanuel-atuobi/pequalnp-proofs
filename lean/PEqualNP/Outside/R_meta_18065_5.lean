import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18065_5
    (hIrred :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ n →
        (∀ u : Fin n, (u, u) ∈ E) →
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
            PEqualNP.EdgeOwnership.gateVal (n + n) D i.val x ≠
            PEqualNP.EdgeOwnership.gateVal (n + n) D j.val x))
    (hClean :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ n →
        (∀ u : Fin n, (u, u) ∈ E) →
        (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + n) C →
        (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C x =
          Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ i j : Fin C.size, i ≠ j → ∃ x : Fin (n + n) → Bool,
          PEqualNP.EdgeOwnership.gateVal (n + n) C i.val x ≠
          PEqualNP.EdgeOwnership.gateVal (n + n) C j.val x) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ C.size ∧
          PEqualNP.TopForm.IsAO2 (n + n) D ∧
          (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x =
            PEqualNP.MetaComplexity.circuitFun (n + n) C x) ∧
          ∀ j < D.gates.length,
            (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ∀ x : Fin (n + n) → Bool, PEqualNP.EdgeOwnership.gateVal (n + n) D j x = Bool.true →
              ∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) → (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x10.size ≤ x4.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x10 ∧ (∀ (x11 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x10 x11 = PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x11) ∧ ∀ x11 < x10.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x14 : Fin (x1 + x1) → Bool), PEqualNP.EdgeOwnership.gateVal (x1 + x1) x10 x11 x14 = Bool.true → ∃ (x16 : Fin x1) (x17 : Fin x1), (x16, x17) ∈ x2 ∧ x14 (Fin.castAdd x1 x16) = Bool.true ∧ x14 (Fin.natAdd x1 x17) = Bool.true := by
  classical
  intro n E p C hPos hC4 hMatch hAO hFun
  by_cases hn1 : n = 1
  · subst hn1
    have h00 : ((0 : Fin 1), (0 : Fin 1)) ∈ E := by
      have hm := hMatch 0
      have hp0 : p 0 = 0 := Subsingleton.elim (p 0) 0
      rwa [hp0] at hm
    have hCsize_pos : 1 ≤ C.size := by
      by_contra h0
      have hlen0 : C.gates.length = 0 := by change ¬1 ≤ C.gates.length at h0; omega
      have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero hlen0
      let x11 : Fin (1 + 1) → Bool := fun _ => true
      have h11 := hFun x11
      have h11t : Decidable.decide (∃ (u v : Fin 1), (u, v) ∈ E ∧ x11 (Fin.castAdd 1 u) = true ∧ x11 (Fin.natAdd 1 v) = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨0, 0, h00, rfl, rfl⟩
      rw [h11t] at h11
      have h11e : PEqualNP.MetaComplexity.circuitFun (1 + 1) C x11 = (List.ofFn x11).getD C.output false := by
        change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x11)).getD C.output false = (List.ofFn x11).getD C.output false
        rw [hnil, List.foldl_nil]
      rw [h11e] at h11
      have hout_lt : C.output < 2 := by
        by_contra hge
        have hnone : (List.ofFn x11).getD C.output false = false := by
          rw [List.getD_eq_default _ _ (by simp; omega)]
        rw [hnone] at h11
        exact Bool.noConfusion h11
      by_cases hout0 : C.output = 0
      · let x10 : Fin (1 + 1) → Bool := fun v => decide (v.val = 0)
        have h10 := hFun x10
        have h10e : PEqualNP.MetaComplexity.circuitFun (1 + 1) C x10 = true := by
          change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x10)).getD C.output false = true
          rw [hnil, List.foldl_nil, hout0]
          rfl
        have h10f : Decidable.decide (∃ (u v : Fin 1), (u, v) ∈ E ∧ x10 (Fin.castAdd 1 u) = true ∧ x10 (Fin.natAdd 1 v) = true) = false := by
          simp only [decide_eq_false_iff_not, not_exists, not_and]
          intro u v _ _ hv
          simp only [x10, Fin.val_natAdd, decide_eq_true_eq] at hv
          omega
        rw [h10e, h10f] at h10
        exact Bool.noConfusion h10
      · have hout1 : C.output = 1 := by omega
        let x01 : Fin (1 + 1) → Bool := fun v => decide (v.val = 1)
        have h01 := hFun x01
        have h01e : PEqualNP.MetaComplexity.circuitFun (1 + 1) C x01 = true := by
          change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x01)).getD C.output false = true
          rw [hnil, List.foldl_nil, hout1]
          rfl
        have h01f : Decidable.decide (∃ (u v : Fin 1), (u, v) ∈ E ∧ x01 (Fin.castAdd 1 u) = true ∧ x01 (Fin.natAdd 1 v) = true) = false := by
          simp only [decide_eq_false_iff_not, not_exists, not_and]
          intro u v _ hu
          simp only [x01, Fin.val_castAdd, decide_eq_true_eq] at hu
          omega
        rw [h01e, h01f] at h01
        exact Bool.noConfusion h01
    let D1 : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩], 2⟩
    refine ⟨D1, hCsize_pos, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [D1, List.mem_singleton] at hg
        subst hg
        left
        rfl
      · intro j hj w hw
        simp only [D1, List.length_singleton] at hj
        have hj0 : j = 0 := by omega
        subst hj0
        change w ∈ [0, 1] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> omega
      · intro g hg
        simp only [D1, List.mem_singleton] at hg
        subst hg
        rfl
    · intro x
      rw [hFun x]
      have hD1e : PEqualNP.MetaComplexity.circuitFun (1 + 1) D1 x = (x ⟨0, by omega⟩ && x ⟨1, by omega⟩) := by
        change (D1.wires (List.ofFn x)).getD 2 false = (x ⟨0, by omega⟩ && x ⟨1, by omega⟩)
        have hof : List.ofFn x = [x ⟨0, by omega⟩, x ⟨1, by omega⟩] := by
          simp only [List.ofFn_succ, List.ofFn_zero]
          rfl
        rw [hof]
        cases hx0 : x ⟨0, by omega⟩ <;> cases hx1 : x ⟨1, by omega⟩ <;> rfl
      rw [hD1e]
      symm
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.and_eq_true]
      constructor
      · rintro ⟨u, v, _, hu, hv⟩
        have hu0 : u = 0 := Subsingleton.elim u 0
        have hv0 : v = 0 := Subsingleton.elim v 0
        subst hu0
        subst hv0
        exact ⟨hu, hv⟩
      · rintro ⟨h0, h1⟩
        exact ⟨0, 0, h00, h0, h1⟩
    · intro j hj _ x hv
      simp only [D1, List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      have hgv : PEqualNP.EdgeOwnership.gateVal (1 + 1) D1 0 x = (x ⟨0, by omega⟩ && x ⟨1, by omega⟩) := by
        change (D1.wires (List.ofFn x)).getD 2 false = (x ⟨0, by omega⟩ && x ⟨1, by omega⟩)
        have hof : List.ofFn x = [x ⟨0, by omega⟩, x ⟨1, by omega⟩] := by
          simp only [List.ofFn_succ, List.ofFn_zero]
          rfl
        rw [hof]
        cases hx0 : x ⟨0, by omega⟩ <;> cases hx1 : x ⟨1, by omega⟩ <;> rfl
      rw [hgv, Bool.and_eq_true] at hv
      exact ⟨0, 0, h00, hv.1, hv.2⟩
  have hn2 : (2 : ℕ) ≤ n := by omega
  have hRemap : ∀ (q : Equiv.Perm (Fin n)) (M : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (n + n) M →
      ∃ M' : PEqualNP.CircuitLowerBounds.Circuit,
        M'.size = M.size ∧
        PEqualNP.TopForm.IsAO2 (n + n) M' ∧
        (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M' j).op =
          (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op) ∧
        (∀ x : Fin (n + n) → Bool,
          let y : Fin (n + n) → Bool := fun k =>
            if hk : k.val < n then x k else x (Fin.natAdd n (q ⟨k.val - n, by omega⟩))
          PEqualNP.MetaComplexity.circuitFun (n + n) M' x = PEqualNP.MetaComplexity.circuitFun (n + n) M y ∧
          ∀ j : ℕ, PEqualNP.EdgeOwnership.gateVal (n + n) M' j x = PEqualNP.EdgeOwnership.gateVal (n + n) M j y) := by
    intro q M hMAO
    let σ : ℕ → ℕ := fun w =>
      if h1 : w < n then w
      else if h2 : w < n + n then n + (q ⟨w - n, by omega⟩).val
      else w
    have hσ_lt : ∀ w k : ℕ, w < n + n + k → σ w < n + n + k := by
      intro w k hw
      dsimp only [σ]
      split_ifs with h1 h2
      · omega
      · have hq := (q ⟨w - n, by omega⟩).isLt
        omega
      · exact hw
    have hσ_ge : ∀ w : ℕ, n + n ≤ w → σ w = w := by
      intro w hw
      dsimp only [σ]
      split_ifs with h1 h2 <;> omega
    let remapGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
      fun g => ⟨g.op, g.inputs.map σ⟩
    let M' : PEqualNP.CircuitLowerBounds.Circuit := ⟨M.gates.map remapGate, σ M.output⟩
    refine ⟨M', List.length_map _, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg
        rw [List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        exact hMAO.1 g0 hg0
      · intro i hi w hw
        have hi0 : i < M.gates.length := by
          change i < (M.gates.map remapGate).length at hi
          rw [List.length_map] at hi
          exact hi
        have hget : PEqualNP.MetaComplexity.NestedCover.gateAt M' i =
            remapGate (PEqualNP.MetaComplexity.NestedCover.gateAt M i) := by
          change M'.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
            remapGate (M.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
          rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi0]
          change (M.gates.map remapGate)[i]'hi = remapGate (M.gates[i]'hi0)
          exact List.getElem_map _
        rw [hget, List.mem_map] at hw
        obtain ⟨w0, hw0, rfl⟩ := hw
        exact hσ_lt w0 i (hMAO.2.1 i hi0 w0 hw0)
      · intro g hg
        rw [List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        change (g0.inputs.map σ).length = 2
        rw [List.length_map]
        exact hMAO.2.2 g0 hg0
    · intro j hj
      have hj' : j < M'.gates.length := by
        change j < (M.gates.map remapGate).length
        rw [List.length_map]
        exact hj
      change (M'.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
        (M.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op
      rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj]
      change ((M.gates.map remapGate)[j]'hj').op = (M.gates[j]'hj).op
      rw [List.getElem_map]
    · intro x
      dsimp only
      let y : Fin (n + n) → Bool := fun k =>
        if hk : k.val < n then x k else x (Fin.natAdd n (q ⟨k.val - n, by omega⟩))
      have hbase_len : (List.ofFn x).length = n + n := List.length_ofFn
      have hbase_len_y : (List.ofFn y).length = n + n := List.length_ofFn
      have hbase_get : ∀ w : ℕ, w < n + n → (List.ofFn x).getD (σ w) Bool.false = (List.ofFn y).getD w Bool.false := by
        intro w hw
        have hsw : σ w < n + n := by
          have := hσ_lt w 0 (by omega)
          omega
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
        simp only [List.getElem_ofFn, y]
        dsimp only [σ]
        split_ifs with h1
        · rfl
        · congr 1
      have hstep : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (wx wy : List Bool),
          wx.length = wy.length →
          n + n ≤ wx.length →
          (∀ w : ℕ, w < wx.length → wx.getD (σ w) Bool.false = wy.getD w Bool.false) →
          (gs.map remapGate).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) wx =
            wx ++ ((gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) wy).drop wy.length) := by
        intro gs
        induction gs with
        | nil =>
          intro wx wy _ _ _
          simp only [List.map_nil, List.foldl_nil, List.drop_length, List.append_nil]
        | cons g rest ih =>
          intro wx wy hlen hge hagree
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
          have hrec := ih (wx ++ [b]) (wy ++ [b]) hwx1 (by simp only [List.length_append, List.length_singleton]; omega) hagree1
          have hfold_append : ∀ (gs0 : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
              ∃ tail : List Bool, gs0.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) init = init ++ tail := by
            intro gs0
            induction gs0 with
            | nil => intro init; exact ⟨[], by simp⟩
            | cons g0 rs0 ih0 =>
              intro init
              obtain ⟨t, ht⟩ := ih0 (init ++ [g0.op.eval (g0.inputs.map fun i => init.getD i Bool.false)])
              exact ⟨g0.op.eval (g0.inputs.map fun i => init.getD i Bool.false) :: t, by simpa [List.foldl_cons, List.append_assoc] using ht⟩
          obtain ⟨t, ht⟩ := hfold_append rest (wy ++ [b])
          simp only [List.map_cons, List.foldl_cons, remapGate]
          rw [heval_eq]
          change (rest.map remapGate).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (wx ++ [b]) =
            wx ++ ((rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (wy ++ [b])).drop wy.length)
          rw [hrec, ht]
          have hdrop1 : ((wy ++ [b]) ++ t).drop (wy ++ [b]).length = t := List.drop_left
          have hdrop2 : ((wy ++ [b]) ++ t).drop wy.length = [b] ++ t := by
            rw [List.append_assoc, List.drop_left]
          rw [hdrop1, hdrop2, List.append_assoc]
      have hwires : M'.wires (List.ofFn x) = List.ofFn x ++ (M.wires (List.ofFn y)).drop (n + n) := by
        have h := hstep M.gates (List.ofFn x) (List.ofFn y) (by omega) (by omega) (by simpa [hbase_len] using hbase_get)
        rw [hbase_len_y] at h
        exact h
      have hfold_append_y : ∃ tail : List Bool, M.wires (List.ofFn y) = List.ofFn y ++ tail := by
        have hfa : ∀ (gs0 : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
            ∃ tail : List Bool, gs0.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) init = init ++ tail := by
          intro gs0
          induction gs0 with
          | nil => intro init; exact ⟨[], by simp⟩
          | cons g0 rs0 ih0 =>
            intro init
            obtain ⟨t, ht⟩ := ih0 (init ++ [g0.op.eval (g0.inputs.map fun i => init.getD i Bool.false)])
            exact ⟨g0.op.eval (g0.inputs.map fun i => init.getD i Bool.false) :: t, by simpa [List.foldl_cons, List.append_assoc] using ht⟩
        exact hfa M.gates (List.ofFn y)
      obtain ⟨tail, htail⟩ := hfold_append_y
      have hdrop : (M.wires (List.ofFn y)).drop (n + n) = tail := by
        rw [htail]
        have hd : (List.ofFn y ++ tail).drop (List.ofFn y).length = tail := List.drop_left
        rwa [hbase_len_y] at hd
      rw [hdrop] at hwires
      constructor
      · change (M'.wires (List.ofFn x)).getD (σ M.output) Bool.false = (M.wires (List.ofFn y)).getD M.output Bool.false
        rw [hwires, htail]
        by_cases hout : M.output < n + n
        · have hsout : σ M.output < n + n := by
            have := hσ_lt M.output 0 (by omega)
            omega
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact hbase_get M.output hout
        · rw [hσ_ge M.output (by omega)]
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          simp only [hbase_len, hbase_len_y]
      · intro j
        change (M'.wires (List.ofFn x)).getD (n + n + j) Bool.false = (M.wires (List.ofFn y)).getD (n + n + j) Bool.false
        rw [hwires, htail]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        simp only [hbase_len, hbase_len_y]
  let E' : Finset (Fin n × Fin n) := E.image (fun e => (e.1, p.symm e.2))
  have hE'_mem : ∀ u v : Fin n, (u, v) ∈ E' ↔ (u, p v) ∈ E := by
    intro u v
    simp only [E', Finset.mem_image]
    constructor
    · rintro ⟨⟨a, b⟩, hab, heq⟩
      have h1 : a = u := (Prod.mk.inj heq).1
      have h2 : p.symm b = v := (Prod.mk.inj heq).2
      have h3 : b = p v := by rw [← h2, Equiv.apply_symm_apply]
      rw [← h1, ← h3]
      exact hab
    · intro h
      exact ⟨(u, p v), h, Prod.ext rfl (Equiv.symm_apply_apply p v)⟩
  have hmatch' : ∀ u : Fin n, (u, u) ∈ E' := fun u => (hE'_mem u u).mpr (hMatch u)
  have hc4' : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
      ¬((a, c) ∈ E' ∧ (a, d) ∈ E' ∧ (b, c) ∈ E' ∧ (b, d) ∈ E') := by
    intro a b c d hab hcd h
    exact hC4 a b (p c) (p d) hab (fun h' => hcd (p.injective h'))
      ⟨(hE'_mem _ _).mp h.1, (hE'_mem _ _).mp h.2.1, (hE'_mem _ _).mp h.2.2.1, (hE'_mem _ _).mp h.2.2.2⟩
  obtain ⟨C', hC'size, hC'AO, _, hC'eval⟩ := hRemap p.symm C hAO
  have hC'fun : ∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C' x =
      Decidable.decide (∃ u v : Fin n, (u, v) ∈ E' ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true) := by
    intro x
    have h1 := (hC'eval x).1
    rw [h1, hFun]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨u, p.symm v, (hE'_mem u (p.symm v)).mpr ?_, ?_, ?_⟩
      · rwa [Equiv.apply_symm_apply]
      · simpa only [Fin.val_castAdd, dif_pos u.isLt] using hu
      · have hnot : ¬ (Fin.natAdd n v).val < n := by simp only [Fin.val_natAdd]; omega
        rw [dif_neg hnot] at hv
        have hsub : (⟨(Fin.natAdd n v).val - n, by simp only [Fin.val_natAdd]; omega⟩ : Fin n) = v := by
          ext; simp only [Fin.val_natAdd]; omega
        simpa only [hsub] using hv
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨u, p v, (hE'_mem u v).mp huv, ?_, ?_⟩
      · simpa only [Fin.val_castAdd, dif_pos u.isLt] using hu
      · have hnot : ¬ (Fin.natAdd n (p v)).val < n := by simp only [Fin.val_natAdd]; omega
        rw [dif_neg hnot]
        have hsub : (⟨(Fin.natAdd n (p v)).val - n, by simp only [Fin.val_natAdd]; omega⟩ : Fin n) = p v := by
          ext; simp only [Fin.val_natAdd]; omega
        rw [hsub, Equiv.symm_apply_apply]
        exact hv
  obtain ⟨C1, hC1size, hC1AO, hC1fun, hC1nd, hC1dist⟩ := hIrred n E' C' hn2 hmatch' hc4' hC'AO hC'fun
  obtain ⟨D', hD'size, hD'AO, hD'same, hD'clean⟩ := hClean n E' C1 hn2 hmatch' hc4' hC1AO hC1fun hC1nd hC1dist
  obtain ⟨D, hDsize, hDAO, hDop, hDeval⟩ := hRemap p D' hD'AO
  refine ⟨D, by omega, hDAO, ?_, ?_⟩
  · intro x
    have h1 := (hDeval x).1
    rw [h1, hD'same, hC1fun, hFun x]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨u, p v, (hE'_mem u v).mp huv, ?_, ?_⟩
      · simpa only [Fin.val_castAdd, dif_pos u.isLt] using hu
      · have hnot : ¬ (Fin.natAdd n v).val < n := by simp only [Fin.val_natAdd]; omega
        rw [dif_neg hnot] at hv
        have hsub : (⟨(Fin.natAdd n v).val - n, by simp only [Fin.val_natAdd]; omega⟩ : Fin n) = v := by
          ext; simp only [Fin.val_natAdd]; omega
        simpa only [hsub] using hv
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨u, p.symm v, (hE'_mem u (p.symm v)).mpr ?_, ?_, ?_⟩
      · rwa [Equiv.apply_symm_apply]
      · simpa only [Fin.val_castAdd, dif_pos u.isLt] using hu
      · have hnot : ¬ (Fin.natAdd n (p.symm v)).val < n := by simp only [Fin.val_natAdd]; omega
        rw [dif_neg hnot]
        have hsub : (⟨(Fin.natAdd n (p.symm v)).val - n, by simp only [Fin.val_natAdd]; omega⟩ : Fin n) = p.symm v := by
          ext; simp only [Fin.val_natAdd]; omega
        rw [hsub, Equiv.apply_symm_apply]
        exact hv
  · intro j hj hop x hgv
    have hj' : j < D'.gates.length := by
      change j < D.size at hj
      change j < D'.size
      omega
    have hop' : (PEqualNP.MetaComplexity.NestedCover.gateAt D' j).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
      rw [← hDop j hj']
      exact hop
    have hgv' := (hDeval x).2 j
    rw [hgv'] at hgv
    obtain ⟨u, v, huv, hu, hv⟩ := hD'clean j hj' hop' _ hgv
    refine ⟨u, p v, (hE'_mem u v).mp huv, ?_, ?_⟩
    · simpa only [Fin.val_castAdd, dif_pos u.isLt] using hu
    · have hnot : ¬ (Fin.natAdd n v).val < n := by simp only [Fin.val_natAdd]; omega
      rw [dif_neg hnot] at hv
      have hsub : (⟨(Fin.natAdd n v).val - n, by simp only [Fin.val_natAdd]; omega⟩ : Fin n) = v := by
        ext; simp only [Fin.val_natAdd]; omega
      simpa only [hsub] using hv
