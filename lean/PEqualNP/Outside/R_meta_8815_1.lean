import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8815_1
    (hIrred :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (0 : ℕ) < n →
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
            (D.wires (List.ofFn x)).getD (n + n + i.val) Bool.false ≠
            (D.wires (List.ofFn x)).getD (n + n + j.val) Bool.false))
    (hCover :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        (0 : ℕ) < n →
        (∀ u : Fin n, (u, u) ∈ E) →
        (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + n) D →
        (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x =
          Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (n + n) → Bool,
          (D.wires (List.ofFn x)).getD (n + n + i.val) Bool.false ≠
          (D.wires (List.ofFn x)).getD (n + n + j.val) Bool.false) →
        ∃ (L R : Finset (Fin n)), (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) →       (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) →         PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →           (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) →             have x10 : List ℕ := x4.output :: List.flatMap (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs) x4.gates;             x2.card ≤ x1 + (x10.length - x10.toFinset.card) := by
  classical
  intro n E p C hpos hc4 hmatch hAO hfun
  let E' : Finset (Fin n × Fin n) := E.image (fun e => (e.1, p.symm e.2))
  have hE'_card : E'.card = E.card := by
    apply Finset.card_image_of_injective
    intro e1 e2 heq
    exact Prod.ext (Prod.mk.inj heq).1 (p.symm.injective (Prod.mk.inj heq).2)
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
  have hmatch' : ∀ u : Fin n, (u, u) ∈ E' := fun u => (hE'_mem u u).mpr (hmatch u)
  have hc4' : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
      ¬((a, c) ∈ E' ∧ (a, d) ∈ E' ∧ (b, c) ∈ E' ∧ (b, d) ∈ E') := by
    intro a b c d hab hcd h
    exact hc4 a b (p c) (p d) hab (fun h' => hcd (p.injective h'))
      ⟨(hE'_mem _ _).mp h.1, (hE'_mem _ _).mp h.2.1, (hE'_mem _ _).mp h.2.2.1, (hE'_mem _ _).mp h.2.2.2⟩
  let σ : ℕ → ℕ := fun w =>
    if h1 : w < n then w
    else if h2 : w < n + n then n + (p.symm ⟨w - n, by omega⟩).val
    else w
  have hσ_lt : ∀ w k : ℕ, w < n + n + k → σ w < n + n + k := by
    intro w k hw
    dsimp only [σ]
    split_ifs with h1 h2
    · omega
    · have hp := (p.symm ⟨w - n, by omega⟩).isLt
      omega
    · exact hw
  let remapGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun g => ⟨g.op, g.inputs.map σ⟩
  let C' : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map remapGate, σ C.output⟩
  have hC'_size : C'.size = C.size := List.length_map _
  have hAO' : PEqualNP.TopForm.IsAO2 (n + n) C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact hAO.1 g0 hg0
    · intro i hi w hw
      have hi0 : i < C.size := by
        change i < (C.gates.map remapGate).length at hi
        rw [List.length_map] at hi
        exact hi
      have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C' i =
          remapGate (PEqualNP.MetaComplexity.NestedCover.gateAt C i) := by
        have hlen' : i < C'.gates.length := hi
        have hlen0 : i < C.gates.length := hi0
        change C'.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
          remapGate (C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
        rw [List.getD_eq_getElem _ _ hlen', List.getD_eq_getElem _ _ hlen0]
        change (C.gates.map remapGate)[i]'hlen' = remapGate (C.gates[i]'hlen0)
        exact List.getElem_map _
      rw [hget] at hw
      rw [List.mem_map] at hw
      obtain ⟨w0, hw0, rfl⟩ := hw
      exact hσ_lt w0 i (hAO.2.1 i hi0 w0 hw0)
    · intro g hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      change (g0.inputs.map σ).length = 2
      rw [List.length_map]
      exact hAO.2.2 g0 hg0
  have hfun' : ∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C' x =
      Decidable.decide (∃ u v : Fin n, (u, v) ∈ E' ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true) := by
    intro x
    let y : Fin (n + n) → Bool := fun k =>
      if hk : k.val < n then x k
      else x (Fin.natAdd n (p.symm ⟨k.val - n, by omega⟩))
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
        have hσ_ge : ∀ w : ℕ, n + n ≤ w → σ w = w := by
          intro w hw
          dsimp only [σ]
          split_ifs with h1 h2 <;> omega
        have heval_eq : g.op.eval ((g.inputs.map σ).map fun i => wx.getD i Bool.false) =
            g.op.eval (g.inputs.map fun i => wy.getD i Bool.false) := by
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro w _
          by_cases hw : w < wx.length
          · exact hagree w hw
          · have hwnn : n + n ≤ w := by omega
            rw [Function.comp_apply, hσ_ge w hwnn]
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
    have hwires_eq := hstep C.gates (List.ofFn x) (List.ofFn y) (by rw [hbase_len, hbase_len_y]) (by rw [hbase_len])
      (fun w hw => hbase_get w (by rw [hbase_len] at hw; exact hw))
    have hceval : PEqualNP.MetaComplexity.circuitFun (n + n) C' x = PEqualNP.MetaComplexity.circuitFun (n + n) C y := by
      change (C'.wires (List.ofFn x)).getD C'.output Bool.false = (C.wires (List.ofFn y)).getD C.output Bool.false
      change ((C.gates.map remapGate).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (List.ofFn x)).getD (σ C.output) Bool.false =
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (List.ofFn y)).getD C.output Bool.false
      rw [hwires_eq]
      by_cases hout : C.output < n + n
      · have hsout : σ C.output < (List.ofFn x).length := by
          rw [hbase_len]
          have := hσ_lt C.output 0 (by omega)
          omega
        rw [List.getD_append _ _ _ _ hsout]
        rw [hfold_prefix C.gates (List.ofFn y) C.output (by rw [hbase_len_y]; exact hout)]
        exact hbase_get C.output hout
      · have hsout : σ C.output = C.output := by
          dsimp only [σ]
          split_ifs with h1 h2 <;> omega
        rw [hsout]
        rw [List.getD_append_right _ _ _ _ (by rw [hbase_len]; omega)]
        rw [hbase_len, hbase_len_y]
        have hleny := hfold_len C.gates (List.ofFn y)
        rw [hbase_len_y] at hleny
        by_cases hlt : C.output < n + n + C.gates.length
        · have h1 : C.output - (n + n) < ((C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (List.ofFn y)).drop (n + n)).length := by
            rw [List.length_drop, hleny]
            omega
          rw [List.getD_eq_getElem _ _ h1, List.getElem_drop, List.getD_eq_getElem _ _ (by omega)]
          congr 1
          omega
        · rw [List.getD_eq_default _ _ (by rw [List.length_drop, hleny]; omega)]
          rw [List.getD_eq_default _ _ (by omega)]
    rw [hceval, hfun y]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨u, p.symm v, (hE'_mem u (p.symm v)).mpr (by simpa only [Equiv.apply_symm_apply] using huv), ?_, ?_⟩
      · simpa only [y, Fin.val_castAdd, u.isLt, ↓reduceDIte] using hu
      · have hnotlt : ¬ (Fin.natAdd n v).val < n := by simp only [Fin.val_natAdd]; omega
        have hsub : (⟨(Fin.natAdd n v).val - n, by simp only [Fin.val_natAdd]; omega⟩ : Fin n) = v := by
          apply Fin.ext
          simp only [Fin.val_natAdd]
          omega
        simpa only [y, hnotlt, ↓reduceDIte, hsub] using hv
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨u, p v, (hE'_mem u v).mp huv, ?_, ?_⟩
      · simpa only [y, Fin.val_castAdd, u.isLt, ↓reduceDIte] using hu
      · have hnotlt : ¬ (Fin.natAdd n (p v)).val < n := by simp only [Fin.val_natAdd]; omega
        have hsub : (⟨(Fin.natAdd n (p v)).val - n, by simp only [Fin.val_natAdd]; omega⟩ : Fin n) = p v := by
          apply Fin.ext
          simp only [Fin.val_natAdd]
          omega
        simpa only [y, hnotlt, ↓reduceDIte, hsub, Equiv.symm_apply_apply] using hv
  obtain ⟨D, hDle, hDAO, hDfun, hDnd, hDdist⟩ := hIrred n E' C' hpos hmatch' hc4' hAO' hfun'
  obtain ⟨L, R, hcov, hcard⟩ := hCover n E' D hpos hmatch' hc4' hDAO hDfun hDnd hDdist
  have hLR : n ≤ L.card + R.card := by
    have hunion : (Finset.univ : Finset (Fin n)) ⊆ L ∪ R := by
      intro u _
      exact Finset.mem_union.mpr (hcov (u, u) (hmatch' u))
    have h1 : n ≤ (L ∪ R).card := by
      have := Finset.card_le_card hunion
      simpa only [Finset.card_univ, Fintype.card_fin] using this
    exact le_trans h1 (Finset.card_union_le L R)
  have hSizeLB : E.card + n ≤ C.size + 1 := by
    rw [← hE'_card, ← hC'_size]
    omega
  have hflat : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.inputs.length = 2) →
      (gs.flatMap (fun g => g.inputs)).length = 2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; rfl
    | cons g gs ih =>
      intro hg
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 : g.inputs.length = 2 := hg g List.mem_cons_self
      have h2 := ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      omega
  have hfold_c : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).length =
        init.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro init; rfl
    | cons g gs ih =>
      intro init
      change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)])).length =
        init.length + (gs.length + 1)
      rw [ih, List.length_append]
      change init.length + 1 + gs.length = init.length + (gs.length + 1)
      omega
  have hout_lt : C.output < n + n + C.size := by
    let v0 : Fin n := ⟨0, hpos⟩
    let f : Fin (n + n) → Bool := fun i => decide (i = Fin.castAdd n v0 ∨ i = Fin.natAdd n (p v0))
    have htrue : PEqualNP.MetaComplexity.circuitFun (n + n) C f = true := by
      rw [hfun f, decide_eq_true_eq]
      exact ⟨v0, p v0, hmatch v0, by simp [f], by simp [f]⟩
    have hget : (C.wires (List.ofFn f)).getD C.output false = true := htrue
    have hwlen : (C.wires (List.ofFn f)).length = n + n + C.size := by
      change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn f)).length = n + n + C.gates.length
      rw [hfold_c, List.length_ofFn]
    by_contra hge
    have hle : (C.wires (List.ofFn f)).length ≤ C.output := by omega
    rw [List.getD_eq_default _ _ hle] at hget
    cases hget
  let refs : List ℕ := C.output :: List.flatMap (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs) C.gates
  have hrefs_len : refs.length = 2 * C.size + 1 := by
    change (List.flatMap (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs) C.gates).length + 1 =
      2 * C.gates.length + 1
    rw [hflat C.gates hAO.2.2]
  have hrefs_sub : refs.toFinset ⊆ Finset.range (n + n + C.size) := by
    intro w hw
    rw [Finset.mem_range]
    rw [List.mem_toFinset] at hw
    rcases List.mem_cons.mp hw with rfl | hfm
    · exact hout_lt
    · rw [List.mem_flatMap] at hfm
      rcases hfm with ⟨g, hg, hwg⟩
      rw [List.mem_iff_getElem] at hg
      rcases hg with ⟨j, hj, rfl⟩
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j]'hj :=
        List.getD_eq_getElem C.gates ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ hj
      have hwj : w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs := by
        rw [hga]; exact hwg
      have hlt : w < (n + n) + j := hAO.2.1 j hj w hwj
      have hj' : j < C.size := hj
      omega
  have hrefs_card : refs.toFinset.card ≤ n + n + C.size := by
    have := Finset.card_le_card hrefs_sub
    rwa [Finset.card_range] at this
  change E.card ≤ n + (refs.length - refs.toFinset.card)
  omega
