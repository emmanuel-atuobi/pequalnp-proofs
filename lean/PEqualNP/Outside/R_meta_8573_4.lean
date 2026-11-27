import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8573_4
    (hIrred :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (3 : ℕ) ≤ n →
        (∀ u : Fin n, (u, u) ∈ E) →
        (∀ u : Fin n, (∃ v : Fin n, v ≠ u ∧ (u, v) ∈ E) ∧ (∃ v : Fin n, v ≠ u ∧ (v, u) ∈ E)) →
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
    (hCover :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        (3 : ℕ) ≤ n →
        (∀ u : Fin n, (u, u) ∈ E) →
        (∀ u : Fin n, (∃ v : Fin n, v ≠ u ∧ (u, v) ∈ E) ∧ (∃ v : Fin n, v ≠ u ∧ (v, u) ∈ E)) →
        (∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + n) D →
        (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x =
          Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (n + n) → Bool,
          PEqualNP.EdgeOwnership.gateVal (n + n) D i.val x ≠
          PEqualNP.EdgeOwnership.gateVal (n + n) D j.val x) →
        ∃ (L R : Finset (Fin n)), (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : SimpleGraph (Fin (x1 + x1))) [x5 : DecidableRel x4.Adj] (x6 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (∀ (x8 x9 x10 x11 : Fin x1), x8 ≠ x9 → x10 ≠ x11 → ¬((x8, x10) ∈ x2 ∧ (x8, x11) ∈ x2 ∧ (x9, x10) ∈ x2 ∧ (x9, x11) ∈ x2)) → (∀ (x9 : Fin x1), (x9, x3 x9) ∈ x2) → ((∀ (x10 : Fin x1), ∃ (x11 : Fin x1), x11 ≠ x3 x10 ∧ (x10, x11) ∈ x2) ∧ ∀ (x10 : Fin x1), ∃ (x11 : Fin x1), x3 x11 ≠ x10 ∧ (x11, x10) ∈ x2) → (∀ (x11 x12 : Fin (x1 + x1)), x4.Adj x11 x12 ↔ ∃ (x13 : Fin x1) (x14 : Fin x1), (x13, x14) ∈ x2 ∧ (x11 = Fin.castAdd x1 x13 ∧ x12 = Fin.natAdd x1 x14 ∨ x12 = Fin.castAdd x1 x13 ∧ x11 = Fin.natAdd x1 x14)) → PEqualNP.TopForm.IsLeastAO x4 x6 → PEqualNP.TopForm.TopForm x4 x6 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x4 x6).card → x2.card + x1 ≤ x6.size + (1 : ℕ) := by
  classical
  intro n E p G _x5 C hdense hC4 hMatch hExtra hG hLeast _hTF _hJunk
  have hn_pos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have hE0 : E = ∅ := Finset.eq_empty_of_forall_notMem fun e _ => Fin.elim0 e.1
    rw [hE0, Finset.card_empty] at hdense
    omega
  have hn_ne1 : n ≠ 1 := by
    intro h1
    subst h1
    obtain ⟨j, hjne, _⟩ := hExtra.1 0
    exact hjne (Subsingleton.elim j (p 0))
  have hn_ne2 : n ≠ 2 := by
    intro h2
    subst h2
    let a0 : Fin 2 := ⟨0, by omega⟩
    let a1 : Fin 2 := ⟨1, by omega⟩
    let b0 : Fin 2 := ⟨0, by omega⟩
    let b1 : Fin 2 := ⟨1, by omega⟩
    have hfin2 : ∀ r : Fin 2, r = b0 ∨ r = b1 := by
      intro r
      rcases Nat.lt_succ_iff_lt_or_eq.mp r.isLt with hlt | heq
      · left; ext; simp only [b0]; omega
      · right; ext; simp only [b1]; omega
    have hall : ∀ a : Fin 2, (a, b0) ∈ E ∧ (a, b1) ∈ E := by
      intro a
      obtain ⟨r2, hrne, hr2⟩ := hExtra.1 a
      have hr1 := hMatch a
      rcases hfin2 (p a) with hp0 | hp1
      · rcases hfin2 r2 with r20 | r21
        · exact absurd (r20.trans hp0.symm) hrne
        · rw [hp0] at hr1; rw [r21] at hr2; exact ⟨hr1, hr2⟩
      · rcases hfin2 r2 with r20 | r21
        · rw [hp1] at hr1; rw [r20] at hr2; exact ⟨hr2, hr1⟩
        · exact absurd (r21.trans hp1.symm) hrne
    have h0 := hall a0
    have h1 := hall a1
    have hneA : a0 ≠ a1 := by intro h; have := congrArg Fin.val h; simp only [a0, a1] at this; omega
    have hneB : b0 ≠ b1 := by intro h; have := congrArg Fin.val h; simp only [b0, b1] at this; omega
    exact hC4 a0 a1 b0 b1 hneA hneB ⟨h0.1, h0.2, h1.1, h1.2⟩
  have hn3 : (3 : ℕ) ≤ n := by omega
  have hAO : PEqualNP.TopForm.IsAO2 (n + n) C := hLeast.1
  have hFun : ∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) C x =
      Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true) := by
    intro x
    have hgf := congrFun hLeast.2.1 x
    rw [hgf]
    change (Decidable.decide (∃ a ∈ (∅ : Finset (Fin (n + n))), x a = Bool.true) ||
      Decidable.decide (∃ u v : Fin (n + n), G.Adj u v ∧ x u = Bool.true ∧ x v = Bool.true)) =
      Decidable.decide (∃ u v : Fin n, (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, false_or]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨a, b, hab, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (hG u v).mp huv
      · exact ⟨a, b, hab, hu, hv⟩
      · exact ⟨a, b, hab, hv, hu⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨Fin.castAdd n a, Fin.natAdd n b, (hG _ _).mpr ⟨a, b, hab, Or.inl ⟨rfl, rfl⟩⟩, ha, hb⟩
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
  have hmatch' : ∀ u : Fin n, (u, u) ∈ E' := fun u => (hE'_mem u u).mpr (hMatch u)
  have hc4' : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
      ¬((a, c) ∈ E' ∧ (a, d) ∈ E' ∧ (b, c) ∈ E' ∧ (b, d) ∈ E') := by
    intro a b c d hab hcd h
    exact hC4 a b (p c) (p d) hab (fun h' => hcd (p.injective h'))
      ⟨(hE'_mem _ _).mp h.1, (hE'_mem _ _).mp h.2.1, (hE'_mem _ _).mp h.2.2.1, (hE'_mem _ _).mp h.2.2.2⟩
  have hDeg2' : ∀ u : Fin n, (∃ v : Fin n, v ≠ u ∧ (u, v) ∈ E') ∧ (∃ v : Fin n, v ≠ u ∧ (v, u) ∈ E') := by
    intro u
    constructor
    · obtain ⟨w, hwne, hwe⟩ := hExtra.1 u
      refine ⟨p.symm w, fun heq => hwne ?_, (hE'_mem u (p.symm w)).mpr (by rwa [Equiv.apply_symm_apply])⟩
      rw [← Equiv.apply_symm_apply p w, heq]
    · obtain ⟨w, hwne, hwe⟩ := hExtra.2 (p u)
      refine ⟨w, fun heq => hwne (by rw [heq]), (hE'_mem w u).mpr hwe⟩
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
  have hσ_ge : ∀ w : ℕ, n + n ≤ w → σ w = w := by
    intro w hw
    dsimp only [σ]
    split_ifs with h1 h2 <;> omega
  let remapGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun g => ⟨g.op, g.inputs.map σ⟩
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map remapGate, σ C.output⟩
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
        change C'.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
          remapGate (C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
        rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi0]
        change (C.gates.map remapGate)[i]'hi = remapGate (C.gates[i]'hi0)
        exact List.getElem_map _
      rw [hget, List.mem_map] at hw
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
    have hwires : C'.wires (List.ofFn x) = List.ofFn x ++ (C.wires (List.ofFn y)).drop (n + n) := by
      have h := hstep C.gates (List.ofFn x) (List.ofFn y) (by omega) (by omega) (by simpa [hbase_len] using hbase_get)
      rw [hbase_len_y] at h
      exact h
    have hfold_append_y : ∃ tail : List Bool, C.wires (List.ofFn y) = List.ofFn y ++ tail := by
      have hfa : ∀ (gs0 : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
          ∃ tail : List Bool, gs0.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) init = init ++ tail := by
        intro gs0
        induction gs0 with
        | nil => intro init; exact ⟨[], by simp⟩
        | cons g0 rs0 ih0 =>
          intro init
          obtain ⟨t, ht⟩ := ih0 (init ++ [g0.op.eval (g0.inputs.map fun i => init.getD i Bool.false)])
          exact ⟨g0.op.eval (g0.inputs.map fun i => init.getD i Bool.false) :: t, by simpa [List.foldl_cons, List.append_assoc] using ht⟩
      exact hfa C.gates (List.ofFn y)
    obtain ⟨tail, htail⟩ := hfold_append_y
    have hdrop : (C.wires (List.ofFn y)).drop (n + n) = tail := by
      rw [htail]
      have hd : (List.ofFn y ++ tail).drop (List.ofFn y).length = tail := List.drop_left
      rwa [hbase_len_y] at hd
    rw [hdrop] at hwires
    have heval : PEqualNP.MetaComplexity.circuitFun (n + n) C' x = PEqualNP.MetaComplexity.circuitFun (n + n) C y := by
      change (C'.wires (List.ofFn x)).getD (σ C.output) Bool.false = (C.wires (List.ofFn y)).getD C.output Bool.false
      rw [hwires, htail]
      by_cases hout : C.output < n + n
      · have hsout : σ C.output < n + n := by
          have := hσ_lt C.output 0 (by omega)
          omega
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hbase_get C.output hout
      · rw [hσ_ge C.output (by omega)]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        simp only [hbase_len, hbase_len_y]
    rw [heval, hFun y, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨u, p.symm v, (hE'_mem u (p.symm v)).mpr ?_, ?_, ?_⟩
      · rwa [Equiv.apply_symm_apply]
      · simpa only [y, Fin.val_castAdd, dif_pos u.isLt] using hu
      · have hnot : ¬ (Fin.natAdd n v).val < n := by simp only [Fin.val_natAdd]; omega
        dsimp only [y] at hv
        rw [dif_neg hnot] at hv
        have hsub : (⟨(Fin.natAdd n v).val - n, by simp only [Fin.val_natAdd]; omega⟩ : Fin n) = v := by
          ext; simp only [Fin.val_natAdd]; omega
        simpa only [hsub] using hv
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨u, p v, (hE'_mem u v).mp huv, ?_, ?_⟩
      · simpa only [y, Fin.val_castAdd, dif_pos u.isLt] using hu
      · have hnot : ¬ (Fin.natAdd n (p v)).val < n := by simp only [Fin.val_natAdd]; omega
        dsimp only [y]
        rw [dif_neg hnot]
        have hsub : (⟨(Fin.natAdd n (p v)).val - n, by simp only [Fin.val_natAdd]; omega⟩ : Fin n) = p v := by
          ext; simp only [Fin.val_natAdd]; omega
        rw [hsub, Equiv.symm_apply_apply]
        exact hv
  obtain ⟨D, hDle, hDAO, hDfun, hDnd, hDdist⟩ := hIrred n E' C' hn3 hmatch' hDeg2' hc4' hAO' hfun'
  obtain ⟨L, R, hCov, hBd⟩ := hCover n E' D hn3 hmatch' hDeg2' hc4' hDAO hDfun hDnd hDdist
  have hKonig : n ≤ L.card + R.card := by
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ L ∪ R := by
      intro u _
      exact Finset.mem_union.mpr (hCov (u, u) (hmatch' u))
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact le_trans h1 (Finset.card_union_le L R)
  omega
