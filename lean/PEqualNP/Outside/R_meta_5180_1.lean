import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5180_1
    (hOutAnd :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        (200 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
        ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) →
        x2 + x2 ≤ x4.output →
        x4.output < x2 + x2 + x4.size →
        x2 + x2 ≤ a ∧ a < x4.output ∧ x2 + x2 ≤ b ∧ b < x4.output →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (x2 + x2))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (x2 + x2))).inputs = [a, b] →
        (∀ (l : Fin x2), ∀ p ∈ x3 l,
          PEqualNP.CircuitLowerBounds.wireValue x4 (List.ofFn (PEqualNP.ReadK.setInput ({Fin.castAdd x2 p, Fin.natAdd x2 l} : Finset (Fin (x2 + x2))))) a = Bool.true ∧
          PEqualNP.CircuitLowerBounds.wireValue x4 (List.ofFn (PEqualNP.ReadK.setInput ({Fin.castAdd x2 p, Fin.natAdd x2 l} : Finset (Fin (x2 + x2))))) b = Bool.true) →
        (∀ (x12 : Finset (Fin (x2 + x2))), List.countP (fun (x13 : Fin x2) => Decidable.decide (Fin.natAdd x2 x13 ∈ x12)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x12 ↔ ∃ (x14 : Fin x2) (x15 : Fin x2), x14 ∈ x3 x15 ∧ x12 = {Fin.castAdd x2 x14, Fin.natAdd x2 x15})) →
        x2 * x1 ≤ (100 : ℕ) * x4.size)
    (hOutOr :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        (200 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
        ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) →
        x2 + x2 ≤ x4.output →
        x4.output < x2 + x2 + x4.size →
        x2 + x2 ≤ a ∧ a < x4.output ∧ x2 + x2 ≤ b ∧ b < x4.output →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (x2 + x2))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x4.output - (x2 + x2))).inputs = [a, b] →
        (∀ (x : Fin (x2 + x2)),
          PEqualNP.CircuitLowerBounds.wireValue x4 (List.ofFn (PEqualNP.ReadK.setInput ({x} : Finset (Fin (x2 + x2))))) a = Bool.false ∧
          PEqualNP.CircuitLowerBounds.wireValue x4 (List.ofFn (PEqualNP.ReadK.setInput ({x} : Finset (Fin (x2 + x2))))) b = Bool.false) →
        (∀ (x12 : Finset (Fin (x2 + x2))), List.countP (fun (x13 : Fin x2) => Decidable.decide (Fin.natAdd x2 x13 ∈ x12)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x12 ↔ ∃ (x14 : Fin x2) (x15 : Fin x2), x14 ∈ x3 x15 ∧ x12 = {Fin.castAdd x2 x14, Fin.natAdd x2 x15})) →
        x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → (∀ (x12 : Finset (Fin (x2 + x2))), List.countP (fun (x13 : Fin x2) => Decidable.decide (Fin.natAdd x2 x13 ∈ x12)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x12 ↔ ∃ (x14 : Fin x2) (x15 : Fin x2), x14 ∈ x3 x15 ∧ x12 = {Fin.castAdd x2 x14, Fin.natAdd x2 x15})) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q N L C hq hN hLcard hProj hAO hNotRK houtLt hPI
  have hN2 : 2 ≤ N := by
    have hq2 : 1 ≤ q ^ 2 := by
      have : 1 * 1 ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
      simpa only [sq] using this
    rw [hN]
    omega
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) init).length =
      init.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro init; simp
    | cons hd tl ih =>
      intro init
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [List.length_append, List.length_singleton]
      omega
  have hfold_pref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (j : ℕ),
      j < init.length →
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) init).getD j false =
      init.getD j false := by
    intro gs
    induction gs with
    | nil => intro init j _; rfl
    | cons hd tl ih =>
      intro init j hj
      simp only [List.foldl_cons]
      rw [ih _ j (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ hj
  have hWireLt : ∀ (S : Finset (Fin (N + N))) (j : ℕ) (hj : j < N + N),
      PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.ReadK.setInput S)) j =
      decide ((⟨j, hj⟩ : Fin (N + N)) ∈ S) := by
    intro S j hj
    have h1 := hfold_pref C.gates (List.ofFn (PEqualNP.ReadK.setInput S)) j (by simp only [List.length_ofFn]; exact hj)
    change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)])
      (List.ofFn (PEqualNP.ReadK.setInput S))).getD j false = _
    rw [h1, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hj), List.getElem_ofFn]
    rfl
  have hCountNodup : ∀ (l : Fin N) (xs : List (Fin N)), xs.Nodup →
      List.countP (fun l' : Fin N => decide (l' = l)) xs ≤ 1 := by
    intro l xs
    induction xs with
    | nil => intro _; simp
    | cons hd tl ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      rw [List.countP_cons]
      by_cases h : hd = l
      · have hzero : List.countP (fun l' : Fin N => decide (l' = l)) tl = 0 := by
          rw [List.countP_eq_zero]
          intro x hx
          simp only [decide_eq_true_eq]
          intro hxl
          exact hnd.1 (h ▸ hxl ▸ hx)
        rw [hzero]
        simp [h]
      · simp only [h, decide_false]
        exact ih hnd.2
  have hIncPI : ∀ (l : Fin N), ∀ p ∈ L l,
      PEqualNP.ReadK.IsPrimeImplicant (N + N) C ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) := by
    intro l p hp
    have hcnt : List.countP (fun l' : Fin N =>
        Decidable.decide (Fin.natAdd N l' ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N)))))
        (List.finRange N) ≤ q := by
      have hcongr : List.countP (fun l' : Fin N =>
          Decidable.decide (Fin.natAdd N l' ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N)))))
          (List.finRange N) =
          List.countP (fun l' : Fin N => decide (l' = l)) (List.finRange N) := by
        apply List.countP_congr
        intro l' _
        have hiff : Fin.natAdd N l' ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ↔ l' = l := by
          constructor
          · intro hm
            rcases Finset.mem_insert.mp hm with h1 | h2
            · have hv := congrArg Fin.val h1
              simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
              omega
            · have h2' := Finset.mem_singleton.mp h2
              have hv := congrArg Fin.val h2'
              simp only [Fin.val_natAdd] at hv
              exact Fin.ext (by omega)
          · intro heq
            rw [heq]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [decide_eq_true_eq]
        exact hiff
      rw [hcongr]
      have h1 := hCountNodup l (List.finRange N) (List.nodup_finRange N)
      omega
    exact (hPI {Fin.castAdd N p, Fin.natAdd N l} hcnt).mpr ⟨p, l, hp, rfl⟩
  have hRejSingle : ∀ (x : Fin (N + N)),
      PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.ReadK.setInput ({x} : Finset (Fin (N + N))))) C.output = Bool.false := by
    intro x
    by_cases hx : x.val < N
    · let p : Fin N := ⟨x.val, hx⟩
      have hxp : x = Fin.castAdd N p := Fin.ext rfl
      let p' : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hne : p ≠ p' := by
        intro heq
        have hv := congrArg Fin.val heq
        by_cases h0 : p.val = 0
        · simp only [p', h0, ↓reduceIte] at hv; omega
        · exact h0 (by simpa only [p', h0, ↓reduceIte] using hv)
      obtain ⟨l, ⟨hp, _⟩, _⟩ := hProj p p' hne
      have hss : ({x} : Finset (Fin (N + N))) ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))).ssubsets := by
        rw [Finset.mem_ssubsets, Finset.ssubset_iff_subset_ne, hxp]
        refine ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _), ?_⟩
        intro heq
        have hm : Fin.natAdd N l ∈ ({Fin.castAdd N p} : Finset (Fin (N + N))) := by
          rw [heq]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hv := congrArg Fin.val (Finset.mem_singleton.mp hm)
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      exact (hIncPI l p hp).2 {x} hss
    · let l : Fin N := ⟨x.val - N, by omega⟩
      have hxl : x = Fin.natAdd N l := Fin.ext (by change x.val = N + (x.val - N); omega)
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [hLcard l]; omega)
      have hss : ({x} : Finset (Fin (N + N))) ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))).ssubsets := by
        rw [Finset.mem_ssubsets, Finset.ssubset_iff_subset_ne, hxl]
        refine ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
        intro heq
        have hm : Fin.castAdd N p ∈ ({Fin.natAdd N l} : Finset (Fin (N + N))) := by
          rw [heq]
          exact Finset.mem_insert_self _ _
        have hv := congrArg Fin.val (Finset.mem_singleton.mp hm)
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      exact (hIncPI l p hp).2 {x} hss
  have hRejGe : ∀ w : ℕ,
      (∀ x : Fin (N + N), PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.ReadK.setInput ({x} : Finset (Fin (N + N))))) w = Bool.false) →
      N + N ≤ w := by
    intro w hw
    by_contra hlt
    have hlt : w < N + N := Nat.lt_of_not_ge hlt
    let x0 : Fin (N + N) := ⟨w, hlt⟩
    have hf := hw x0
    rw [hWireLt {x0} w hlt] at hf
    have heq : (⟨w, hlt⟩ : Fin (N + N)) = x0 := rfl
    rw [heq] at hf
    simp at hf
  have hAccGe : ∀ w : ℕ,
      (∀ (l : Fin N), ∀ p ∈ L l, PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.ReadK.setInput ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))))) w = Bool.true) →
      N + N ≤ w := by
    intro w hw
    by_contra hlt
    have hlt : w < N + N := Nat.lt_of_not_ge hlt
    by_cases hwN : w < N
    · let p0 : Fin N := ⟨w, hwN⟩
      let l0 : Fin N := ⟨0, by omega⟩
      have hsub : L l0 ⊆ {p0} := by
        intro p hp
        have ht := hw l0 p hp
        rw [hWireLt _ w hlt] at ht
        simp only [decide_eq_true_eq] at ht
        rcases Finset.mem_insert.mp ht with h1 | h2
        · have hv := congrArg Fin.val h1
          simp only [Fin.val_castAdd] at hv
          exact Finset.mem_singleton.mpr (Fin.ext hv.symm)
        · have hv := congrArg Fin.val (Finset.mem_singleton.mp h2)
          simp only [Fin.val_natAdd] at hv
          omega
      have hc1 := Finset.card_le_card hsub
      simp only [Finset.card_singleton, hLcard l0] at hc1
      omega
    · let l0 : Fin N := ⟨w - N, by omega⟩
      let l1 : Fin N := if l0.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hne : l1 ≠ l0 := by
        intro heq
        have hv := congrArg Fin.val heq
        by_cases h0 : l0.val = 0
        · simp only [l1, h0, ↓reduceIte] at hv; omega
        · exact h0 (by simpa only [l1, h0, ↓reduceIte] using hv.symm)
      obtain ⟨p1, hp1⟩ := Finset.card_pos.mp (by rw [hLcard l1]; omega)
      have ht := hw l1 p1 hp1
      rw [hWireLt _ w hlt] at ht
      simp only [decide_eq_true_eq] at ht
      rcases Finset.mem_insert.mp ht with h1 | h2
      · have hv := congrArg Fin.val h1
        simp only [Fin.val_castAdd] at hv
        omega
      · have hv := congrArg Fin.val (Finset.mem_singleton.mp h2)
        simp only [Fin.val_natAdd] at hv
        exact hne (Fin.ext (by change l1.val = w - N; omega))
  have houtGe : N + N ≤ C.output := hRejGe C.output hRejSingle
  let k : ℕ := C.output - (N + N)
  have hk_lt : k < C.gates.length := by change C.output - (N + N) < C.size; omega
  let g0 : PEqualNP.CircuitLowerBounds.Gate := C.gates[k]'hk_lt
  have hga0 : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g0 := by
    change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g0
    rw [List.getD_eq_getElem _ _ hk_lt]
  have hg0_mem : g0 ∈ C.gates := List.getElem_mem hk_lt
  have hlen2 : g0.inputs.length = 2 := hAO.2.2 g0 hg0_mem
  cases hinp : g0.inputs with
  | nil => rw [hinp] at hlen2; simp at hlen2
  | cons a rest =>
    cases rest with
    | nil => rw [hinp] at hlen2; simp at hlen2
    | cons b tail =>
      cases tail with
      | cons _ _ => rw [hinp] at hlen2; simp at hlen2
      | nil =>
        have ha_lt : a < C.output := by
          have h1 := hAO.2.1 k hk_lt a (by rw [hga0, hinp]; simp)
          omega
        have hb_lt : b < C.output := by
          have h1 := hAO.2.1 k hk_lt b (by rw [hga0, hinp]; simp)
          omega
        have hEvalOut : ∀ x : List Bool, x.length = N + N →
            PEqualNP.CircuitLowerBounds.wireValue C x C.output =
            g0.op.eval [PEqualNP.CircuitLowerBounds.wireValue C x a, PEqualNP.CircuitLowerBounds.wireValue C x b] := by
          intro x hxlen
          have hsplit : C.gates = C.gates.take k ++ g0 :: C.gates.drop (k + 1) := by
            have h1 := (List.take_append_drop k C.gates).symm
            have h2 : C.gates.drop k = g0 :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk_lt
            rw [h2] at h1
            exact h1
          let w0 := (C.gates.take k).foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) x
          have hw0_len : w0.length = C.output := by
            have h1 := hfold_len (C.gates.take k) x
            rw [hxlen, List.length_take, Nat.min_eq_left (le_of_lt hk_lt)] at h1
            change w0.length = N + N + k at h1
            omega
          let bval := g0.op.eval (g0.inputs.map fun i => w0.getD i false)
          have hw_eq : C.wires x = (C.gates.drop (k + 1)).foldl
              (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (w0 ++ [bval]) := by
            change C.gates.foldl _ x = _
            conv_lhs => rw [hsplit]
            rw [List.foldl_append, List.foldl_cons]
          have hw_out : (C.wires x).getD C.output false = bval := by
            rw [hw_eq, hfold_pref _ _ C.output (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
            rw [List.getD_append_right _ _ _ _ (by omega)]
            simp only [hw0_len, Nat.sub_self, List.getD_cons_zero]
          have hw_a : (C.wires x).getD a false = w0.getD a false := by
            rw [hw_eq, hfold_pref _ _ a (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
            exact List.getD_append _ _ _ _ (by omega)
          have hw_b : (C.wires x).getD b false = w0.getD b false := by
            rw [hw_eq, hfold_pref _ _ b (by simp only [List.length_append, List.length_singleton, hw0_len]; omega)]
            exact List.getD_append _ _ _ _ (by omega)
          change (C.wires x).getD C.output false = g0.op.eval [(C.wires x).getD a false, (C.wires x).getD b false]
          rw [hw_out, hw_a, hw_b]
          dsimp only [bval]
          rw [hinp, List.map_cons, List.map_cons, List.map_nil]
        have hga_inp : (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [a, b] := by
          rw [hga0, hinp]
        rcases hAO.1 g0 hg0_mem with hAnd | hOr
        · have hAndEval : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [u, v] = (u && v) := by
            intro u v; cases u <;> cases v <;> rfl
          have hAccAB : ∀ (l : Fin N), ∀ p ∈ L l,
              PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.ReadK.setInput ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))))) a = Bool.true ∧
              PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.ReadK.setInput ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))))) b = Bool.true := by
            intro l p hp
            have h1 := (hIncPI l p hp).1
            change PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.ReadK.setInput ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))))) C.output = true at h1
            rw [hEvalOut _ (by simp only [List.length_ofFn]), hAnd, hAndEval, Bool.and_eq_true] at h1
            exact h1
          have haGe : N + N ≤ a := hAccGe a (fun l p hp => (hAccAB l p hp).1)
          have hbGe : N + N ≤ b := hAccGe b (fun l p hp => (hAccAB l p hp).2)
          exact hOutAnd q N L C a b hq hN hLcard hProj hAO hNotRK houtGe houtLt ⟨haGe, ha_lt, hbGe, hb_lt⟩
            (by rw [hga0]; exact hAnd) hga_inp hAccAB hPI
        · have hOrEval : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [u, v] = (u || v) := by
            intro u v; cases u <;> cases v <;> rfl
          have hRejAB : ∀ x : Fin (N + N),
              PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.ReadK.setInput ({x} : Finset (Fin (N + N))))) a = Bool.false ∧
              PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.ReadK.setInput ({x} : Finset (Fin (N + N))))) b = Bool.false := by
            intro x
            have h1 := hRejSingle x
            rw [hEvalOut _ (by simp only [List.length_ofFn]), hOr, hOrEval, Bool.or_eq_false_iff] at h1
            exact h1
          have haGe : N + N ≤ a := hRejGe a (fun x => (hRejAB x).1)
          have hbGe : N + N ≤ b := hRejGe b (fun x => (hRejAB x).2)
          exact hOutOr q N L C a b hq hN hLcard hProj hAO hNotRK houtGe houtLt ⟨haGe, ha_lt, hbGe, hb_lt⟩
            (by rw [hga0]; exact hOr) hga_inp hRejAB hPI
