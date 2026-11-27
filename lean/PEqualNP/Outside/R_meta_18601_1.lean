import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Matching
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18601_1
    (hIrred :
      ∀ (k : ℕ) (E : Finset (Fin k × Fin k)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ k →
        (∀ u : Fin k, (u, u) ∈ E) →
        (∀ u : Fin k, (3 : ℕ) ≤ (E.filter fun e => e.1 = u).card) →
        (∀ v : Fin k, (3 : ℕ) ≤ (E.filter fun e => e.2 = v).card) →
        (∀ a b c d : Fin k, a ≠ b → c ≠ d →
          ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        ((2 : ℕ) * E.card - (3 : ℕ) * (k + k)) ^ (3 : ℕ) ≤ (k + k) ^ (2 : ℕ) →
        PEqualNP.TopForm.IsAO2 (k + k) C →
        (∀ x : Fin (k + k) → Bool, PEqualNP.MetaComplexity.circuitFun (k + k) C x =
          Decidable.decide (∃ u v : Fin k, (u, v) ∈ E ∧
            x (Fin.castAdd k u) = Bool.true ∧ x (Fin.natAdd k v) = Bool.true)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ C.size ∧
          PEqualNP.TopForm.IsAO2 (k + k) D ∧
          (∀ x : Fin (k + k) → Bool, PEqualNP.MetaComplexity.circuitFun (k + k) D x =
            Decidable.decide (∃ u v : Fin k, (u, v) ∈ E ∧
              x (Fin.castAdd k u) = Bool.true ∧ x (Fin.natAdd k v) = Bool.true)) ∧
          (∀ g ∈ D.gates, g.inputs.Nodup) ∧
          (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (k + k) → Bool,
            (D.wires (List.ofFn x)).getD (k + k + i.val) Bool.false ≠
            (D.wires (List.ofFn x)).getD (k + k + j.val) Bool.false))
    (hCover :
      ∀ (k : ℕ) (E : Finset (Fin k × Fin k)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ k →
        (∀ u : Fin k, (u, u) ∈ E) →
        (∀ u : Fin k, (3 : ℕ) ≤ (E.filter fun e => e.1 = u).card) →
        (∀ v : Fin k, (3 : ℕ) ≤ (E.filter fun e => e.2 = v).card) →
        (∀ a b c d : Fin k, a ≠ b → c ≠ d →
          ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        ((2 : ℕ) * E.card - (3 : ℕ) * (k + k)) ^ (3 : ℕ) ≤ (k + k) ^ (2 : ℕ) →
        PEqualNP.TopForm.IsAO2 (k + k) D →
        (∀ x : Fin (k + k) → Bool, PEqualNP.MetaComplexity.circuitFun (k + k) D x =
          Decidable.decide (∃ u v : Fin k, (u, v) ∈ E ∧
            x (Fin.castAdd k u) = Bool.true ∧ x (Fin.natAdd k v) = Bool.true)) →
        (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ i j : Fin D.size, i ≠ j → ∃ x : Fin (k + k) → Bool,
          (D.wires (List.ofFn x)).getD (k + k + i.val) Bool.false ≠
          (D.wires (List.ofFn x)).getD (k + k + j.val) Bool.false) →
        ∃ (L R : Finset (Fin k)),
          (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ D.size + (1 : ℕ) + (k + k).sqrt) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → PEqualNP.TopForm.NoFourCycle x2 → (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) → (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) → ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) → PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x2.edgeFinset.card + x1 / (2 : ℕ) ≤ x4.size + (1 : ℕ) + x1.sqrt := by
  classical
  intro n G _ C hBip hC4 hConn hPM hDens hAO hFun
  obtain ⟨col⟩ := hBip
  obtain ⟨M, hM⟩ := hPM
  let mate : Fin n → Fin n := fun v => Classical.choose (hM.1 (hM.2 v))
  have hmadj : ∀ v : Fin n, M.Adj v (mate v) := fun v => (Classical.choose_spec (hM.1 (hM.2 v))).1
  have hmuniq : ∀ v w : Fin n, M.Adj v w → w = mate v :=
    fun v w h => (Classical.choose_spec (hM.1 (hM.2 v))).2 w h
  have hGadj : ∀ v : Fin n, G.Adj v (mate v) := fun v => M.adj_sub (hmadj v)
  have hminv : ∀ v : Fin n, mate (mate v) = v := fun v => (hmuniq (mate v) v (hmadj v).symm).symm
  have hcol_ne : ∀ u v : Fin n, G.Adj u v → col u ≠ col v := fun u v h => col.valid h
  have hcol_mate : ∀ v : Fin n, col (mate v) ≠ col v := fun v => hcol_ne (mate v) v (hGadj v).symm
  let c0 : Finset (Fin n) := Finset.univ.filter fun v => col v = (0 : Fin 2)
  let c1 : Finset (Fin n) := Finset.univ.filter fun v => col v = (1 : Fin 2)
  have hdisj01 : Disjoint c0 c1 := by
    rw [Finset.disjoint_left]
    intro v hv0 hv1
    have h0 := (Finset.mem_filter.mp hv0).2
    have h1 := (Finset.mem_filter.mp hv1).2
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hunion01 : c0 ∪ c1 = Finset.univ := by
    ext v
    simp only [c0, c1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have hv := (col v).isLt
    have h01 : (col v).val = 0 ∨ (col v).val = 1 := by omega
    rcases h01 with h0 | h1
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h1)
  have hmate_c0 : ∀ v : Fin n, v ∈ c0 → mate v ∈ c1 := by
    intro v hv
    have h0 : col v = 0 := (Finset.mem_filter.mp hv).2
    have hne : col (mate v) ≠ 0 := by rw [← h0]; exact hcol_mate v
    simp only [c1, Finset.mem_filter, Finset.mem_univ, true_and]
    have hvlt := (col (mate v)).isLt
    have h01 : (col (mate v)).val = 0 ∨ (col (mate v)).val = 1 := by omega
    rcases h01 with hz | ho
    · exact False.elim (hne (Fin.ext hz))
    · exact Fin.ext ho
  have hmate_c1 : ∀ v : Fin n, v ∈ c1 → mate v ∈ c0 := by
    intro v hv
    have h1 : col v = 1 := (Finset.mem_filter.mp hv).2
    have hne : col (mate v) ≠ 1 := by rw [← h1]; exact hcol_mate v
    simp only [c0, Finset.mem_filter, Finset.mem_univ, true_and]
    have hvlt := (col (mate v)).isLt
    have h01 : (col (mate v)).val = 0 ∨ (col (mate v)).val = 1 := by omega
    rcases h01 with hz | ho
    · exact Fin.ext hz
    · exact False.elim (hne (Fin.ext ho))
  have hcard01 : c0.card = c1.card := by
    have hmap : c0.image mate = c1 := by
      ext w
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact hmate_c0 v hv
      · intro hw
        exact ⟨mate w, hmate_c1 w hw, hminv w⟩
    rw [← hmap]
    refine (Finset.card_image_of_injective c0 ?_).symm
    intro u v huv
    have := congrArg mate huv
    rwa [hminv u, hminv v] at this
  let k : ℕ := c0.card
  have hnk : n = k + k := by
    have h1 : (c0 ∪ c1).card = n := by
      rw [hunion01, Finset.card_univ, Fintype.card_fin]
    rw [Finset.card_union_of_disjoint hdisj01] at h1
    omega
  have hk2 : (2 : ℕ) ≤ k := by
    by_contra hlt
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with hk0 | hk1
    · have hn0 : n = 0 := by omega
      have hconn0 := hConn ∅ (by simp)
      have hne := hconn0.nonempty
      obtain ⟨⟨v, _⟩⟩ := hne
      have := v.isLt
      omega
    · have hn2 : n = 2 := by omega
      have hcardU : (Finset.univ : Finset (Fin n)).card ≤ 2 := by
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      have hconnU := hConn Finset.univ hcardU
      obtain ⟨⟨v, hv⟩⟩ := hconnU.nonempty
      exact hv (Finset.mem_univ v)
  let e0 : ↥c0 ≃ Fin k := c0.equivFin
  let fL : Fin k → Fin n := fun u => (e0.symm u).1
  let fR : Fin k → Fin n := fun v => mate (fL v)
  have hfL_c0 : ∀ u : Fin k, fL u ∈ c0 := fun u => (e0.symm u).2
  have hfR_c1 : ∀ v : Fin k, fR v ∈ c1 := fun v => hmate_c0 (fL v) (hfL_c0 v)
  have hfL_inj : Function.Injective fL := fun u1 u2 h => e0.symm.injective (Subtype.ext h)
  have hfR_inj : Function.Injective fR := by
    intro v1 v2 h
    have h1 := congrArg mate h
    simp only [fR, hminv] at h1
    exact hfL_inj h1
  have hLR_ne : ∀ u v : Fin k, fL u ≠ fR v := by
    intro u v h
    have h0 := hfL_c0 u
    have h1 := hfR_c1 v
    rw [h] at h0
    exact Finset.disjoint_left.mp hdisj01 h0 h1
  let πFun : Fin (k + k) → Fin n := Fin.addCases fL fR
  have hπ_inj : Function.Injective πFun := by
    intro x y hxy
    refine Fin.addCases (motive := fun x => πFun x = πFun y → x = y) ?_ ?_ x hxy
    · intro a
      refine Fin.addCases (motive := fun y => πFun (Fin.castAdd k a) = πFun y → Fin.castAdd k a = y) ?_ ?_ y
      · intro a' h
        simp only [πFun, Fin.addCases_left] at h
        rw [hfL_inj h]
      · intro b' h
        simp only [πFun, Fin.addCases_left, Fin.addCases_right] at h
        exact False.elim (hLR_ne a b' h)
    · intro b
      refine Fin.addCases (motive := fun y => πFun (Fin.natAdd k b) = πFun y → Fin.natAdd k b = y) ?_ ?_ y
      · intro a' h
        simp only [πFun, Fin.addCases_left, Fin.addCases_right] at h
        exact False.elim (hLR_ne a' b h.symm)
      · intro b' h
        simp only [πFun, Fin.addCases_right] at h
        rw [hfR_inj h]
  have hπ_bij : Function.Bijective πFun := by
    refine ⟨hπ_inj, ?_⟩
    intro w
    have hwU : w ∈ c0 ∪ c1 := by rw [hunion01]; exact Finset.mem_univ w
    rcases Finset.mem_union.mp hwU with h0 | h1
    · refine ⟨Fin.castAdd k (e0 ⟨w, h0⟩), ?_⟩
      simp only [πFun, Fin.addCases_left, fL, Equiv.symm_apply_apply]
    · refine ⟨Fin.natAdd k (e0 ⟨mate w, hmate_c1 w h1⟩), ?_⟩
      simp only [πFun, Fin.addCases_right, fR, fL, Equiv.symm_apply_apply, hminv]
  let π : Fin (k + k) ≃ Fin n := Equiv.ofBijective πFun hπ_bij
  have hπ_left : ∀ u : Fin k, π (Fin.castAdd k u) = fL u := fun u => by
    change πFun (Fin.castAdd k u) = fL u
    simp only [πFun, Fin.addCases_left]
  have hπ_right : ∀ v : Fin k, π (Fin.natAdd k v) = fR v := fun v => by
    change πFun (Fin.natAdd k v) = fR v
    simp only [πFun, Fin.addCases_right]
  let E : Finset (Fin k × Fin k) := Finset.univ.filter fun p => G.Adj (fL p.1) (fR p.2)
  have hE_mem : ∀ u v : Fin k, (u, v) ∈ E ↔ G.Adj (fL u) (fR v) := by
    intro u v
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
  have hE_match : ∀ u : Fin k, (u, u) ∈ E := fun u => (hE_mem u u).mpr (hGadj (fL u))
  have hE_card : E.card = G.edgeFinset.card := by
    let φ : Fin k × Fin k → Sym2 (Fin n) := fun p => s(fL p.1, fR p.2)
    have hφ_inj : Set.InjOn φ ↑E := by
      intro p1 _ p2 _ heq
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext (hfL_inj h1) (hfR_inj h2)
      · exact False.elim (hLR_ne p1.1 p2.2 h1)
    have hφ_img : E.image φ = G.edgeFinset := by
      ext e
      refine Sym2.ind (fun a b => ?_) e
      simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨p, hp, heq⟩
        have hadj := (hE_mem p.1 p.2).mp hp
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj
        · exact hadj.symm
      · intro hadj
        have hcol := hcol_ne a b hadj
        have haU : a ∈ c0 ∪ c1 := by rw [hunion01]; exact Finset.mem_univ a
        have hbU : b ∈ c0 ∪ c1 := by rw [hunion01]; exact Finset.mem_univ b
        rcases Finset.mem_union.mp haU with ha0 | ha1 <;> rcases Finset.mem_union.mp hbU with hb0 | hb1
        · exact False.elim (hcol ((Finset.mem_filter.mp ha0).2.trans (Finset.mem_filter.mp hb0).2.symm))
        · let u : Fin k := e0 ⟨a, ha0⟩
          let v : Fin k := e0 ⟨mate b, hmate_c1 b hb1⟩
          have hu : fL u = a := by simp only [fL, u, Equiv.symm_apply_apply]
          have hv : fR v = b := by simp only [fR, fL, v, Equiv.symm_apply_apply, hminv]
          refine ⟨(u, v), (hE_mem u v).mpr (by rw [hu, hv]; exact hadj), ?_⟩
          simp only [φ, hu, hv]
        · let u : Fin k := e0 ⟨b, hb0⟩
          let v : Fin k := e0 ⟨mate a, hmate_c1 a ha1⟩
          have hu : fL u = b := by simp only [fL, u, Equiv.symm_apply_apply]
          have hv : fR v = a := by simp only [fR, fL, v, Equiv.symm_apply_apply, hminv]
          refine ⟨(u, v), (hE_mem u v).mpr (by rw [hu, hv]; exact hadj.symm), ?_⟩
          dsimp only [φ]
          rw [hu, hv, Sym2.eq_swap]
        · exact False.elim (hcol ((Finset.mem_filter.mp ha1).2.trans (Finset.mem_filter.mp hb1).2.symm))
    rw [← hφ_img]
    exact (Finset.card_image_of_injOn hφ_inj).symm
  have hE_c4 : ∀ a b c d : Fin k, a ≠ b → c ≠ d →
      ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E) := by
    intro a b c d hab hcd h
    have hle := hC4 (fL a) (fL b) (fun heq => hab (hfL_inj heq))
    have hc_mem : fR c ∈ Finset.univ.filter (fun w => G.Adj (fL a) w ∧ G.Adj (fL b) w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hE_mem a c).mp h.1, (hE_mem b c).mp h.2.2.1⟩
    have hd_mem : fR d ∈ Finset.univ.filter (fun w => G.Adj (fL a) w ∧ G.Adj (fL b) w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hE_mem a d).mp h.2.1, (hE_mem b d).mp h.2.2.2⟩
    have hcd_eq := Finset.card_le_one.mp hle (fR c) hc_mem (fR d) hd_mem
    exact hcd (hfR_inj hcd_eq)
  have hDegG : ∀ v : Fin n, (3 : ℕ) ≤ (G.neighborFinset v).card := by
    intro v
    by_contra hlt
    have hle2 : (G.neighborFinset v).card ≤ 2 := by omega
    have hcv := hConn (G.neighborFinset v) hle2
    have hv_not : v ∉ (G.neighborFinset v : Set (Fin n)) := by
      simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
      exact G.loopless.irrefl v
    have hex_other : ∃ w : Fin n, w ≠ v ∧ w ∉ (G.neighborFinset v : Set (Fin n)) := by
      have hcard_lt : (insert v (G.neighborFinset v)).card < (Finset.univ : Finset (Fin n)).card := by
        have h1 : (insert v (G.neighborFinset v)).card ≤ (G.neighborFinset v).card + 1 := Finset.card_insert_le _ _
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      have hne_univ : insert v (G.neighborFinset v) ≠ Finset.univ := fun h => by rw [h] at hcard_lt; omega
      have hsub : (Finset.univ \ insert v (G.neighborFinset v)).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro hsu
        exact hne_univ (Finset.Subset.antisymm (Finset.subset_univ _) hsu)
      obtain ⟨w, hw⟩ := hsub
      rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hw
      exact ⟨w, hw.2.1, hw.2.2⟩
    obtain ⟨w, hwne, hwnot⟩ := hex_other
    obtain ⟨p⟩ := hcv ⟨v, hv_not⟩ ⟨w, hwnot⟩
    cases p with
    | nil => exact hwne rfl
    | cons hadj _ =>
      rename_i u _
      have hu_mem : u.1 ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v u.1).mpr hadj
      exact u.2 hu_mem
  have hDegL : ∀ u : Fin k, (3 : ℕ) ≤ (E.filter fun e => e.1 = u).card := by
    intro u
    have himg : (E.filter fun e => e.1 = u).image (fun e => fR e.2) = G.neighborFinset (fL u) := by
      ext w
      simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨e, ⟨he, rfl⟩, rfl⟩
        exact (hE_mem e.1 e.2).mp he
      · intro hadj
        have hcol := hcol_ne (fL u) w hadj
        have hwU : w ∈ c0 ∪ c1 := by rw [hunion01]; exact Finset.mem_univ w
        rcases Finset.mem_union.mp hwU with hw0 | hw1
        · exact False.elim (hcol ((Finset.mem_filter.mp (hfL_c0 u)).2.trans (Finset.mem_filter.mp hw0).2.symm))
        · let v : Fin k := e0 ⟨mate w, hmate_c1 w hw1⟩
          have hv : fR v = w := by simp only [fR, fL, v, Equiv.symm_apply_apply, hminv]
          exact ⟨(u, v), ⟨(hE_mem u v).mpr (by rw [hv]; exact hadj), rfl⟩, hv⟩
    have hinj : Set.InjOn (fun e : Fin k × Fin k => fR e.2) (E.filter fun e => e.1 = u) := by
      intro e1 he1 e2 he2 hEq
      have h1 : e1.1 = u := (Finset.mem_filter.mp he1).2
      have h2 : e2.1 = u := (Finset.mem_filter.mp he2).2
      exact Prod.ext (h1.trans h2.symm) (hfR_inj hEq)
    have hcard := Finset.card_image_of_injOn hinj
    rw [himg] at hcard
    rw [← hcard]
    exact hDegG (fL u)
  have hDegR : ∀ v : Fin k, (3 : ℕ) ≤ (E.filter fun e => e.2 = v).card := by
    intro v
    have himg : (E.filter fun e => e.2 = v).image (fun e => fL e.1) = G.neighborFinset (fR v) := by
      ext w
      simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨e, ⟨he, rfl⟩, rfl⟩
        exact ((hE_mem e.1 e.2).mp he).symm
      · intro hadj
        have hcol := hcol_ne (fR v) w hadj
        have hwU : w ∈ c0 ∪ c1 := by rw [hunion01]; exact Finset.mem_univ w
        rcases Finset.mem_union.mp hwU with hw0 | hw1
        · let u : Fin k := e0 ⟨w, hw0⟩
          have hu : fL u = w := by simp only [fL, u, Equiv.symm_apply_apply]
          exact ⟨(u, v), ⟨(hE_mem u v).mpr (by rw [hu]; exact hadj.symm), rfl⟩, hu⟩
        · exact False.elim (hcol ((Finset.mem_filter.mp (hfR_c1 v)).2.trans (Finset.mem_filter.mp hw1).2.symm))
    have hinj : Set.InjOn (fun e : Fin k × Fin k => fL e.1) (E.filter fun e => e.2 = v) := by
      intro e1 he1 e2 he2 hEq
      have h1 : e1.2 = v := (Finset.mem_filter.mp he1).2
      have h2 : e2.2 = v := (Finset.mem_filter.mp he2).2
      exact Prod.ext (hfL_inj hEq) (h1.trans h2.symm)
    have hcard := Finset.card_image_of_injOn hinj
    rw [himg] at hcard
    rw [← hcard]
    exact hDegG (fR v)
  let σ : ℕ → ℕ := fun w => if hw : w < n then (π.symm ⟨w, hw⟩).val else w
  have hσ_lt : ∀ w j : ℕ, w < n + j → σ w < k + k + j := by
    intro w j hw
    dsimp only [σ]
    split_ifs with h1
    · have := (π.symm ⟨w, h1⟩).isLt
      omega
    · omega
  let rg : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun g => ⟨g.op, g.inputs.map σ⟩
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map rg, σ C.output⟩
  have hC'_size : C'.size = C.size := List.length_map _
  have hAO' : PEqualNP.TopForm.IsAO2 (k + k) C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact hAO.1 g0 hg0
    · intro i hi w hw
      have hi0 : i < C.size := by
        change i < (C.gates.map rg).length at hi
        rw [List.length_map] at hi
        exact hi
      have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C' i =
          rg (PEqualNP.MetaComplexity.NestedCover.gateAt C i) := by
        change C'.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
          rg (C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
        rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi0]
        change (C.gates.map rg)[i]'hi = rg (C.gates[i]'hi0)
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
  have hfun' : ∀ x : Fin (k + k) → Bool, PEqualNP.MetaComplexity.circuitFun (k + k) C' x =
      Decidable.decide (∃ u v : Fin k, (u, v) ∈ E ∧
        x (Fin.castAdd k u) = Bool.true ∧ x (Fin.natAdd k v) = Bool.true) := by
    intro x
    let y : Fin n → Bool := fun w => x (π.symm w)
    have hbase_len : (List.ofFn x).length = k + k := List.length_ofFn
    have hbase_len_y : (List.ofFn y).length = n := List.length_ofFn
    have hbase_get : ∀ w : ℕ, w < n → (List.ofFn x).getD (σ w) Bool.false = (List.ofFn y).getD w Bool.false := by
      intro w hw
      have hsw : σ w < k + k := by
        have := hσ_lt w 0 (by omega)
        omega
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      simp only [List.getElem_ofFn, y]
      dsimp only [σ]
      simp only [hw, ↓reduceDIte]
    have hstep : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (wx wy : List Bool),
        wx.length = wy.length →
        n ≤ wx.length →
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
        have hσ_ge : ∀ w : ℕ, n ≤ w → σ w = w := by
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
              have := hσ_lt w (wx.length - n) (by omega)
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
    have hfold_prefix : ∀ (gs0 : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (j : ℕ),
        j < init.length →
        (gs0.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) init).getD j Bool.false = init.getD j Bool.false := by
      intro gs0
      induction gs0 with
      | nil => intro init j _; rfl
      | cons g0 rs0 ih0 =>
        intro init j hj
        simp only [List.foldl_cons]
        rw [ih0 _ j (by simp only [List.length_append, List.length_singleton]; omega)]
        exact List.getD_append _ _ _ _ hj
    have hwires_eq := hstep C.gates (List.ofFn x) (List.ofFn y)
      (by rw [hbase_len, hbase_len_y, hnk]) (by rw [hbase_len, hnk])
      (fun w hw => hbase_get w (by rw [hbase_len] at hw; omega))
    have hceval : PEqualNP.MetaComplexity.circuitFun (k + k) C' x = PEqualNP.MetaComplexity.circuitFun n C y := by
      change ((C.gates.map rg).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (List.ofFn x)).getD (σ C.output) Bool.false =
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (List.ofFn y)).getD C.output Bool.false
      rw [hwires_eq]
      by_cases hout : C.output < n
      · have hsout : σ C.output < (List.ofFn x).length := by
          rw [hbase_len]
          have := hσ_lt C.output 0 (by omega)
          omega
        rw [List.getD_append _ _ _ _ hsout]
        rw [hfold_prefix C.gates (List.ofFn y) C.output (by rw [hbase_len_y]; exact hout)]
        exact hbase_get C.output hout
      · have hsout : σ C.output = C.output := by
          dsimp only [σ]
          split_ifs with h1 <;> omega
        rw [hsout]
        rw [List.getD_append_right _ _ _ _ (by rw [hbase_len]; omega)]
        rw [hbase_len, hbase_len_y]
        have hleny := hfold_len C.gates (List.ofFn y)
        rw [hbase_len_y] at hleny
        by_cases hlt : C.output < n + C.gates.length
        · have h1 : C.output - (k + k) < ((C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) (List.ofFn y)).drop n).length := by
            rw [List.length_drop, hleny]
            omega
          rw [List.getD_eq_getElem _ _ h1, List.getElem_drop, List.getD_eq_getElem _ _ (by omega)]
          congr 1
          omega
        · rw [List.getD_eq_default _ _ (by rw [List.length_drop, hleny]; omega)]
          rw [List.getD_eq_default _ _ (by omega)]
    rw [hceval]
    have hCy := congrFun hFun y
    rw [hCy]
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), y a = true) ||
      decide (∃ a b : Fin n, G.Adj a b ∧ y a = true ∧ y b = true)) =
      decide (∃ u v : Fin k, (u, v) ∈ E ∧ x (Fin.castAdd k u) = true ∧ x (Fin.natAdd k v) = true)
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hadj, ha, hb⟩
      have hcol := hcol_ne a b hadj
      have haU : a ∈ c0 ∪ c1 := by rw [hunion01]; exact Finset.mem_univ a
      have hbU : b ∈ c0 ∪ c1 := by rw [hunion01]; exact Finset.mem_univ b
      rcases Finset.mem_union.mp haU with ha0 | ha1 <;> rcases Finset.mem_union.mp hbU with hb0 | hb1
      · exact False.elim (hcol ((Finset.mem_filter.mp ha0).2.trans (Finset.mem_filter.mp hb0).2.symm))
      · let u : Fin k := e0 ⟨a, ha0⟩
        let v : Fin k := e0 ⟨mate b, hmate_c1 b hb1⟩
        have hu : π (Fin.castAdd k u) = a := by rw [hπ_left]; simp only [fL, u, Equiv.symm_apply_apply]
        have hv : π (Fin.natAdd k v) = b := by rw [hπ_right]; simp only [fR, fL, v, Equiv.symm_apply_apply, hminv]
        refine ⟨u, v, (hE_mem u v).mpr (by rw [← hπ_left, ← hπ_right, hu, hv]; exact hadj), ?_, ?_⟩
        · simpa only [y, ← hu, Equiv.symm_apply_apply] using ha
        · simpa only [y, ← hv, Equiv.symm_apply_apply] using hb
      · let u : Fin k := e0 ⟨b, hb0⟩
        let v : Fin k := e0 ⟨mate a, hmate_c1 a ha1⟩
        have hu : π (Fin.castAdd k u) = b := by rw [hπ_left]; simp only [fL, u, Equiv.symm_apply_apply]
        have hv : π (Fin.natAdd k v) = a := by rw [hπ_right]; simp only [fR, fL, v, Equiv.symm_apply_apply, hminv]
        refine ⟨u, v, (hE_mem u v).mpr (by rw [← hπ_left, ← hπ_right, hu, hv]; exact hadj.symm), ?_, ?_⟩
        · simpa only [y, ← hu, Equiv.symm_apply_apply] using hb
        · simpa only [y, ← hv, Equiv.symm_apply_apply] using ha
      · exact False.elim (hcol ((Finset.mem_filter.mp ha1).2.trans (Finset.mem_filter.mp hb1).2.symm))
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨fL u, fR v, (hE_mem u v).mp huv, ?_, ?_⟩
      · simpa only [y, ← hπ_left, Equiv.symm_apply_apply] using hu
      · simpa only [y, ← hπ_right, Equiv.symm_apply_apply] using hv
  have hDens' : ((2 : ℕ) * E.card - (3 : ℕ) * (k + k)) ^ (3 : ℕ) ≤ (k + k) ^ (2 : ℕ) := by
    rw [hE_card, ← hnk]
    exact hDens
  obtain ⟨D, hDle, hDAO, hDfun, hDnd, hDdist⟩ :=
    hIrred k E C' hk2 hE_match hDegL hDegR hE_c4 hDens' hAO' hfun'
  obtain ⟨L, R, hcov, hcard⟩ :=
    hCover k E D hk2 hE_match hDegL hDegR hE_c4 hDens' hDAO hDfun hDnd hDdist
  have hLR : k ≤ L.card + R.card := by
    have hunion : (Finset.univ : Finset (Fin k)) ⊆ L ∪ R := by
      intro u _
      exact Finset.mem_union.mpr (hcov (u, u) (hE_match u))
    have h1 : k ≤ (L ∪ R).card := by
      have := Finset.card_le_card hunion
      simpa only [Finset.card_univ, Fintype.card_fin] using this
    exact le_trans h1 (Finset.card_union_le L R)
  rw [← hE_card, ← hC'_size, hnk]
  omega
