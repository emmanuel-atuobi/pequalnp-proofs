import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17381_3
    (hFirstInter :
      have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];
      have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ));
      ∀ (x3 : List (Finset (Fin (285 : ℕ)))) (a b : Finset (Fin (285 : ℕ))),
        (2 : ℕ) ≤ x3.length →
        (a ∈ x2 ∧ b ∈ x2 ∧ ¬a ⊆ b ∧ ¬b ⊆ a ∧ x3.getD (0 : ℕ) ∅ ∉ x2 ∧ x3.getD (0 : ℕ) ∅ = a ∩ b) →
        (∀ (x4 : Fin x3.length),
          have x5 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x4) x3;
          ∃ x6 ∈ x5, ∃ x7 ∈ x5, ¬x6 ⊆ x7 ∧ ¬x7 ⊆ x6 ∧ x3.get x4 ∉ x5 ∧ (x3.get x4 = x6 ∩ x7 ∨ x3.get x4 = x6 ∪ x7)) →
        (∃ x5 ∈ x3, ∃ x6 ∈ x3, ¬x5 ⊆ x6 ∧ ¬x6 ⊆ x5 ∧ x5 ∩ x6 = (List.filter (fun (x7 : Fin (285 : ℕ)) => Decidable.decide (↑x7 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) →
        ∃ (x6 : Fin (12 : ℕ) → ℕ), Function.Injective x6 ∧ ∀ (x7 : Fin (12 : ℕ)), x6 x7 < x3.length ∧ ¬∃ x8 ∈ x2 ++ List.take (x6 x7) x3, ∃ x9 ∈ x2 ++ List.take (x6 x7) x3, ¬x8 ⊆ x9 ∧ ¬x9 ⊆ x8 ∧ x3.getD (x6 x7) ∅ = x8 ∪ x9)
    (hFirstUnion :
      have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];
      have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ));
      ∀ (x3 : List (Finset (Fin (285 : ℕ)))) (a b : Finset (Fin (285 : ℕ))),
        (2 : ℕ) ≤ x3.length →
        (a ∈ x2 ∧ b ∈ x2 ∧ ¬a ⊆ b ∧ ¬b ⊆ a ∧ x3.getD (0 : ℕ) ∅ ∉ x2 ∧ x3.getD (0 : ℕ) ∅ = a ∪ b) →
        (∀ (x4 : Fin x3.length),
          have x5 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x4) x3;
          ∃ x6 ∈ x5, ∃ x7 ∈ x5, ¬x6 ⊆ x7 ∧ ¬x7 ⊆ x6 ∧ x3.get x4 ∉ x5 ∧ (x3.get x4 = x6 ∩ x7 ∨ x3.get x4 = x6 ∪ x7)) →
        (∃ x5 ∈ x3, ∃ x6 ∈ x3, ¬x5 ⊆ x6 ∧ ¬x6 ⊆ x5 ∧ x5 ∩ x6 = (List.filter (fun (x7 : Fin (285 : ℕ)) => Decidable.decide (↑x7 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) →
        ∃ (x6 : Fin (12 : ℕ) → ℕ), Function.Injective x6 ∧ ∀ (x7 : Fin (12 : ℕ)), x6 x7 < x3.length ∧ ¬∃ x8 ∈ x2 ++ List.take (x6 x7) x3, ∃ x9 ∈ x2 ++ List.take (x6 x7) x3, ¬x8 ⊆ x9 ∧ ¬x9 ⊆ x8 ∧ x3.getD (x6 x7) ∅ = x8 ∪ x9) :
    have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))),   (∀ (x4 : Fin x3.length),       have x5 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x4) x3;       ∃ x6 ∈ x5, ∃ x7 ∈ x5, ¬x6 ⊆ x7 ∧ ¬x7 ⊆ x6 ∧ x3.get x4 ∉ x5 ∧ (x3.get x4 = x6 ∩ x7 ∨ x3.get x4 = x6 ∪ x7)) →     (∃ x5 ∈ x2 ++ x3, ∃ x6 ∈ x2 ++ x3, ¬x5 ⊆ x6 ∧ ¬x6 ⊆ x5 ∧ x5 ∩ x6 = (List.filter (fun (x7 : Fin (285 : ℕ)) => Decidable.decide (↑x7 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) → ∃ (x6 : Fin (12 : ℕ) → ℕ), Function.Injective x6 ∧ ∀ (x7 : Fin (12 : ℕ)), x6 x7 < x3.length ∧ ¬∃ x8 ∈ x2 ++ List.take (x6 x7) x3, ∃ x9 ∈ x2 ++ List.take (x6 x7) x3, ¬x8 ⊆ x9 ∧ ¬x9 ⊆ x8 ∧ x3.getD (x6 x7) ∅ = x8 ∪ x9 := by
  intro x1 x2 x3 hValid hTarget
  have hBitDisj : ∀ k : Fin 26,
      ¬(((8193 : ℕ).testBit ((k : ℕ) / 13 * 13 + ((k : ℕ) + 13 - 1) % 13) = true) ∧
        ((8193 : ℕ).testBit ((k : ℕ) / 13 * 13 + ((k : ℕ) + 13 - 2) % 13) = true)) := by
    decide
  have hNotBoth01 : ∀ s ∈ x2, ¬((0 : Fin 285) ∈ s ∧ (1 : Fin 285) ∈ s) := by
    intro s hs h01
    obtain ⟨k, hkR, hks⟩ := List.mem_map.mp hs
    have hk : k < 26 := List.mem_range.mp hkR
    rw [← hks] at h01
    have h0 := (List.mem_filter.mp (List.mem_toFinset.mp h01.1)).2
    have h1 := (List.mem_filter.mp (List.mem_toFinset.mp h01.2)).2
    exact hBitDisj ⟨k, hk⟩ ⟨h0, h1⟩
  let T : Finset (Fin 285) := (List.filter (fun (x7 : Fin 285) => Decidable.decide (↑x7 < 51)) (List.finRange 285)).toFinset
  have h0T : (0 : Fin 285) ∈ T :=
    List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_finRange 0, by decide⟩)
  have h1T : (1 : Fin 285) ∈ T :=
    List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_finRange 1, by decide⟩)
  obtain ⟨u, huApp, v, hvApp, hnuv, hnvu, huvT⟩ := hTarget
  have hu01 : (0 : Fin 285) ∈ u ∧ (1 : Fin 285) ∈ u := by
    have h0' : (0 : Fin 285) ∈ u ∩ v := huvT.symm ▸ h0T
    have h1' : (1 : Fin 285) ∈ u ∩ v := huvT.symm ▸ h1T
    exact ⟨(Finset.mem_inter.mp h0').1, (Finset.mem_inter.mp h1').1⟩
  have hv01 : (0 : Fin 285) ∈ v ∧ (1 : Fin 285) ∈ v := by
    have h0' : (0 : Fin 285) ∈ u ∩ v := huvT.symm ▸ h0T
    have h1' : (1 : Fin 285) ∈ u ∩ v := huvT.symm ▸ h1T
    exact ⟨(Finset.mem_inter.mp h0').2, (Finset.mem_inter.mp h1').2⟩
  have hu3 : u ∈ x3 := by
    rcases List.mem_append.mp huApp with hu2 | hu3
    · exact False.elim (hNotBoth01 u hu2 hu01)
    · exact hu3
  have hv3 : v ∈ x3 := by
    rcases List.mem_append.mp hvApp with hv2 | hv3
    · exact False.elim (hNotBoth01 v hv2 hv01)
    · exact hv3
  have huvNe : u ≠ v := fun heq => hnuv (heq ▸ Finset.Subset.refl v)
  have hLen2 : 2 ≤ x3.length := by
    rcases x3 with _ | ⟨e0, t⟩
    · cases hu3
    · rcases t with _ | ⟨e1, r⟩
      · rcases List.mem_cons.mp hu3 with rfl | hu'
        · rcases List.mem_cons.mp hv3 with rfl | hv'
          · exact False.elim (huvNe rfl)
          · cases hv'
        · cases hu'
      · simp only [List.length_cons]
        omega
  have h0lt : 0 < x3.length := by omega
  have h0Valid := hValid ⟨0, h0lt⟩
  have hPre0 : x2 ++ List.take (0 : ℕ) x3 = x2 := by
    rw [List.take_zero, List.append_nil]
  have hGet0 : x3.get ⟨0, h0lt⟩ = x3.getD 0 ∅ := by
    rw [List.getD_eq_getElem _ _ h0lt]
    rfl
  obtain ⟨a, ha, b, hb, hnab, hnba, hnotIn, hOp⟩ := h0Valid
  rw [hPre0] at ha hb hnotIn
  rw [hGet0] at hnotIn hOp
  have hTarget3 : ∃ x5 ∈ x3, ∃ x6 ∈ x3, ¬x5 ⊆ x6 ∧ ¬x6 ⊆ x5 ∧ x5 ∩ x6 = T :=
    ⟨u, hu3, v, hv3, hnuv, hnvu, huvT⟩
  rcases hOp with hInter | hUnion
  · exact hFirstInter x3 a b hLen2 ⟨ha, hb, hnab, hnba, hnotIn, hInter⟩ hValid hTarget3
  · exact hFirstUnion x3 a b hLen2 ⟨ha, hb, hnab, hnba, hnotIn, hUnion⟩ hValid hTarget3
