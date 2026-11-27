import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Bitwise
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25879

open Finset Polynomial

theorem exists_irred_poly (m : ℕ) (hm : 0 < m) :
    ∃ P : Polynomial (ZMod 2), P.Monic ∧ Irreducible P ∧ P.natDegree = m := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) (GaloisField 2 m)
  have hint : IsIntegral (ZMod 2) α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  have h1 : Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2) ({α} : Set (GaloisField 2 m))) =
      (minpoly (ZMod 2) α).natDegree := IntermediateField.adjoin.finrank hint
  have h2 : Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2) ({α} : Set (GaloisField 2 m))) =
      Module.finrank (ZMod 2) (GaloisField 2 m) := by
    rw [hα]
    exact IntermediateField.finrank_top'
  have h3 : Module.finrank (ZMod 2) (GaloisField 2 m) = m := GaloisField.finrank 2 hm0
  omega

theorem sum_pow_two_eq (m : ℕ) : (∑ i : Fin m, 2 ^ i.val) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    omega

theorem sum_bool_pow_two_lt (m : ℕ) (f : Fin m → Bool) :
    (∑ i : Fin m, if f i then 2 ^ i.val else 0) < 2 ^ m := by
  have hle : (∑ i : Fin m, if f i then 2 ^ i.val else 0) ≤ ∑ i : Fin m, 2 ^ i.val :=
    Finset.sum_le_sum fun i _ => by
      by_cases h : f i = true
      · simp [h]
      · simp [h]
  have hs := sum_pow_two_eq m
  omega

theorem testBit_add_two_pow {a m j : ℕ} (ha : a < 2 ^ m) :
    (a + 2 ^ m).testBit j = if j = m then true else a.testBit j := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  by_cases hjm : j = m
  · subst hjm
    simp only [↓reduceIte]
    have hpos : 0 < 2 ^ j := Nat.pow_pos (by omega)
    have hdiv : (a + 2 ^ j) / 2 ^ j = 1 := by
      rw [Nat.add_div_right _ hpos, Nat.div_eq_of_lt ha]
    rw [hdiv]
    decide
  · simp only [hjm, ↓reduceIte]
    by_cases hlt : j < m
    · have hpow : 2 ^ m = 2 ^ j * 2 ^ (m - j) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]
      have hpos : 0 < 2 ^ j := Nat.pow_pos (by omega)
      have hdiv : (a + 2 ^ m) / 2 ^ j = a / 2 ^ j + 2 ^ (m - j) := by
        rw [hpow, Nat.mul_comm, Nat.add_mul_div_right _ _ hpos]
      have heven : 2 ^ (m - j) % 2 = 0 := by
        have hsub : m - j = (m - j - 1) + 1 := by omega
        rw [hsub, Nat.pow_succ]
        exact Nat.mul_mod_left _ 2
      rw [hdiv]
      congr 1
      rw [Nat.add_mod, heven, Nat.add_zero, Nat.mod_mod]
    · have hgt : m + 1 ≤ j := by omega
      have hpow : 2 ^ (m + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hgt
      have h2m : a + 2 ^ m < 2 ^ (m + 1) := by
        have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
        omega
      have h1 : (a + 2 ^ m) / 2 ^ j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le h2m hpow)
      have h2 : a / 2 ^ j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le (by omega) hpow)
      rw [h1, h2]

theorem testBit_add_mul_two_pow {a b m j : ℕ} (ha : a < 2 ^ m) :
    (a + 2 ^ m * b).testBit j = if j < m then a.testBit j else b.testBit (j - m) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  by_cases hlt : j < m
  · simp only [hlt, ↓reduceIte]
    have hpow : 2 ^ m = 2 ^ j * 2 ^ (m - j) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]
    have hpos : 0 < 2 ^ j := Nat.pow_pos (by omega)
    have hdiv : (a + 2 ^ m * b) / 2 ^ j = a / 2 ^ j + 2 ^ (m - j) * b := by
      rw [hpow, Nat.mul_assoc, Nat.mul_comm (2 ^ j), Nat.add_mul_div_right _ _ hpos]
    have heven : (2 ^ (m - j) * b) % 2 = 0 := by
      have hsub : m - j = (m - j - 1) + 1 := by omega
      rw [hsub, Nat.pow_succ, Nat.mul_right_comm]
      exact Nat.mul_mod_left _ 2
    rw [hdiv]
    congr 1
    rw [Nat.add_mod, heven, Nat.add_zero, Nat.mod_mod]
  · simp only [hlt, ↓reduceIte]
    have hge : m ≤ j := by omega
    have hpow : 2 ^ j = 2 ^ m * 2 ^ (j - m) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
    have hpos : 0 < 2 ^ m := Nat.pow_pos (by omega)
    have hdiv : (a + 2 ^ m * b) / 2 ^ j = b / 2 ^ (j - m) := by
      rw [hpow, ← Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ m), Nat.add_mul_div_right _ _ hpos,
        Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [hdiv]

theorem sum_pow_two_testBit (m : ℕ) (f : Fin m → Bool) (j : ℕ) :
    (∑ i : Fin m, if f i then 2 ^ i.val else 0).testBit j =
      if hj : j < m then f ⟨j, hj⟩ else false := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hlt := sum_bool_pow_two_lt m (fun i => f i.castSucc)
    by_cases hlast : f (Fin.last m) = true
    · simp only [hlast, ↓reduceIte]
      rw [testBit_add_two_pow hlt, ih (fun i => f i.castSucc) j]
      by_cases hjm : j = m
      · subst hjm
        simp only [↓reduceIte, Nat.lt_succ_self, ↓reduceDIte]
        exact hlast.symm
      · simp only [hjm, ↓reduceIte]
        by_cases hj : j < m
        · have hj' : j < m + 1 := by omega
          simp [hj, hj']
        · have hj' : ¬ j < m + 1 := by omega
          simp [hj, hj']
    · have hfalse : f (Fin.last m) = false := Bool.eq_false_iff.mpr hlast
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [ih (fun i => f i.castSucc) j]
      by_cases hj : j < m
      · have hj' : j < m + 1 := by omega
        simp [hj, hj']
      · by_cases hjm : j = m
        · subst hjm
          simp only [lt_irrefl, ↓reduceDIte, Nat.lt_succ_self]
          exact hfalse.symm
        · have hj' : ¬ j < m + 1 := by omega
          simp [hj, hj']

noncomputable def toPoly (m u : ℕ) : Polynomial (ZMod 2) :=
  ∑ i : Fin m, if u.testBit i.val then Polynomial.X ^ i.val else 0

noncomputable def polyToNat (m : ℕ) (q : Polynomial (ZMod 2)) : ℕ :=
  ∑ i : Fin m, if q.coeff i.val = 1 then 2 ^ i.val else 0

theorem toPoly_coeff (m u j : ℕ) :
    (toPoly m u).coeff j = if j < m ∧ u.testBit j then 1 else 0 := by
  classical
  unfold toPoly
  change (Polynomial.lcoeff (ZMod 2) j) _ = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply]
  by_cases hj : j < m
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · by_cases hb : u.testBit j
      · simp [hj, hb, Polynomial.coeff_X_pow]
      · simp [hj, hb]
    · intro i _ hi
      have hne : j ≠ i.val := fun h => hi (Fin.ext h.symm)
      split_ifs
      · simp [Polynomial.coeff_X_pow, hne]
      · simp
    · intro h; exact absurd (mem_univ _) h
  · simp only [hj, false_and, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro i _
    have hne : j ≠ i.val := fun h => hj (h ▸ i.isLt)
    split_ifs
    · simp [Polynomial.coeff_X_pow, hne]
    · simp

theorem toPoly_xor (m u v : ℕ) :
    toPoly m (u ^^^ v) = toPoly m u + toPoly m v := by
  ext j
  rw [Polynomial.coeff_add, toPoly_coeff, toPoly_coeff, toPoly_coeff, Nat.testBit_xor]
  by_cases hj : j < m
  · cases hu : u.testBit j <;> cases hv : v.testBit j <;> simp [hj]
    decide
  · simp [hj]

theorem polyToNat_lt (m : ℕ) (q : Polynomial (ZMod 2)) : polyToNat m q < 2 ^ m := by
  classical
  have h := sum_bool_pow_two_lt m (fun i : Fin m => decide (q.coeff i.val = 1))
  convert h using 1
  unfold polyToNat
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : q.coeff i.val = 1 <;> simp [h1]

theorem polyToNat_testBit (m : ℕ) (q : Polynomial (ZMod 2)) (j : ℕ) :
    (polyToNat m q).testBit j = if j < m then decide (q.coeff j = 1) else false := by
  classical
  have h := sum_pow_two_testBit m (fun i : Fin m => decide (q.coeff i.val = 1)) j
  have heq : polyToNat m q = ∑ i : Fin m, if decide (q.coeff i.val = 1) = true then 2 ^ i.val else 0 := by
    unfold polyToNat
    apply Finset.sum_congr rfl
    intro i _
    by_cases h1 : q.coeff i.val = 1 <;> simp [h1]
  rw [heq, h]
  by_cases hj : j < m <;> simp [hj]

theorem toPoly_polyToNat {m : ℕ} {q : Polynomial (ZMod 2)} (hq : ∀ j, m ≤ j → q.coeff j = 0) :
    toPoly m (polyToNat m q) = q := by
  ext j
  rw [toPoly_coeff, polyToNat_testBit]
  by_cases hj : j < m
  · simp only [hj, ↓reduceIte, true_and, decide_eq_true_eq]
    have hz : q.coeff j = 0 ∨ q.coeff j = 1 := by
      have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      exact h2 (q.coeff j)
    rcases hz with h0 | h1
    · rw [h0]; decide
    · simp [h1]
  · simp only [hj, false_and, ↓reduceIte]
    exact (hq j (by omega)).symm

theorem eq_of_toPoly_eq {m u v : ℕ} (hu : u < 2 ^ m) (hv : v < 2 ^ m)
    (h : toPoly m u = toPoly m v) : u = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < m
  · have hc : (toPoly m u).coeff j = (toPoly m v).coeff j := congrArg (fun p => p.coeff j) h
    rw [toPoly_coeff, toPoly_coeff] at hc
    cases h1 : u.testBit j <;> cases h2 : v.testBit j
    · rfl
    · simp [hj, h1, h2] at hc
    · simp [hj, h1, h2] at hc
    · rfl
  · have h1 : u.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by omega) (by omega)))
    have h2 : v.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1, h2]

theorem toPoly_degree_lt (m u : ℕ) : (toPoly m u).degree < (m : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro j hj
  rw [toPoly_coeff]
  have : ¬ j < m := by omega
  simp [this]

noncomputable def cubeNat (m : ℕ) (P : Polynomial (ZMod 2)) (u : ℕ) : ℕ :=
  polyToNat m ((toPoly m u ^ 3) %ₘ P)

theorem cubeNat_lt (m : ℕ) (P : Polynomial (ZMod 2)) (u : ℕ) : cubeNat m P u < 2 ^ m :=
  polyToNat_lt m _

noncomputable def gammaSet (m : ℕ) (P : Polynomial (ZMod 2)) : Finset ℕ :=
  (Finset.range (2 ^ m)).image (fun u => u + 2 ^ m * cubeNat m P u)

theorem gammaSet_subset (m k : ℕ) (P : Polynomial (ZMod 2)) (hmk : 2 * m ≤ k) :
    gammaSet m P ⊆ Finset.range (2 ^ k) := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
  rw [Finset.mem_range] at hu ⊢
  have hc := cubeNat_lt m P u
  have h1 : u + 2 ^ m * cubeNat m P u < 2 ^ m * 2 ^ m := by
    have : 2 ^ m * (cubeNat m P u + 1) ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_left _ (by omega)
    linarith
  have h2 : 2 ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [← Nat.pow_add]; ring_nf
  have h3 : 2 ^ (2 * m) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hmk
  omega

theorem gammaSet_card (m : ℕ) (P : Polynomial (ZMod 2)) : (gammaSet m P).card = 2 ^ m := by
  unfold gammaSet
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro u hu v hv heq
  rw [Finset.mem_coe, Finset.mem_range] at hu hv
  have hmod := congrArg (· % 2 ^ m) heq
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at hmod
  exact hmod

theorem gammaSet_autocorr (m : ℕ) (_hm : 0 < m)
    (P : Polynomial (ZMod 2)) (hPm : P.Monic) (hPi : Irreducible P) (hPd : P.natDegree = m)
    (d : ℕ) (hd : d ≠ 0) :
    ((gammaSet m P).filter (fun z => z ^^^ d ∈ gammaSet m P)).card ≤ 2 := by
  classical
  have : Fact (Irreducible P) := ⟨hPi⟩
  let K := AdjoinRoot P
  let φ : Polynomial (ZMod 2) →+* K := AdjoinRoot.mk P
  have hφ_inj : ∀ u v : ℕ, u < 2 ^ m → v < 2 ^ m → φ (toPoly m u) = φ (toPoly m v) → u = v := by
    intro u v hu hv heq
    have hdvd : P ∣ toPoly m u - toPoly m v := AdjoinRoot.mk_eq_mk.mp heq
    have hdeg : (toPoly m u - toPoly m v).degree < P.degree := by
      rw [Polynomial.degree_eq_natDegree hPm.ne_zero, hPd]
      exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt (toPoly_degree_lt m u) (toPoly_degree_lt m v))
    have hzero : toPoly m u - toPoly m v = 0 := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg
    exact eq_of_toPoly_eq hu hv (sub_eq_zero.mp hzero)
  have hφ_cube : ∀ u : ℕ, φ (toPoly m (cubeNat m P u)) = (φ (toPoly m u)) ^ 3 := by
    intro u
    unfold cubeNat
    have hdeg : ((toPoly m u ^ 3) %ₘ P).degree < (m : WithBot ℕ) := by
      have := Polynomial.degree_modByMonic_lt (toPoly m u ^ 3) hPm
      rwa [Polynomial.degree_eq_natDegree hPm.ne_zero, hPd] at this
    have hcoeff : ∀ j, m ≤ j → ((toPoly m u ^ 3) %ₘ P).coeff j = 0 := by
      intro j hj
      exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by exact_mod_cast hj))
    rw [toPoly_polyToNat hcoeff]
    have hdiv := Polynomial.modByMonic_add_div (toPoly m u ^ 3) P
    have hmk0 : φ P = 0 := AdjoinRoot.mk_self
    have h1 : φ ((toPoly m u ^ 3) %ₘ P + P * ((toPoly m u ^ 3) /ₘ P)) = φ (toPoly m u ^ 3) :=
      congrArg φ hdiv
    rw [map_add, map_mul, hmk0, zero_mul, add_zero, map_pow] at h1
    exact h1
  let dlo := d % 2 ^ m
  let dhi := (d / 2 ^ m) % 2 ^ m
  let dtop := d / 2 ^ (2 * m)
  have h2m_pos : 0 < 2 ^ m := Nat.pow_pos (by omega)
  by_cases htop : dtop ≠ 0
  · have hemp : ((gammaSet m P).filter (fun z => z ^^^ d ∈ gammaSet m P)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z hz hmem
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hmem
      rw [Finset.mem_range] at hu hv
      have hlt1 : u + 2 ^ m * cubeNat m P u < 2 ^ (2 * m) := by
        have hc := cubeNat_lt m P u
        have hsq : 2 ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [← Nat.pow_add]; ring_nf
        nlinarith
      have hlt2 : v + 2 ^ m * cubeNat m P v < 2 ^ (2 * m) := by
        have hc := cubeNat_lt m P v
        have hsq : 2 ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [← Nat.pow_add]; ring_nf
        nlinarith
      have hge : 2 ^ (2 * m) ≤ d := by
        by_contra hlt
        push Not at hlt
        exact htop (Nat.div_eq_of_lt hlt)
      obtain ⟨j, hjge, hjd⟩ : ∃ j, 2 * m ≤ j ∧ d.testBit j = true := by
        have hne : d / 2 ^ (2 * m) ≠ 0 := htop
        have hex : ∃ r, (d / 2 ^ (2 * m)).testBit r = true := by
          by_contra hall
          push Not at hall
          apply hne
          apply Nat.eq_of_testBit_eq
          intro r
          rw [Nat.zero_testBit]
          exact Bool.eq_false_iff.mpr (hall r)
        obtain ⟨r, hr⟩ := hex
        refine ⟨2 * m + r, by omega, ?_⟩
        rw [Nat.testBit_eq_decide_div_mod_eq] at hr ⊢
        rwa [Nat.pow_add, ← Nat.div_div_eq_div_mul]
      have hbit := congrArg (fun n => n.testBit j) heq
      rw [Nat.testBit_xor,
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right (by omega) hjge)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt2 (Nat.pow_le_pow_right (by omega) hjge)),
        hjd] at hbit
      simp at hbit
    rw [hemp, Finset.card_empty]
    omega
  · push Not at htop
    have hd_lt : d < 2 ^ (2 * m) := by
      by_contra hge
      push Not at hge
      have : 0 < d / 2 ^ (2 * m) := Nat.div_pos hge (Nat.pow_pos (by omega))
      omega
    have hd_eq : d = dlo + 2 ^ m * dhi := by
      have h1 : d = d % 2 ^ m + 2 ^ m * (d / 2 ^ m) := by
        have := Nat.div_add_mod d (2 ^ m); omega
      have h2 : d / 2 ^ m < 2 ^ m := by
        rw [Nat.div_lt_iff_lt_mul h2m_pos]
        have hsq : 2 ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [← Nat.pow_add]; ring_nf
        omega
      rw [show dlo = d % 2 ^ m from rfl, show dhi = (d / 2 ^ m) % 2 ^ m from rfl,
        Nat.mod_eq_of_lt h2]
      exact h1
    have hdlo_lt : dlo < 2 ^ m := Nat.mod_lt d h2m_pos
    have hdhi_lt : dhi < 2 ^ m := Nat.mod_lt _ h2m_pos
    let a : K := φ (toPoly m dlo)
    let b : K := φ (toPoly m dhi)
    have hchar2 : ∀ x : K, x + x = 0 := by
      intro x
      have h1 : (1 : ZMod 2) + 1 = 0 := by decide
      have h2 : (1 : K) + 1 = 0 := by
        have := congrArg (fun r : ZMod 2 => φ (Polynomial.C r)) h1
        simpa only [map_add, map_one, map_zero] using this
      calc x + x = (1 + 1) * x := by ring
        _ = 0 * x := by rw [h2]
        _ = 0 := zero_mul x
    have htoPoly0 : toPoly m 0 = 0 := by
      simp [toPoly]
    by_cases ha0 : a = 0
    · have hdlo0 : dlo = 0 :=
        hφ_inj dlo 0 hdlo_lt h2m_pos (by rw [htoPoly0, map_zero]; exact ha0)
      have hdhi0 : dhi ≠ 0 := by
        intro h0
        apply hd
        rw [hd_eq, hdlo0, h0]
        simp
      have hemp : ((gammaSet m P).filter (fun z => z ^^^ d ∈ gammaSet m P)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro z hz hmem
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hmem
        rw [Finset.mem_range] at hu hv
        have hlo : v = u := by
          apply Nat.eq_of_testBit_eq
          intro j
          by_cases hj : j < m
          · have hbit := congrArg (fun n => n.testBit j) heq
            rw [Nat.testBit_xor, testBit_add_mul_two_pow hu, testBit_add_mul_two_pow hv,
              hd_eq, hdlo0, testBit_add_mul_two_pow h2m_pos] at hbit
            simp [hj] at hbit
            exact hbit
          · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))),
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by omega) (by omega)))]
        subst hlo
        have hhi : cubeNat m P v = cubeNat m P v ^^^ dhi := by
          apply Nat.eq_of_testBit_eq
          intro j
          by_cases hj : j < m
          · have hbit := congrArg (fun n => n.testBit (m + j)) heq
            rw [Nat.testBit_xor, testBit_add_mul_two_pow hu,
              hd_eq, hdlo0, testBit_add_mul_two_pow h2m_pos] at hbit
            simp only [show ¬ m + j < m by omega, ↓reduceIte, Nat.add_sub_cancel_left] at hbit
            rw [Nat.testBit_xor]
            exact hbit
          · have hc := cubeNat_lt m P v
            rw [Nat.testBit_xor,
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega))),
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hdhi_lt (Nat.pow_le_pow_right (by omega) (by omega)))]
            rfl
        have hxor0 : dhi = 0 := by
          apply Nat.eq_of_testBit_eq
          intro j
          have hbit := congrArg (fun n => n.testBit j) hhi
          rw [Nat.testBit_xor] at hbit
          rw [Nat.zero_testBit]
          cases h2 : dhi.testBit j
          · rfl
          · rw [h2] at hbit
            cases h1 : (cubeNat m P v).testBit j <;> rw [h1] at hbit <;> simp at hbit
        exact hdhi0 hxor0
      rw [hemp, Finset.card_empty]
      omega
    · let F : Polynomial K := Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (a ^ 2) * Polynomial.X + Polynomial.C (a ^ 3 + b)
      have hFdeg : F.natDegree ≤ 2 := by
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
          · refine le_trans (Polynomial.natDegree_mul_le) ?_
            simp [Polynomial.natDegree_C]
          · refine le_trans (Polynomial.natDegree_mul_le) ?_
            simp [Polynomial.natDegree_C, Polynomial.natDegree_X]
        · simp [Polynomial.natDegree_C]
      have hFne : F ≠ 0 := by
        intro hF0
        have hc2 := congrArg (fun p : Polynomial K => p.coeff 2) hF0
        simp only [F, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at hc2
        simp only [↓reduceIte, mul_one, show (1 : ℕ) ≠ 2 by decide, mul_zero, add_zero,
          show (2 : ℕ) ≠ 0 by decide] at hc2
        exact ha0 hc2
      let S := (gammaSet m P).filter (fun z => z ^^^ d ∈ gammaSet m P)
      let f : ℕ → K := fun z => φ (toPoly m (z % 2 ^ m))
      have hinj : Set.InjOn f S := by
        intro z₁ hz₁ z₂ hz₂ hfz
        obtain ⟨u₁, hu₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hz₁).1
        obtain ⟨u₂, hu₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hz₂).1
        rw [Finset.mem_range] at hu₁ hu₂
        simp only [f, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu₁, Nat.mod_eq_of_lt hu₂] at hfz
        have hu : u₁ = u₂ := hφ_inj u₁ u₂ hu₁ hu₂ hfz
        rw [hu]
      have hmaps : ∀ z ∈ S, f z ∈ F.roots.toFinset := by
        intro z hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hz2
        rw [Finset.mem_range] at hu hv
        have hv_eq : v = u ^^^ dlo := by
          apply Nat.eq_of_testBit_eq
          intro j
          by_cases hj : j < m
          · have hbit := congrArg (fun n => n.testBit j) heq
            rw [Nat.testBit_xor, testBit_add_mul_two_pow hu, testBit_add_mul_two_pow hv,
              hd_eq, testBit_add_mul_two_pow hdlo_lt] at hbit
            simp only [hj, ↓reduceIte] at hbit
            rw [Nat.testBit_xor]
            exact hbit
          · rw [Nat.testBit_xor,
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))),
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by omega) (by omega))),
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hdlo_lt (Nat.pow_le_pow_right (by omega) (by omega)))]
            rfl
        have hcv_eq : cubeNat m P v = cubeNat m P u ^^^ dhi := by
          apply Nat.eq_of_testBit_eq
          intro j
          by_cases hj : j < m
          · have hbit := congrArg (fun n => n.testBit (m + j)) heq
            rw [Nat.testBit_xor, testBit_add_mul_two_pow hu, testBit_add_mul_two_pow hv,
              hd_eq, testBit_add_mul_two_pow hdlo_lt] at hbit
            simp only [show ¬ m + j < m by omega, ↓reduceIte, Nat.add_sub_cancel_left] at hbit
            rw [Nat.testBit_xor]
            exact hbit
          · have hcu := cubeNat_lt m P u
            have hcv := cubeNat_lt m P v
            rw [Nat.testBit_xor,
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hcv (Nat.pow_le_pow_right (by omega) (by omega))),
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hcu (Nat.pow_le_pow_right (by omega) (by omega))),
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hdhi_lt (Nat.pow_le_pow_right (by omega) (by omega)))]
            rfl
        have hK : (φ (toPoly m u) + a) ^ 3 = (φ (toPoly m u)) ^ 3 + b := by
          have h1 := congrArg (fun n => φ (toPoly m n)) hcv_eq
          rw [hφ_cube, toPoly_xor, map_add, hφ_cube, hv_eq, toPoly_xor, map_add] at h1
          exact h1
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hFne, Polynomial.IsRoot]
        have hfx : f (u + 2 ^ m * cubeNat m P u) = φ (toPoly m u) := by
          simp [f, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
        rw [hfx]
        set x := φ (toPoly m u)
        simp only [F, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
        have hexp : (x + a) ^ 3 = x ^ 3 + a * x ^ 2 + a ^ 2 * x + a ^ 3 := by
          have h3 : (3 : K) = 1 := by
            have h1 : (2 : K) + 1 = 3 := by ring
            have h2 : (2 : K) = 0 := by
              have : (1 : K) + 1 = 0 := hchar2 1
              calc (2 : K) = 1 + 1 := by ring
                _ = 0 := this
            rw [← h1, h2, zero_add]
          calc (x + a) ^ 3 = x ^ 3 + (3 : K) * a * x ^ 2 + (3 : K) * a ^ 2 * x + a ^ 3 := by ring
            _ = x ^ 3 + 1 * a * x ^ 2 + 1 * a ^ 2 * x + a ^ 3 := by rw [h3]
            _ = x ^ 3 + a * x ^ 2 + a ^ 2 * x + a ^ 3 := by ring
        rw [hexp] at hK
        have hsub : x ^ 3 + (a * x ^ 2 + a ^ 2 * x + a ^ 3) = x ^ 3 + b := by
          calc x ^ 3 + (a * x ^ 2 + a ^ 2 * x + a ^ 3)
              = x ^ 3 + a * x ^ 2 + a ^ 2 * x + a ^ 3 := by ring
            _ = x ^ 3 + b := hK
        have hcancel : a * x ^ 2 + a ^ 2 * x + a ^ 3 = b := add_left_cancel hsub
        calc a * x ^ 2 + a ^ 2 * x + (a ^ 3 + b) = (a * x ^ 2 + a ^ 2 * x + a ^ 3) + b := by ring
          _ = b + b := by rw [hcancel]
          _ = 0 := hchar2 b
      calc S.card ≤ F.roots.toFinset.card := Finset.card_le_card_of_injOn f hmaps hinj
        _ ≤ F.roots.card := Multiset.toFinset_card_le _
        _ ≤ F.natDegree := Polynomial.card_roots' F
        _ ≤ 2 := hFdeg

theorem pow_two_ge_add_seven (a : ℕ) (ha : 6 ≤ a) : a + 7 ≤ 2 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    omega

theorem xor_lt_pow_two {k x y : ℕ} (hx : x < 2 ^ k) (hy : y < 2 ^ k) : x ^^^ y < 2 ^ k := by
  exact Nat.xor_lt_two_pow hx hy

theorem card_xor_mem_gamma (k : ℕ) (Γ : Finset ℕ) (hΓ : Γ ⊆ Finset.range (2 ^ k)) (x : Fin (2 ^ k)) :
    (Finset.univ.filter (fun z : Fin (2 ^ k) => x.val ^^^ z.val ∈ Γ)).card = Γ.card := by
  classical
  let S := Finset.univ.filter (fun z : Fin (2 ^ k) => x.val ^^^ z.val ∈ Γ)
  let f : Fin (2 ^ k) → ℕ := fun z => x.val ^^^ z.val
  have hinj : Set.InjOn f S := by
    intro z₁ _ z₂ _ heq
    apply Fin.ext
    have h1 := congrArg (fun n => x.val ^^^ n) heq
    simpa [f, Nat.xor_assoc] using h1
  have himg : S.image f = Γ := by
    ext d
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, f]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hd
      have hd_lt : d < 2 ^ k := Finset.mem_range.mp (hΓ hd)
      refine ⟨⟨x.val ^^^ d, xor_lt_pow_two x.isLt hd_lt⟩, ?_, ?_⟩
      · simpa [Nat.xor_assoc] using hd
      · simp
  calc S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ = Γ.card := by rw [himg]

theorem card_xor_symm_diff_gamma (k : ℕ) (Γ : Finset ℕ) (hΓ : Γ ⊆ Finset.range (2 ^ k))
    (hauto : ∀ d, d ≠ 0 → (Γ.filter (fun z => z ^^^ d ∈ Γ)).card ≤ 2)
    (i j : Fin (2 ^ k)) (hij : i ≠ j) :
    2 * Γ.card - 4 ≤
      (Finset.univ.filter (fun z : Fin (2 ^ k) =>
        decide (i.val ^^^ z.val ∈ Γ) ≠ decide (j.val ^^^ z.val ∈ Γ))).card ∧
    (Finset.univ.filter (fun z : Fin (2 ^ k) =>
        decide (i.val ^^^ z.val ∈ Γ) ≠ decide (j.val ^^^ z.val ∈ Γ))).card ≤ 2 * Γ.card := by
  classical
  let A := Finset.univ.filter (fun z : Fin (2 ^ k) => i.val ^^^ z.val ∈ Γ)
  let B := Finset.univ.filter (fun z : Fin (2 ^ k) => j.val ^^^ z.val ∈ Γ)
  have hA : A.card = Γ.card := card_xor_mem_gamma k Γ hΓ i
  have hB : B.card = Γ.card := card_xor_mem_gamma k Γ hΓ j
  have hS : Finset.univ.filter (fun z : Fin (2 ^ k) =>
      decide (i.val ^^^ z.val ∈ Γ) ≠ decide (j.val ^^^ z.val ∈ Γ)) = (A \ B) ∪ (B \ A) := by
    ext z
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
    by_cases hi : i.val ^^^ z.val ∈ Γ <;> by_cases hj : j.val ^^^ z.val ∈ Γ <;> simp [hi, hj]
  have hdisj : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff
  have hAB : (A ∩ B).card ≤ 2 := by
    let d := i.val ^^^ j.val
    have hd : d ≠ 0 := by
      intro h0
      apply hij
      apply Fin.ext
      have h1 := congrArg (fun n => i.val ^^^ n) h0
      simp only [d, Nat.xor_zero, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h1
      exact h1.symm
    let g : Fin (2 ^ k) → ℕ := fun z => i.val ^^^ z.val
    have hinj : Set.InjOn g ↑(A ∩ B) := by
      intro z₁ _ z₂ _ heq
      apply Fin.ext
      have h1 := congrArg (fun n => i.val ^^^ n) heq
      simpa [g, Nat.xor_assoc] using h1
    have hmaps : ∀ z ∈ A ∩ B, g z ∈ Γ.filter (fun w => w ^^^ d ∈ Γ) := by
      intro z hz
      obtain ⟨hzA, hzB⟩ := Finset.mem_inter.mp hz
      rw [Finset.mem_filter] at hzA hzB ⊢
      refine ⟨hzA.2, ?_⟩
      have hxd : g z ^^^ d = j.val ^^^ z.val := by
        dsimp [g, d]
        calc (i.val ^^^ z.val) ^^^ (i.val ^^^ j.val)
            = (z.val ^^^ i.val) ^^^ (i.val ^^^ j.val) := by rw [Nat.xor_comm i.val z.val]
          _ = z.val ^^^ (i.val ^^^ (i.val ^^^ j.val)) := by rw [Nat.xor_assoc]
          _ = z.val ^^^ ((i.val ^^^ i.val) ^^^ j.val) := by rw [Nat.xor_assoc]
          _ = z.val ^^^ j.val := by rw [Nat.xor_self, Nat.zero_xor]
          _ = j.val ^^^ z.val := Nat.xor_comm _ _
      rw [hxd]
      exact hzB.2
    exact le_trans (Finset.card_le_card_of_injOn g hmaps hinj) (hauto d hd)
  have hcard : ((A \ B) ∪ (B \ A)).card + 2 * (A ∩ B).card = A.card + B.card := by
    rw [Finset.card_union_of_disjoint hdisj]
    have h1 := Finset.card_sdiff_add_card_inter A B
    have h2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at h2
    omega
  rw [hS]
  omega

theorem card_mod_eq (k a : ℕ) (hak : a ≤ k) (c : ℕ) (hc : c < 2 ^ a) :
    (Finset.univ.filter (fun z : Fin (2 ^ k) => z.val % 2 ^ a = c)).card = 2 ^ (k - a) := by
  classical
  have hpow : 2 ^ k = 2 ^ a * 2 ^ (k - a) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hak]
  let f : Fin (2 ^ (k - a)) → Fin (2 ^ k) := fun q =>
    ⟨c + 2 ^ a * q.val, by
      have h1 : c + 2 ^ a * q.val < 2 ^ a * (q.val + 1) := by nlinarith
      have h2 : 2 ^ a * (q.val + 1) ≤ 2 ^ a * 2 ^ (k - a) := Nat.mul_le_mul_left _ q.isLt
      omega⟩
  have hinj : Function.Injective f := by
    intro q₁ q₂ heq
    have hv := congrArg Fin.val heq
    dsimp [f] at hv
    have hpos : 0 < 2 ^ a := Nat.pow_pos (by omega)
    have hq : q₁.val = q₂.val := by nlinarith
    exact Fin.ext hq
  have himg : Finset.univ.image f = Finset.univ.filter (fun z : Fin (2 ^ k) => z.val % 2 ^ a = c) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨q, rfl⟩
      dsimp [f]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    · intro hz
      have hqlt : z.val / 2 ^ a < 2 ^ (k - a) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))]
        have hlt : z.val < 2 ^ a * 2 ^ (k - a) := hpow ▸ z.isLt
        rw [Nat.mul_comm] at hlt
        exact hlt
      refine ⟨⟨z.val / 2 ^ a, hqlt⟩, Fin.ext ?_⟩
      dsimp [f]
      have hdm := Nat.div_add_mod z.val (2 ^ a)
      omega
  rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

theorem card_filter_add_not {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card + (Finset.univ.filter (fun z => ¬ P z)).card = Fintype.card α := by
  classical
  have hdisj : Disjoint (Finset.univ.filter P) (Finset.univ.filter (fun z => ¬ P z)) := by
    rw [Finset.disjoint_filter]
    intro z _ h1 h2; exact h2 h1
  have hunion : (Finset.univ.filter P) ∪ (Finset.univ.filter (fun z => ¬ P z)) = Finset.univ := by
    ext z
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact em (P z)
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]

theorem card_xor_bool_lower {α : Type*} [Fintype α] (p q : α → Bool) (c : Bool) :
    let P := (Finset.univ.filter (fun z => p z = true)).card
    let Q := (Finset.univ.filter (fun z => q z = true)).card
    let D := (Finset.univ.filter (fun z => xor (p z) (q z) ≠ c)).card
    (c = false → P - Q ≤ D ∧ Q - P ≤ D) ∧
    (c = true → (Fintype.card α - P) - Q ≤ D ∧ (Fintype.card α - Q) - P ≤ D ∧ Q - (Fintype.card α - P) ≤ D) := by
  classical
  dsimp only
  have htri : ∀ (u v : α → Bool),
      (Finset.univ.filter (fun z => u z = true)).card -
        (Finset.univ.filter (fun z => v z = true)).card ≤
      (Finset.univ.filter (fun z => xor (u z) (v z) = true)).card := by
    intro u v
    have hsub : Finset.univ.filter (fun z => u z = true) ⊆
        Finset.univ.filter (fun z => v z = true) ∪
        Finset.univ.filter (fun z => xor (u z) (v z) = true) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hz ⊢
      cases hv : v z <;> simp [hz]
    have hle := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    omega
  constructor
  · intro hc
    subst hc
    have heq : (Finset.univ.filter (fun z => xor (p z) (q z) ≠ false)) =
        (Finset.univ.filter (fun z => xor (p z) (q z) = true)) := by
      ext z; simp
    rw [heq]
    refine ⟨htri p q, ?_⟩
    have hcomm : (Finset.univ.filter (fun z => xor (p z) (q z) = true)) =
        (Finset.univ.filter (fun z => xor (q z) (p z) = true)) := by
      ext z; simp [Bool.xor_comm]
    rw [hcomm]
    exact htri q p
  · intro hc
    subst hc
    have h1 := htri (fun z => !p z) q
    have h2 := htri (fun z => !q z) p
    have h3 := htri q (fun z => !p z)
    have hcp : (Finset.univ.filter (fun z => (!p z) = true)).card =
        Fintype.card α - (Finset.univ.filter (fun z => p z = true)).card := by
      have htot := card_filter_add_not (fun z : α => p z = true)
      have heq : Finset.univ.filter (fun z => (!p z) = true) =
          Finset.univ.filter (fun z => ¬ p z = true) := by
        ext z; cases p z <;> simp
      rw [heq]
      omega
    have hcq : (Finset.univ.filter (fun z => (!q z) = true)).card =
        Fintype.card α - (Finset.univ.filter (fun z => q z = true)).card := by
      have htot := card_filter_add_not (fun z : α => q z = true)
      have heq : Finset.univ.filter (fun z => (!q z) = true) =
          Finset.univ.filter (fun z => ¬ q z = true) := by
        ext z; cases q z <;> simp
      rw [heq]
      omega
    have heq1 : (Finset.univ.filter (fun z => xor (!p z) (q z) = true)) =
        (Finset.univ.filter (fun z => xor (p z) (q z) ≠ true)) := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases p z <;> cases q z <;> decide
    have heq2 : (Finset.univ.filter (fun z => xor (!q z) (p z) = true)) =
        (Finset.univ.filter (fun z => xor (p z) (q z) ≠ true)) := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases p z <;> cases q z <;> decide
    have heq3 : (Finset.univ.filter (fun z => xor (q z) (!p z) = true)) =
        (Finset.univ.filter (fun z => xor (p z) (q z) ≠ true)) := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases p z <;> cases q z <;> decide
    rw [hcp, heq1] at h1
    rw [hcq, heq2] at h2
    rw [hcp, heq3] at h3
    exact ⟨h1, h2, h3⟩

theorem row_col_dist_ge (k a : ℕ) (ha : 6 ≤ a) (hk : 2 * 2 ^ a ≤ k)
    (Γ : Finset ℕ) (hΓsub : Γ ⊆ Finset.range (2 ^ k)) (hΓcard : Γ.card = 2 ^ (k / 2))
    (hauto : ∀ d, d ≠ 0 → (Γ.filter (fun z => z ^^^ d ∈ Γ)).card ≤ 2)
    (f g : Fin (2 ^ k) → Bool) :
    let N := 2 ^ k
    let r := 2 ^ a
    let T : Fin N → Fin N → Bool := fun x y =>
      xor (xor (x.val.testBit (y.val % r)) (decide (x.val ^^^ y.val ∈ Γ))) (xor (f x) (g y))
    (∀ i j : Fin N, i ≠ j → 2 * 2 ^ (k / 2) - 4 ≤ (Finset.univ.filter (fun z : Fin N => T i z ≠ T j z)).card) ∧
    (∀ i j : Fin N, i ≠ j → 2 * 2 ^ (k / 2) - 4 ≤ (Finset.univ.filter (fun z : Fin N => T z i ≠ T z j)).card) := by
  classical
  dsimp only
  have hak : a ≤ k := by
    have := pow_two_ge_add_seven a ha
    omega
  have hrk : 2 ^ a < k := by omega
  have hNr_ge : 4 * 2 ^ (k / 2) ≤ 2 ^ (k - a) := by
    have h4 : 4 * 2 ^ (k / 2) = 2 ^ (k / 2 + 2) := by
      rw [Nat.pow_add]; ring
    rw [h4]
    apply Nat.pow_le_pow_right (by omega)
    have := pow_two_ge_add_seven a ha
    omega
  have hN_ge : 4 * 2 ^ (k / 2) ≤ 2 ^ k := by
    exact le_trans hNr_ge (Nat.pow_le_pow_right (by omega) (by omega))
  have hN_half_ge : 4 * 2 ^ (k / 2) ≤ 2 ^ (k - 1) := by
    exact le_trans hNr_ge (Nat.pow_le_pow_right (by omega) (by omega))
  constructor
  · intro i j hij
    let p : Fin (2 ^ k) → Bool := fun z =>
      xor (i.val.testBit (z.val % 2 ^ a)) (j.val.testBit (z.val % 2 ^ a))
    let q : Fin (2 ^ k) → Bool := fun z =>
      xor (decide (i.val ^^^ z.val ∈ Γ)) (decide (j.val ^^^ z.val ∈ Γ))
    let c : Bool := xor (f i) (f j)
    have hfilt : (Finset.univ.filter (fun z : Fin (2 ^ k) =>
        xor (xor (i.val.testBit (z.val % 2 ^ a)) (decide (i.val ^^^ z.val ∈ Γ))) (xor (f i) (g z)) ≠
        xor (xor (j.val.testBit (z.val % 2 ^ a)) (decide (j.val ^^^ z.val ∈ Γ))) (xor (f j) (g z)))) =
        Finset.univ.filter (fun z : Fin (2 ^ k) => xor (p z) (q z) ≠ c) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, q, c]
      cases i.val.testBit (z.val % 2 ^ a) <;> cases j.val.testBit (z.val % 2 ^ a) <;>
        cases decide (i.val ^^^ z.val ∈ Γ) <;> cases decide (j.val ^^^ z.val ∈ Γ) <;>
        cases f i <;> cases f j <;> cases g z <;> decide
    rw [hfilt]
    have hq_eq : (Finset.univ.filter (fun z : Fin (2 ^ k) => q z = true)) =
        Finset.univ.filter (fun z : Fin (2 ^ k) => decide (i.val ^^^ z.val ∈ Γ) ≠ decide (j.val ^^^ z.val ∈ Γ)) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, q]
      cases decide (i.val ^^^ z.val ∈ Γ) <;> cases decide (j.val ^^^ z.val ∈ Γ) <;> decide
    have hq_bounds := card_xor_symm_diff_gamma k Γ hΓsub hauto i j hij
    rw [← hq_eq, hΓcard] at hq_bounds
    let S := (Finset.range (2 ^ a)).filter (fun r0 => i.val.testBit r0 ≠ j.val.testBit r0)
    have hp_card : (Finset.univ.filter (fun z : Fin (2 ^ k) => p z = true)).card = S.card * 2 ^ (k - a) := by
      have hfib : (Finset.univ.filter (fun z : Fin (2 ^ k) => p z = true)).card =
          ∑ r0 ∈ S, (Finset.univ.filter (fun z : Fin (2 ^ k) => z.val % 2 ^ a = r0)).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := fun z : Fin (2 ^ k) => z.val % 2 ^ a) (t := S)]
        · apply Finset.sum_congr rfl
          intro r0 hr0
          congr 1
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, S, Finset.mem_range] at hr0 ⊢
          constructor
          · intro h; exact h.2
          · intro h
            refine ⟨?_, h⟩
            rw [h]
            cases h1 : i.val.testBit r0 <;> cases h2 : j.val.testBit r0 <;> simp_all
        · intro z hz
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, p, S, Finset.mem_range] at hz ⊢
          refine ⟨Nat.mod_lt _ (Nat.pow_pos (by omega)), ?_⟩
          cases h1 : i.val.testBit (z.val % 2 ^ a) <;> cases h2 : j.val.testBit (z.val % 2 ^ a) <;> simp_all
      rw [hfib]
      have hconst : ∑ r0 ∈ S, (Finset.univ.filter (fun z : Fin (2 ^ k) => z.val % 2 ^ a = r0)).card =
          ∑ _r0 ∈ S, 2 ^ (k - a) := by
        apply Finset.sum_congr rfl
        intro r0 hr0
        exact card_mod_eq k a hak r0 (Finset.mem_range.mp (Finset.mem_filter.mp hr0).1)
      rw [hconst, Finset.sum_const, smul_eq_mul]
    have hS_le : S.card ≤ 2 ^ a := by
      have := Finset.card_filter_le (Finset.range (2 ^ a)) (fun r0 => i.val.testBit r0 ≠ j.val.testBit r0)
      simpa using this
    have hpow : 2 ^ a * 2 ^ (k - a) = 2 ^ k := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hak]
    have hlb := card_xor_bool_lower p q c
    simp only [Fintype.card_fin] at hlb
    by_cases hS0 : S.card = 0
    · rw [hS0, Nat.zero_mul] at hp_card
      rcases Bool.eq_false_or_eq_true c with hc | hc
      · have := (hlb.2 hc).2.1; omega
      · have := (hlb.1 hc).2; omega
    · by_cases hSr : S.card = 2 ^ a
      · rw [hSr, hpow] at hp_card
        rcases Bool.eq_false_or_eq_true c with hc | hc
        · have := (hlb.2 hc).2.2; omega
        · have := (hlb.1 hc).1; omega
      · have h1 : 2 ^ (k - a) ≤ (Finset.univ.filter (fun z : Fin (2 ^ k) => p z = true)).card := by
          rw [hp_card]
          have : 1 ≤ S.card := by omega
          nlinarith
        have h2 : (Finset.univ.filter (fun z : Fin (2 ^ k) => p z = true)).card + 2 ^ (k - a) ≤ 2 ^ k := by
          rw [hp_card, ← hpow]
          have : S.card + 1 ≤ 2 ^ a := by omega
          nlinarith
        rcases Bool.eq_false_or_eq_true c with hc | hc
        · have := (hlb.2 hc).1; omega
        · have := (hlb.1 hc).1; omega
  · intro i j hij
    let p : Fin (2 ^ k) → Bool := fun z =>
      xor (z.val.testBit (i.val % 2 ^ a)) (z.val.testBit (j.val % 2 ^ a))
    let q : Fin (2 ^ k) → Bool := fun z =>
      xor (decide (z.val ^^^ i.val ∈ Γ)) (decide (z.val ^^^ j.val ∈ Γ))
    let c : Bool := xor (g i) (g j)
    have hfilt : (Finset.univ.filter (fun z : Fin (2 ^ k) =>
        xor (xor (z.val.testBit (i.val % 2 ^ a)) (decide (z.val ^^^ i.val ∈ Γ))) (xor (f z) (g i)) ≠
        xor (xor (z.val.testBit (j.val % 2 ^ a)) (decide (z.val ^^^ j.val ∈ Γ))) (xor (f z) (g j)))) =
        Finset.univ.filter (fun z : Fin (2 ^ k) => xor (p z) (q z) ≠ c) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, q, c]
      cases z.val.testBit (i.val % 2 ^ a) <;> cases z.val.testBit (j.val % 2 ^ a) <;>
        cases decide (z.val ^^^ i.val ∈ Γ) <;> cases decide (z.val ^^^ j.val ∈ Γ) <;>
        cases f z <;> cases g i <;> cases g j <;> decide
    rw [hfilt]
    have hq_eq : (Finset.univ.filter (fun z : Fin (2 ^ k) => q z = true)) =
        Finset.univ.filter (fun z : Fin (2 ^ k) => decide (i.val ^^^ z.val ∈ Γ) ≠ decide (j.val ^^^ z.val ∈ Γ)) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, q, Nat.xor_comm z.val]
      cases decide (i.val ^^^ z.val ∈ Γ) <;> cases decide (j.val ^^^ z.val ∈ Γ) <;> decide
    have hq_bounds := card_xor_symm_diff_gamma k Γ hΓsub hauto i j hij
    rw [← hq_eq, hΓcard] at hq_bounds
    have hlb := card_xor_bool_lower p q c
    simp only [Fintype.card_fin] at hlb
    by_cases hmod : i.val % 2 ^ a = j.val % 2 ^ a
    · have hp0 : (Finset.univ.filter (fun z : Fin (2 ^ k) => p z = true)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro z _
        simp [p, hmod]
      rcases Bool.eq_false_or_eq_true c with hc | hc
      · have := (hlb.2 hc).2.1; omega
      · have := (hlb.1 hc).2; omega
    · have hb_lt : i.val % 2 ^ a < k := lt_trans (Nat.mod_lt _ (Nat.pow_pos (by omega))) hrk
      have hmask_lt : 2 ^ (i.val % 2 ^ a) < 2 ^ k := Nat.pow_lt_pow_right (by omega) hb_lt
      let flip : Fin (2 ^ k) → Fin (2 ^ k) := fun z => ⟨z.val ^^^ 2 ^ (i.val % 2 ^ a), xor_lt_pow_two z.isLt hmask_lt⟩
      have hflip_inv : ∀ z, flip (flip z) = z := by
        intro z; apply Fin.ext; dsimp [flip]; rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      have hflip_p : ∀ z, p (flip z) = !p z := by
        intro z
        dsimp [p, flip]
        rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_two_pow_self,
          Nat.testBit_two_pow_of_ne hmod]
        cases z.val.testBit (i.val % 2 ^ a) <;> cases z.val.testBit (j.val % 2 ^ a) <;> decide
      have hcard_eq : (Finset.univ.filter (fun z : Fin (2 ^ k) => p z = true)).card =
          (Finset.univ.filter (fun z : Fin (2 ^ k) => ¬ p z = true)).card := by
        apply Finset.card_bij (fun z _ => flip z)
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          rw [hflip_p, hz]; decide
        · intro z₁ _ z₂ _ heq
          have := congrArg flip heq
          simpa [hflip_inv] using this
        · intro z hz
          refine ⟨flip z, ?_, hflip_inv z⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          rw [hflip_p]
          cases hp : p z <;> simp_all
      have htot := card_filter_add_not (fun z : Fin (2 ^ k) => p z = true)
      rw [Fintype.card_fin] at htot
      have hpow2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
        have hk1 : k = (k - 1) + 1 := by omega
        conv_lhs => rw [hk1, Nat.pow_succ]
        ring
      have hp_half : (Finset.univ.filter (fun z : Fin (2 ^ k) => p z = true)).card = 2 ^ (k - 1) := by omega
      rcases Bool.eq_false_or_eq_true c with hc | hc
      · have := (hlb.2 hc).1; omega
      · have := (hlb.1 hc).1; omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def runGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

theorem circuit_wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = runGates C.gates x := rfl

theorem runGates_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    runGates (gs₁ ++ gs₂) w = runGates gs₂ (runGates gs₁ w) :=
  List.foldl_append

theorem runGates_length (gs : List Gate) (w : List Bool) :
    (runGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runGates]
  | cons g gs ih =>
    simp only [runGates, List.foldl_cons]
    change (runGates gs _).length = _
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem list_getD_append_left {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem list_getD_append_right {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

theorem runGates_getD_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (runGates gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [runGates, List.foldl_cons]
    change (runGates gs _).getD i false = _
    rw [ih _ (by rw [List.length_append, List.length_singleton]; omega),
      list_getD_append_left _ _ _ _ hi]

theorem runGates_getD_append (gs₁ gs₂ : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + gs₁.length) :
    (runGates (gs₁ ++ gs₂) w).getD i false = (runGates gs₁ w).getD i false := by
  rw [runGates_append, runGates_getD_prefix gs₂ (runGates gs₁ w) i (by rw [runGates_length]; exact hi)]

theorem runGates_getD_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    (runGates (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (runGates gs w).getD i false) := by
  rw [runGates_append]
  change (runGates gs w ++ [g.op.eval (g.inputs.map fun i => (runGates gs w).getD i false)]).getD
      (w.length + gs.length) false = _
  have hlen : (runGates gs w).length = w.length + gs.length := runGates_length gs w
  rw [← hlen, list_getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

theorem list_any_congr {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self ..), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false =
      if i < n then decide (i = u.val)
      else if i < n + m then decide (i - n = v.val)
      else false := by
  unfold oneEach
  by_cases h1 : i < n
  · rw [list_getD_append_left _ _ _ _ (by simp [h1])]
    simp only [h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_ofFn, ↓reduceDIte,
      Option.getD_some, Fin.ext_iff]
  · rw [list_getD_append_right _ _ _ _ (by simp; omega)]
    simp only [h1, ↓reduceIte, List.length_ofFn]
    by_cases h2 : i < n + m
    · have hsub : i - n < m := by omega
      simp only [h2, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hsub, ↓reduceDIte,
        Option.getD_some, Fin.ext_iff]
    · have hsub : ¬ i - n < m := by omega
      simp only [h2, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hsub, ↓reduceDIte,
        Option.getD_none]

def appendOrChain (base : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: rest =>
    let idx := base + gs.length
    appendOrChain base (gs ++ [⟨GateOp.or, [acc, w]⟩]) idx rest

theorem appendOrChain_spec (base : ℕ) (gs : List Gate) (acc : ℕ) (ws : List ℕ) :
    let res := appendOrChain base gs acc ws
    (∃ extra, res.1 = gs ++ extra ∧
      (∀ g ∈ extra, g.op = GateOp.or ∧ g.inputs.length = 2) ∧
      extra.length = ws.length) ∧
    (acc < base + gs.length → (∀ w ∈ ws, w < base + gs.length) →
      res.2 < base + res.1.length ∧
      ∀ x : List Bool, x.length = base →
        (runGates res.1 x).getD res.2 false =
          ((runGates gs x).getD acc false || ws.any (fun w => (runGates gs x).getD w false))) := by
  induction ws generalizing gs acc with
  | nil =>
    refine ⟨⟨[], by simp [appendOrChain], by simp, by simp⟩, ?_⟩
    intro hacc _
    refine ⟨hacc, fun x _ => by simp [appendOrChain]⟩
  | cons w rest ih =>
    dsimp only [appendOrChain]
    set g0 : Gate := ⟨GateOp.or, [acc, w]⟩
    set gs1 := gs ++ [g0]
    set idx := base + gs.length
    have hih := ih gs1 idx
    rcases hih with ⟨⟨extra1, hres1, hextra1, hlen1⟩, heval1⟩
    refine ⟨⟨g0 :: extra1, ?_, ?_, ?_⟩, ?_⟩
    · rw [hres1]; simp [gs1]
    · intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨rfl, rfl⟩
      · exact hextra1 g hg
    · simp [hlen1]
    · intro hacc hws
      have hw : w < base + gs.length := hws w (List.mem_cons_self ..)
      have hidx_lt : idx < base + gs1.length := by simp [idx, gs1]
      have hrest_lt : ∀ u ∈ rest, u < base + gs1.length := by
        intro u hu
        have := hws u (List.mem_cons_of_mem w hu)
        simp only [gs1, List.length_append, List.length_singleton]
        omega
      obtain ⟨hout_lt, hout_eval⟩ := heval1 hidx_lt hrest_lt
      refine ⟨hout_lt, ?_⟩
      intro x hx
      rw [hout_eval x hx]
      have hidx_val : (runGates gs1 x).getD idx false =
          ((runGates gs x).getD acc false || (runGates gs x).getD w false) := by
        simp only [gs1, idx, ← hx]
        rw [runGates_getD_snoc]
        simp [g0, GateOp.eval]
      have hrest_val : rest.any (fun u => (runGates gs1 x).getD u false) =
          rest.any (fun u => (runGates gs x).getD u false) := by
        apply list_any_congr
        intro u hu
        have hu_lt : u < x.length + gs.length := by rw [hx]; exact hws u (List.mem_cons_of_mem w hu)
        rw [runGates_getD_append gs [g0] x u hu_lt]
      rw [hidx_val, hrest_val, List.any_cons, Bool.or_assoc]

def mkOrList (base : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs ++ [⟨GateOp.or, []⟩], base + gs.length)
  | w :: rest => appendOrChain base gs w rest

theorem mkOrList_spec (base : ℕ) (gs : List Gate) (ws : List ℕ) :
    let res := mkOrList base gs ws
    (∃ extra, res.1 = gs ++ extra ∧
      (∀ g ∈ extra, g.inputs.length ≤ 2) ∧
      extra.countP (fun g => g.inputs.length == 2) ≤ ws.length) ∧
    ((∀ w ∈ ws, w < base + gs.length) →
      res.2 < base + res.1.length ∧
      ∀ x : List Bool, x.length = base →
        (runGates res.1 x).getD res.2 false =
          ws.any (fun w => (runGates gs x).getD w false)) := by
  cases ws with
  | nil =>
    refine ⟨⟨[⟨GateOp.or, []⟩], rfl, ?_, ?_⟩, ?_⟩
    · intro g hg; simp at hg; subst hg; simp
    · simp
    · intro _
      refine ⟨by simp [mkOrList], ?_⟩
      intro x hx
      simp only [mkOrList, ← hx]
      rw [runGates_getD_snoc]
      simp [GateOp.eval]
  | cons w rest =>
    dsimp only [mkOrList]
    obtain ⟨⟨extra, hres, hextra, hlen⟩, heval⟩ := appendOrChain_spec base gs w rest
    refine ⟨⟨extra, hres, ?_, ?_⟩, ?_⟩
    · intro g hg; exact le_of_eq (hextra g hg).2
    · calc extra.countP (fun g => g.inputs.length == 2) ≤ extra.length := List.countP_le_length
        _ = rest.length := hlen
        _ ≤ (w :: rest).length := by simp
    · intro hws
      have hw : w < base + gs.length := hws w (List.mem_cons_self ..)
      have hrest : ∀ u ∈ rest, u < base + gs.length := fun u hu => hws u (List.mem_cons_of_mem w hu)
      obtain ⟨hlt, hev⟩ := heval hw hrest
      refine ⟨hlt, ?_⟩
      intro x hx
      rw [hev x hx, List.any_cons]

noncomputable def mkOrMapNC {α : Type*} [DecidableEq α] (base : ℕ) (gs : List Gate)
    (keys : List α) (f : α → List ℕ) : List Gate × (α → ℕ) :=
  match keys with
  | [] => (gs, fun _ => 0)
  | a :: rest =>
    let p1 := mkOrList base gs (f a)
    let p2 := mkOrMapNC base p1.1 rest f
    (p2.1, fun b => if b = a then p1.2 else p2.2 b)

theorem mkOrMapNC_spec {α : Type*} [DecidableEq α] (base : ℕ) (gs : List Gate)
    (keys : List α) (f : α → List ℕ) (hnd : keys.Nodup) :
    let res := mkOrMapNC base gs keys f
    (∃ extra, res.1 = gs ++ extra ∧
      (∀ g ∈ extra, g.inputs.length ≤ 2) ∧
      extra.countP (fun g => g.inputs.length == 2) ≤ (keys.map (fun a => (f a).length)).sum) ∧
    ((∀ a ∈ keys, ∀ w ∈ f a, w < base + gs.length) →
      (∀ a ∈ keys, res.2 a < base + res.1.length) ∧
      ∀ a ∈ keys, ∀ x : List Bool, x.length = base →
        (runGates res.1 x).getD (res.2 a) false =
          (f a).any (fun w => (runGates gs x).getD w false)) := by
  induction keys generalizing gs with
  | nil =>
    refine ⟨⟨[], by simp [mkOrMapNC], by simp, by simp⟩, fun _ => ⟨by simp, by simp⟩⟩
  | cons a rest ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hanot, hnd_rest⟩ := hnd
    dsimp only [mkOrMapNC]
    set p1 := mkOrList base gs (f a)
    obtain ⟨⟨e1, he1, hg1, hc1⟩, hv1⟩ := mkOrList_spec base gs (f a)
    obtain ⟨⟨e2, he2, hg2, hc2⟩, hv2⟩ := ih p1.1 hnd_rest
    refine ⟨⟨e1 ++ e2, ?_, ?_, ?_⟩, ?_⟩
    · rw [he2, he1, List.append_assoc]
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with h | h
      · exact hg1 g h
      · exact hg2 g h
    · rw [List.countP_append, List.map_cons, List.sum_cons]
      omega
    · intro hlt
      have hlt_a : ∀ w ∈ f a, w < base + gs.length := hlt a (List.mem_cons_self ..)
      obtain ⟨hw1_lt, hw1_ev⟩ := hv1 hlt_a
      have hlt_rest : ∀ b ∈ rest, ∀ w ∈ f b, w < base + p1.1.length := by
        intro b hb w hw
        have := hlt b (List.mem_cons_of_mem a hb) w hw
        rw [he1, List.length_append]
        omega
      obtain ⟨hw2_lt, hw2_ev⟩ := hv2 hlt_rest
      constructor
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · simp only [↓reduceIte]
          have hlen2 : (mkOrMapNC base p1.1 rest f).1.length = p1.1.length + e2.length := by
            rw [he2, List.length_append]
          change p1.2 < base + (mkOrMapNC base p1.1 rest f).1.length
          dsimp only [p1] at hlen2 ⊢
          omega
        · have hba : b ≠ a := fun h => hanot (h ▸ hb)
          simp only [hba, ↓reduceIte]
          exact hw2_lt b hb
      · intro b hb x hx
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · simp only [↓reduceIte]
          have h1 := runGates_getD_append p1.1 e2 x p1.2 (by rw [hx]; exact hw1_lt)
          rw [he2, h1, hw1_ev x hx]
        · have hba : b ≠ a := fun h => hanot (h ▸ hb)
          simp only [hba, ↓reduceIte]
          rw [hw2_ev b hb x hx]
          apply list_any_congr
          intro w hw
          have hw_lt : w < x.length + gs.length := by rw [hx]; exact hlt b (List.mem_cons_of_mem a hb) w hw
          rw [he1, runGates_getD_append gs e1 x w hw_lt]

theorem list_sum_filter_partition {α β : Type*} [DecidableEq β] (xs : List α) (keys : List β)
    (key : α → β) (hnd : keys.Nodup) (hcov : ∀ x ∈ xs, key x ∈ keys) :
    (keys.map (fun k => (xs.filter (fun x => decide (key x = k))).length)).sum = xs.length := by
  induction xs with
  | nil =>
    simp only [List.filter_nil, List.length_nil]
    clear hnd hcov
    induction keys with
    | nil => rfl
    | cons _ _ ih => simp
  | cons x xs ih =>
    have hkx : key x ∈ keys := hcov x (List.mem_cons_self ..)
    have hcov' : ∀ y ∈ xs, key y ∈ keys := fun y hy => hcov y (List.mem_cons_of_mem x hy)
    have hstep : ∀ (ks : List β), ks.Nodup →
        (ks.map (fun k => ((x :: xs).filter (fun y => decide (key y = k))).length)).sum =
        (ks.map (fun k => (xs.filter (fun y => decide (key y = k))).length)).sum +
          if key x ∈ ks then 1 else 0 := by
      intro ks hks
      induction ks with
      | nil => simp
      | cons k ks ihk =>
        rw [List.nodup_cons] at hks
        simp only [List.map_cons, List.sum_cons, List.mem_cons]
        rw [ihk hks.2, List.filter_cons]
        by_cases h : key x = k
        · subst h
          simp only [↓reduceIte, decide_true, List.length_cons, hks.1, or_false]
          omega
        · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, false_or]
          omega
    rw [hstep keys hnd, ih hcov', ite_eq_left_iff.mpr (fun hn => absurd hkx hn), List.length_cons]

theorem list_map_sum_le_mul {α : Type*} (l : List α) (f : α → ℕ) (B : ℕ) (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    nlinarith

theorem finRange_flatMap_bool_nodup (m : ℕ) :
    ((List.finRange m).flatMap (fun p => [(p, false), (p, true)])).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun _ _ => by simp, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij pb h1 h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  have hne : (List.finRange m)[i] ≠ (List.finRange m)[j] := by
    intro heq
    have := congrArg Fin.val heq
    simp only [List.getElem_finRange, Fin.val_cast] at this
    omega
  rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2 <;> injection h2 with h2' <;> exact hne h2'

theorem exists_base_circuit (k a : ℕ) (ha : 6 ≤ a) (hk : 2 * 2 ^ a ≤ k)
    (Γ : Finset ℕ) (hΓ : Γ ⊆ Finset.range (2 ^ k))
    (f g : Fin (2 ^ k) → Bool) :
    let N := 2 ^ k
    let r := 2 ^ a
    let I := Fin N
    let target := fun (D : Finset ℕ) (x y : I) =>
      xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
    let fits := fun C : Circuit =>
      (∀ gt ∈ C.gates, gt.inputs.length ≤ 2) ∧ 16 * (C.gates.countP (fun gt => gt.inputs.length == 2)) ≤ 33 * N
    let table := fun (C : Circuit) (x y : I) => C.eval (oneEach x y)
    let loss := fun (H : I → I → Bool) (D : Finset ℕ) =>
      (Finset.univ.filter (fun z : I × I => H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2)))).card
    ∃ C₀ : Circuit, fits C₀ ∧ (∀ D : Finset ℕ, D ⊆ Γ → loss (table C₀) D = N * D.card) := by
  classical
  dsimp only
  let N : ℕ := 2 ^ k
  let r : ℕ := 2 ^ a
  let base : ℕ := N + N
  let pKeys : List (Fin (2 ^ r) × Bool) :=
    (List.finRange (2 ^ r)).flatMap (fun p => [(p, false), (p, true)])
  have hpKeys_nd : pKeys.Nodup := finRange_flatMap_bool_nodup (2 ^ r)
  let rKeys : List (Fin r × Bool) :=
    (List.finRange r).flatMap (fun j => [(j, false), (j, true)])
  have hrKeys_nd : rKeys.Nodup := finRange_flatMap_bool_nodup r
  have hr_pos : 0 < r := Nat.pow_pos (by omega)
  have h2r_pos : 0 < 2 ^ r := Nat.pow_pos (by omega)
  let pKeyOf : Fin N → Fin (2 ^ r) × Bool := fun u => (⟨u.val % 2 ^ r, Nat.mod_lt _ h2r_pos⟩, f u)
  let rKeyOf : Fin N → Fin r × Bool := fun v => (⟨v.val % r, Nat.mod_lt _ hr_pos⟩, g v)
  let pList : Fin (2 ^ r) × Bool → List ℕ := fun pb =>
    ((List.finRange N).filter (fun u => decide (pKeyOf u = pb))).map Fin.val
  let rList : Fin r × Bool → List ℕ := fun jc =>
    ((List.finRange N).filter (fun v => decide (rKeyOf v = jc))).map (fun v => N + v.val)
  have hpKeys_mem : ∀ pb : Fin (2 ^ r) × Bool, pb ∈ pKeys := by
    intro ⟨p, b⟩
    simp only [pKeys, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨p, ?_⟩
    cases b <;> simp
  have hrKeys_mem : ∀ jc : Fin r × Bool, jc ∈ rKeys := by
    intro ⟨j, c⟩
    simp only [rKeys, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨j, ?_⟩
    cases c <;> simp
  have hpKeys_len : pKeys.length = 2 * 2 ^ r := by
    simp [pKeys, List.length_flatMap, List.map_const', List.sum_replicate, Nat.mul_comm]
  have hrKeys_len : rKeys.length = 2 * r := by
    simp [rKeys, List.length_flatMap, List.map_const', List.sum_replicate, Nat.mul_comm]
  have hlt1 : ∀ pb ∈ pKeys, ∀ w ∈ pList pb, w < base + ([] : List Gate).length := by
    intro pb _ w hw
    simp only [pList, List.mem_map, List.mem_filter] at hw
    obtain ⟨u, _, rfl⟩ := hw
    have := u.isLt; simp only [List.length_nil, add_zero, base]; omega
  obtain ⟨⟨e1, he1, hge1, hce1⟩, hev1⟩ := mkOrMapNC_spec base [] pKeys pList hpKeys_nd
  obtain ⟨hwP_lt, hwP_ev⟩ := hev1 hlt1
  generalize hs1 : mkOrMapNC base [] pKeys pList = s1 at he1 hwP_lt hwP_ev
  clear hs1
  rcases s1 with ⟨gs1, wP⟩
  dsimp only at he1 hwP_lt hwP_ev
  have hlt2 : ∀ jc ∈ rKeys, ∀ w ∈ rList jc, w < base + gs1.length := by
    intro jc _ w hw
    simp only [rList, List.mem_map, List.mem_filter] at hw
    obtain ⟨v, _, rfl⟩ := hw
    have := v.isLt; simp only [base]; omega
  obtain ⟨⟨e2, he2, hge2, hce2⟩, hev2⟩ := mkOrMapNC_spec base gs1 rKeys rList hrKeys_nd
  obtain ⟨hwY_lt, hwY_ev⟩ := hev2 hlt2
  generalize hs2 : mkOrMapNC base gs1 rKeys rList = s2 at he2 hwY_lt hwY_ev
  clear hs2
  rcases s2 with ⟨gs2, wY⟩
  dsimp only at he2 hwY_lt hwY_ev
  let xList : Fin r × Bool → List ℕ := fun jc =>
    (pKeys.filter (fun pb => decide (xor (pb.1.val.testBit jc.1.val) pb.2 = jc.2))).map wP
  have hlt3 : ∀ jc ∈ rKeys, ∀ w ∈ xList jc, w < base + gs2.length := by
    intro jc _ w hw
    simp only [xList, List.mem_map, List.mem_filter] at hw
    obtain ⟨pb, hpb, rfl⟩ := hw
    have := hwP_lt pb hpb.1
    rw [he2, List.length_append]; omega
  obtain ⟨⟨e3, he3, hge3, hce3⟩, hev3⟩ := mkOrMapNC_spec base gs2 rKeys xList hrKeys_nd
  obtain ⟨hwX_lt, hwX_ev⟩ := hev3 hlt3
  generalize hs3 : mkOrMapNC base gs2 rKeys xList = s3 at he3 hwX_lt hwX_ev
  clear hs3
  rcases s3 with ⟨gs3, wX⟩
  dsimp only at he3 hwX_lt hwX_ev
  let andGates : List Gate := rKeys.map (fun jc => ⟨GateOp.and, [wX (jc.1, !jc.2), wY jc]⟩)
  let gs4 := gs3 ++ andGates
  let zWires : List ℕ := (List.range rKeys.length).map (fun i => base + gs3.length + i)
  have hlt5 : ∀ w ∈ zWires, w < base + gs4.length := by
    intro w hw
    simp only [zWires, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    simp only [gs4, andGates, List.length_append, List.length_map]
    omega
  obtain ⟨⟨e5, he5, hge5, hce5⟩, hev5⟩ := mkOrList_spec base gs4 zWires
  obtain ⟨_, hw5_ev⟩ := hev5 hlt5
  generalize hs5 : mkOrList base gs4 zWires = s5 at he5 hw5_ev
  clear hs5
  rcases s5 with ⟨gs5, wOut⟩
  dsimp only at he5 hw5_ev
  let C₀ : Circuit := ⟨gs5, wOut⟩
  have hfits : (∀ gt ∈ C₀.gates, gt.inputs.length ≤ 2) ∧
      16 * (C₀.gates.countP (fun gt => gt.inputs.length == 2)) ≤ 33 * N := by
    have hgs1_eq : gs1 = e1 := by simpa using he1
    have hgs2_eq : gs2 = e1 ++ e2 := by rw [← hgs1_eq]; exact he2
    have hgs3_eq : gs3 = e1 ++ e2 ++ e3 := by rw [← hgs2_eq]; exact he3
    have hgs4_eq : gs4 = e1 ++ e2 ++ e3 ++ andGates := by rw [← hgs3_eq]
    have hC0_eq : C₀.gates = e1 ++ e2 ++ e3 ++ andGates ++ e5 := by
      change gs5 = _
      rw [he5, hgs4_eq]
    constructor
    · intro gt hgt
      rw [hC0_eq] at hgt
      simp only [List.mem_append] at hgt
      rcases hgt with (((h | h) | h) | h) | h
      · exact hge1 gt h
      · exact hge2 gt h
      · exact hge3 gt h
      · simp only [andGates, List.mem_map] at h
        obtain ⟨_, _, rfl⟩ := h; simp
      · exact hge5 gt h
    · rw [hC0_eq]
      simp only [List.countP_append]
      have hsum1 : (pKeys.map (fun pb => (pList pb).length)).sum = N := by
        have hpart := list_sum_filter_partition (List.finRange N) pKeys pKeyOf hpKeys_nd
          (fun u _ => hpKeys_mem (pKeyOf u))
        simpa [pList] using hpart
      have hsum2 : (rKeys.map (fun jc => (rList jc).length)).sum = N := by
        have hpart := list_sum_filter_partition (List.finRange N) rKeys rKeyOf hrKeys_nd
          (fun v _ => hrKeys_mem (rKeyOf v))
        simpa [rList] using hpart
      have hsum3 : (rKeys.map (fun jc => (xList jc).length)).sum ≤ 4 * r * 2 ^ r := by
        have hle : ∀ jc ∈ rKeys, (xList jc).length ≤ 2 * 2 ^ r := by
          intro jc _
          calc (xList jc).length = (pKeys.filter (fun pb => decide (xor (pb.1.val.testBit jc.1.val) pb.2 = jc.2))).length :=
                List.length_map _
            _ ≤ pKeys.length := List.length_filter_le _ _
            _ = 2 * 2 ^ r := hpKeys_len
        have htot := list_map_sum_le_mul rKeys (fun jc => (xList jc).length) (2 * 2 ^ r) hle
        rw [hrKeys_len] at htot
        linarith
      have hc4 : andGates.countP (fun gt => gt.inputs.length == 2) ≤ 2 * r := by
        calc andGates.countP _ ≤ andGates.length := List.countP_le_length
          _ = rKeys.length := List.length_map _
          _ = 2 * r := hrKeys_len
      have hc5 : e5.countP (fun gt => gt.inputs.length == 2) ≤ 2 * r := by
        calc e5.countP _ ≤ zWires.length := hce5
          _ = rKeys.length := by simp [zWires]
          _ = 2 * r := hrKeys_len
      have htail : 16 * (4 * r * 2 ^ r + 2 * r + 2 * r) ≤ N := by
        have h1 : 16 * (4 * r * 2 ^ r + 2 * r + 2 * r) = 64 * r * (2 ^ r + 1) := by ring
        rw [h1]
        have h2 : 2 ^ r + 1 ≤ 2 ^ (r + 1) := by
          have : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
          have : 1 ≤ 2 ^ r := Nat.one_le_pow _ _ (by omega)
          omega
        have h3 : 64 * r * (2 ^ r + 1) ≤ 64 * r * 2 ^ (r + 1) := Nat.mul_le_mul_left _ h2
        have h4 : 64 * r * 2 ^ (r + 1) = 2 ^ (r + a + 7) := by
          have : 64 = 2 ^ 6 := by decide
          rw [this, show r = 2 ^ a from rfl]
          rw [← Nat.pow_add, ← Nat.pow_add]
          congr 1; omega
        have h5 : 2 ^ (r + a + 7) ≤ 2 ^ k := by
          apply Nat.pow_le_pow_right (by omega)
          have := pow_two_ge_add_seven a ha
          omega
        exact le_trans h3 (h4 ▸ h5)
      omega
  have htable : ∀ (x y : Fin N), C₀.eval (oneEach x y) =
      xor (x.val.testBit (y.val % r)) (xor (f x) (g y)) := by
    intro x y
    set inp := oneEach x y
    have hinp : inp.length = base := oneEach_length x y
    have hwP_val : ∀ pb : Fin (2 ^ r) × Bool,
        (runGates gs1 inp).getD (wP pb) false = decide (pKeyOf x = pb) := by
      intro pb
      rw [hwP_ev pb (hpKeys_mem pb) inp hinp]
      by_cases heq : pKeyOf x = pb
      · rw [decide_eq_true heq, List.any_eq_true]
        refine ⟨x.val, ?_, ?_⟩
        · simp only [pList, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
          exact ⟨x, decide_eq_true heq, rfl⟩
        · simp only [runGates, List.foldl_nil]
          rw [oneEach_getD]
          simp [x.isLt]
      · rw [decide_eq_false heq, Bool.eq_false_iff]
        intro hany
        rw [List.any_eq_true] at hany
        obtain ⟨w, hw, htrue⟩ := hany
        simp only [pList, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
          decide_eq_true_eq] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        simp only [runGates, List.foldl_nil] at htrue
        rw [oneEach_getD] at htrue
        simp only [u.isLt, ↓reduceIte, decide_eq_true_eq] at htrue
        exact heq (by rw [← Fin.ext htrue]; exact hu)
    have hwY_val : ∀ jc : Fin r × Bool,
        (runGates gs2 inp).getD (wY jc) false = decide (rKeyOf y = jc) := by
      intro jc
      rw [hwY_ev jc (hrKeys_mem jc) inp hinp]
      by_cases heq : rKeyOf y = jc
      · rw [decide_eq_true heq, List.any_eq_true]
        refine ⟨N + y.val, ?_, ?_⟩
        · simp only [rList, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
          exact ⟨y, decide_eq_true heq, rfl⟩
        · rw [runGates_getD_prefix gs1 inp (N + y.val) (by rw [hinp]; simp only [base]; have := y.isLt; omega),
            oneEach_getD]
          have h1 : ¬ N + y.val < N := by omega
          have h2 : N + y.val < N + N := by have := y.isLt; omega
          simp [h1, h2]
      · rw [decide_eq_false heq, Bool.eq_false_iff]
        intro hany
        rw [List.any_eq_true] at hany
        obtain ⟨w, hw, htrue⟩ := hany
        simp only [rList, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
          decide_eq_true_eq] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        rw [runGates_getD_prefix gs1 inp (N + v.val) (by rw [hinp]; simp only [base]; have := v.isLt; omega),
          oneEach_getD] at htrue
        have h1 : ¬ N + v.val < N := by omega
        have h2 : N + v.val < N + N := by have := v.isLt; omega
        simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left, decide_eq_true_eq] at htrue
        exact heq (by rw [← Fin.ext htrue]; exact hv)
    have hwX_val : ∀ jc : Fin r × Bool,
        (runGates gs3 inp).getD (wX jc) false =
          decide (xor (x.val.testBit jc.1.val) (f x) = jc.2) := by
      intro jc
      rw [hwX_ev jc (hrKeys_mem jc) inp hinp]
      have hbit : (pKeyOf x).1.val.testBit jc.1.val = x.val.testBit jc.1.val := by
        dsimp [pKeyOf]
        rw [Nat.testBit_mod_two_pow]
        simp [jc.1.isLt]
      by_cases heq : xor (x.val.testBit jc.1.val) (f x) = jc.2
      · rw [decide_eq_true heq, List.any_eq_true]
        refine ⟨wP (pKeyOf x), ?_, ?_⟩
        · simp only [xList, List.mem_map, List.mem_filter, decide_eq_true_eq]
          refine ⟨pKeyOf x, ⟨hpKeys_mem _, ?_⟩, rfl⟩
          rw [hbit]; exact heq
        · rw [he2, runGates_getD_append gs1 e2 inp (wP (pKeyOf x)) (by rw [hinp]; exact hwP_lt _ (hpKeys_mem _)),
            hwP_val]
          simp
      · rw [decide_eq_false heq, Bool.eq_false_iff]
        intro hany
        rw [List.any_eq_true] at hany
        obtain ⟨w, hw, htrue⟩ := hany
        simp only [xList, List.mem_map, List.mem_filter, decide_eq_true_eq] at hw
        obtain ⟨pb, ⟨hpb, hcond⟩, rfl⟩ := hw
        rw [he2, runGates_getD_append gs1 e2 inp (wP pb) (by rw [hinp]; exact hwP_lt pb hpb),
          hwP_val] at htrue
        rw [decide_eq_true_eq] at htrue
        subst htrue
        rw [hbit] at hcond
        exact heq hcond
    have hgate_and : ∀ i (hi : i < rKeys.length),
        (runGates gs4 inp).getD (base + gs3.length + i) false =
          (decide (xor (x.val.testBit (rKeys[i].1.val)) (f x) = !rKeys[i].2) &&
           decide (rKeyOf y = rKeys[i])) := by
      intro i hi
      have hlen_and : i < andGates.length := by simp [andGates, hi]
      have hsplit : andGates = andGates.take i ++ [andGates[i]'hlen_and] ++ andGates.drop (i + 1) := by
        have h1 : andGates.take i ++ [andGates[i]'hlen_and] = andGates.take (i + 1) :=
          (List.take_succ_eq_append_getElem hlen_and).symm
        rw [h1, List.take_append_drop]
      have hlen_take : (andGates.take i).length = i := by
        rw [List.length_take, Nat.min_eq_left]; omega
      have hstep1 : (runGates gs4 inp).getD (base + gs3.length + i) false =
          (runGates ((gs3 ++ andGates.take i) ++ [andGates[i]'hlen_and]) inp).getD
            (inp.length + (gs3 ++ andGates.take i).length) false := by
        have hidx : base + gs3.length + i = inp.length + (gs3 ++ andGates.take i).length := by
          rw [hinp, List.length_append, hlen_take]; omega
        rw [hidx]
        have hgs4' : gs4 = ((gs3 ++ andGates.take i) ++ [andGates[i]'hlen_and]) ++ andGates.drop (i + 1) := by
          simp only [gs4]; conv_lhs => rw [hsplit]
          simp [List.append_assoc]
        rw [hgs4', runGates_getD_append _ (andGates.drop (i + 1)) inp _ (by
          simp only [List.length_append, List.length_singleton]; omega)]
      rw [hstep1, runGates_getD_snoc]
      have hgi : andGates[i]'hlen_and =
          ⟨GateOp.and, [wX (rKeys[i].1, !rKeys[i].2), wY rKeys[i]]⟩ := by
        simp [andGates]
      rw [hgi]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      have hmem_i : rKeys[i] ∈ rKeys := List.getElem_mem hi
      have hmem_neg : (rKeys[i].1, !rKeys[i].2) ∈ rKeys := hrKeys_mem _
      rw [runGates_getD_append gs3 (andGates.take i) inp _ (by rw [hinp]; exact hwX_lt _ hmem_neg),
        runGates_getD_append gs3 (andGates.take i) inp _ (by
          rw [hinp, he3, List.length_append]
          have := hwY_lt _ hmem_i; omega),
        hwX_val, he3, runGates_getD_append gs2 e3 inp _ (by rw [hinp]; exact hwY_lt _ hmem_i),
        hwY_val]
    change (runGates gs5 inp).getD wOut false = _
    rw [hw5_ev inp hinp]
    have hxor_iff : ∀ a1 a2 a3 : Bool, (xor a1 (xor a2 a3) = true) ↔ (xor a1 a2 = !a3) := by
      intro a1 a2 a3; cases a1 <;> cases a2 <;> cases a3 <;> decide
    by_cases hres : xor (x.val.testBit (y.val % r)) (xor (f x) (g y)) = true
    · rw [hres, List.any_eq_true]
      have hmem_y : rKeyOf y ∈ rKeys := hrKeys_mem (rKeyOf y)
      obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hmem_y
      refine ⟨base + gs3.length + i, ?_, ?_⟩
      · simp only [zWires, List.mem_map, List.mem_range]
        exact ⟨i, hi, rfl⟩
      · rw [hgate_and i hi, hri]
        simp only [decide_true, Bool.and_true, decide_eq_true_eq]
        exact (hxor_iff _ _ _).mp hres
    · have hres_f : xor (x.val.testBit (y.val % r)) (xor (f x) (g y)) = false := Bool.eq_false_iff.mpr hres
      rw [hres_f, Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨w, hw, htrue⟩ := hany
      simp only [zWires, List.mem_map, List.mem_range] at hw
      obtain ⟨i, hi, rfl⟩ := hw
      rw [hgate_and i hi, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at htrue
      obtain ⟨h1, h2⟩ := htrue
      rw [← h2] at h1
      exact hres ((hxor_iff _ _ _).mpr h1)
  refine ⟨C₀, hfits, ?_⟩
  intro D hD
  have hfilt : (Finset.univ.filter (fun z : Fin N × Fin N =>
      C₀.eval (oneEach z.1 z.2) ≠
        xor (xor (z.1.val.testBit (z.2.val % r)) (decide (Nat.xor z.1.val z.2.val ∈ D)))
          (xor (f z.1) (g z.2)))) =
      Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ D) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, htable x y]
    cases x.val.testBit (y.val % r) <;> cases f x <;> cases g y <;>
      by_cases h : Nat.xor x.val y.val ∈ D <;> simp
  rw [hfilt]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := (Finset.univ : Finset (Fin N)))
    (fun _ _ => Finset.mem_univ _)]
  have hfiber : ∀ x : Fin N,
      ((Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ D)).filter
        (fun z => z.1 = x)).card = D.card := by
    intro x
    have heq : ((Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ D)).filter
        (fun z => z.1 = x)) =
        (Finset.univ.filter (fun y : Fin N => x.val ^^^ y.val ∈ D)).map
          ⟨fun y => (x, y), fun _ _ h => congrArg Prod.snd h⟩ := by
      ext ⟨x', y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · rintro ⟨h1, rfl⟩; exact ⟨y, h1, rfl⟩
      · rintro ⟨y', h1, h2⟩
        injection h2 with hx' hy'
        subst hx'; subst hy'; exact ⟨h1, rfl⟩
    rw [heq, Finset.card_map]
    exact card_xor_mem_gamma k D (Finset.Subset.trans hD hΓ) x
  have hsum : ∑ x : Fin N,
      ((Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ D)).filter
        (fun z => z.1 = x)).card = ∑ _x : Fin N, D.card :=
    Finset.sum_congr rfl (fun x _ => hfiber x)
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

def chi (j : ℕ) (x : ℕ) : ℤ := if x.testBit j then 1 else -1

theorem chi_sq (j x : ℕ) : chi j x * chi j x = 1 := by
  unfold chi; cases x.testBit j <;> decide

theorem sum_chi_four_eq_zero (k : ℕ) (j₁ j₂ j₃ j₄ t : ℕ)
    (ht : t < k)
    (hodd : (decide (j₁ = t) ^^ decide (j₂ = t) ^^ decide (j₃ = t) ^^ decide (j₄ = t)) = true) :
    (∑ x : Fin (2 ^ k), chi j₁ x.val * chi j₂ x.val * chi j₃ x.val * chi j₄ x.val) = 0 := by
  have hmask : 2 ^ t < 2 ^ k := Nat.pow_lt_pow_right (by omega) ht
  let e : Equiv.Perm (Fin (2 ^ k)) :=
    { toFun := fun x => ⟨x.val ^^^ 2 ^ t, xor_lt_pow_two x.isLt hmask⟩
      invFun := fun x => ⟨x.val ^^^ 2 ^ t, xor_lt_pow_two x.isLt hmask⟩
      left_inv := fun x => Fin.ext (by simp)
      right_inv := fun x => Fin.ext (by simp) }
  have hchi_flip : ∀ (j : ℕ) (x : Fin (2 ^ k)),
      chi j (e x).val = if j = t then -chi j x.val else chi j x.val := by
    intro j x
    dsimp [chi, e]
    rw [Nat.testBit_xor]
    by_cases hj : j = t
    · subst hj
      rw [Nat.testBit_two_pow_self]
      simp only [↓reduceIte]
      cases x.val.testBit j <;> decide
    · rw [Nat.testBit_two_pow_of_ne (Ne.symm hj)]
      simp [hj]
  have hneg : ∀ x : Fin (2 ^ k),
      chi j₁ (e x).val * chi j₂ (e x).val * chi j₃ (e x).val * chi j₄ (e x).val =
        -(chi j₁ x.val * chi j₂ x.val * chi j₃ x.val * chi j₄ x.val) := by
    intro x
    rw [hchi_flip j₁ x, hchi_flip j₂ x, hchi_flip j₃ x, hchi_flip j₄ x]
    by_cases h1 : j₁ = t <;> by_cases h2 : j₂ = t <;> by_cases h3 : j₃ = t <;> by_cases h4 : j₄ = t
    all_goals simp only [h1, h2, h3, h4, decide_true, decide_false, ↓reduceIte] at hodd ⊢
    all_goals first | contradiction | ring
  have hsum : (∑ x : Fin (2 ^ k), chi j₁ x.val * chi j₂ x.val * chi j₃ x.val * chi j₄ x.val) =
      ∑ x : Fin (2 ^ k), chi j₁ (e x).val * chi j₂ (e x).val * chi j₃ (e x).val * chi j₄ (e x).val :=
    (Equiv.sum_comp e (fun x : Fin (2 ^ k) =>
      chi j₁ x.val * chi j₂ x.val * chi j₃ x.val * chi j₄ x.val)).symm
  have hsum2 : (∑ x : Fin (2 ^ k), chi j₁ (e x).val * chi j₂ (e x).val * chi j₃ (e x).val * chi j₄ (e x).val) =
      -(∑ x : Fin (2 ^ k), chi j₁ x.val * chi j₂ x.val * chi j₃ x.val * chi j₄ x.val) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ => hneg x)
  linarith

theorem sum_chi_four_le (k r : ℕ) (hrk : r ≤ k) (c : Fin r → ℤ) :
    (∑ x : Fin (2 ^ k), (∑ j : Fin r, c j * chi j.val x.val) ^ 4) ≤
      3 * (2 ^ k : ℤ) * (∑ j : Fin r, c j ^ 2) ^ 2 := by
  classical
  have hexp : ∀ x : Fin (2 ^ k),
      (∑ j : Fin r, c j * chi j.val x.val) ^ 4 =
      ∑ j₁ : Fin r, ∑ j₂ : Fin r, ∑ j₃ : Fin r, ∑ j₄ : Fin r,
        (c j₁ * c j₂ * c j₃ * c j₄) * (chi j₁.val x.val * chi j₂.val x.val * chi j₃.val x.val * chi j₄.val x.val) := by
    intro x
    let g : Fin r → ℤ := fun j => c j * chi j.val x.val
    have h4 : (∑ j : Fin r, g j) ^ 4 =
        ∑ j₁ : Fin r, ∑ j₂ : Fin r, ∑ j₃ : Fin r, ∑ j₄ : Fin r, g j₁ * g j₂ * g j₃ * g j₄ := by
      calc (∑ j : Fin r, g j) ^ 4
          = (∑ j : Fin r, g j) * ((∑ j : Fin r, g j) * ((∑ j : Fin r, g j) * (∑ j : Fin r, g j))) := by ring
        _ = ∑ j₁ : Fin r, g j₁ * ((∑ j : Fin r, g j) * ((∑ j : Fin r, g j) * (∑ j : Fin r, g j))) := Finset.sum_mul ..
        _ = ∑ j₁ : Fin r, ∑ j₂ : Fin r, g j₁ * (g j₂ * ((∑ j : Fin r, g j) * (∑ j : Fin r, g j))) := by
            refine Finset.sum_congr rfl fun j₁ _ => ?_
            rw [Finset.sum_mul, Finset.mul_sum]
        _ = ∑ j₁ : Fin r, ∑ j₂ : Fin r, ∑ j₃ : Fin r, g j₁ * (g j₂ * (g j₃ * (∑ j : Fin r, g j))) := by
            refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
            rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
        _ = ∑ j₁ : Fin r, ∑ j₂ : Fin r, ∑ j₃ : Fin r, ∑ j₄ : Fin r, g j₁ * g j₂ * g j₃ * g j₄ := by
            refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ =>
              Finset.sum_congr rfl fun j₃ _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j₄ _ => by ring
    rw [h4]
    refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ =>
      Finset.sum_congr rfl fun j₃ _ => Finset.sum_congr rfl fun j₄ _ => by dsimp [g]; ring
  have hswap : (∑ x : Fin (2 ^ k), (∑ j : Fin r, c j * chi j.val x.val) ^ 4) =
      ∑ j₁ : Fin r, ∑ j₂ : Fin r, ∑ j₃ : Fin r, ∑ j₄ : Fin r,
        (c j₁ * c j₂ * c j₃ * c j₄) *
          (∑ x : Fin (2 ^ k), chi j₁.val x.val * chi j₂.val x.val * chi j₃.val x.val * chi j₄.val x.val) := by
    simp_rw [hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₃ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₄ _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  have hterm : ∀ j₁ j₂ j₃ j₄ : Fin r,
      (c j₁ * c j₂ * c j₃ * c j₄) *
        (∑ x : Fin (2 ^ k), chi j₁.val x.val * chi j₂.val x.val * chi j₃.val x.val * chi j₄.val x.val) ≤
      (2 ^ k : ℤ) *
        ((if j₁ = j₂ ∧ j₃ = j₄ then c j₁ ^ 2 * c j₃ ^ 2 else 0) +
         (if j₁ = j₃ ∧ j₂ = j₄ then c j₁ ^ 2 * c j₂ ^ 2 else 0) +
         (if j₁ = j₄ ∧ j₂ = j₃ then c j₁ ^ 2 * c j₂ ^ 2 else 0)) := by
    intro j₁ j₂ j₃ j₄
    by_cases hp : (j₁ = j₂ ∧ j₃ = j₄) ∨ (j₁ = j₃ ∧ j₂ = j₄) ∨ (j₁ = j₄ ∧ j₂ = j₃)
    · have hprod_one : ∀ x : Fin (2 ^ k),
          chi j₁.val x.val * chi j₂.val x.val * chi j₃.val x.val * chi j₄.val x.val = 1 := by
        intro x
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · calc chi j₁.val x.val * chi j₁.val x.val * chi j₃.val x.val * chi j₃.val x.val
              = (chi j₁.val x.val * chi j₁.val x.val) * (chi j₃.val x.val * chi j₃.val x.val) := by ring
            _ = 1 * 1 := by rw [chi_sq, chi_sq]
            _ = 1 := one_mul 1
        · calc chi j₁.val x.val * chi j₂.val x.val * chi j₁.val x.val * chi j₂.val x.val
              = (chi j₁.val x.val * chi j₁.val x.val) * (chi j₂.val x.val * chi j₂.val x.val) := by ring
            _ = 1 * 1 := by rw [chi_sq, chi_sq]
            _ = 1 := one_mul 1
        · calc chi j₁.val x.val * chi j₂.val x.val * chi j₂.val x.val * chi j₁.val x.val
              = (chi j₁.val x.val * chi j₁.val x.val) * (chi j₂.val x.val * chi j₂.val x.val) := by ring
            _ = 1 * 1 := by rw [chi_sq, chi_sq]
            _ = 1 := one_mul 1
      have hsumN : (∑ x : Fin (2 ^ k), chi j₁.val x.val * chi j₂.val x.val * chi j₃.val x.val * chi j₄.val x.val) = (2 ^ k : ℤ) := by
        simp [hprod_one]
      rw [hsumN]
      have h2k : (0 : ℤ) ≤ (2 ^ k : ℤ) := by positivity
      have hnonneg : ∀ a b : ℤ, (0 : ℤ) ≤ a ^ 2 * b ^ 2 := fun a b => by positivity
      have hle_rhs : c j₁ * c j₂ * c j₃ * c j₄ ≤
          (if j₁ = j₂ ∧ j₃ = j₄ then c j₁ ^ 2 * c j₃ ^ 2 else 0) +
          (if j₁ = j₃ ∧ j₂ = j₄ then c j₁ ^ 2 * c j₂ ^ 2 else 0) +
          (if j₁ = j₄ ∧ j₂ = j₃ then c j₁ ^ 2 * c j₂ ^ 2 else 0) := by
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [true_and, ↓reduceIte]
          have h1 : (0 : ℤ) ≤ if j₁ = j₃ ∧ j₁ = j₃ then c j₁ ^ 2 * c j₁ ^ 2 else 0 := by split_ifs <;> positivity
          have h2 : (0 : ℤ) ≤ if j₁ = j₃ ∧ j₁ = j₃ then c j₁ ^ 2 * c j₁ ^ 2 else 0 := by split_ifs <;> positivity
          nlinarith [hnonneg (c j₁) (c j₃)]
        · simp only [true_and, ↓reduceIte]
          have h1 : (0 : ℤ) ≤ if j₁ = j₂ ∧ j₁ = j₂ then c j₁ ^ 2 * c j₁ ^ 2 else 0 := by split_ifs <;> positivity
          have h2 : (0 : ℤ) ≤ if j₁ = j₂ ∧ j₂ = j₁ then c j₁ ^ 2 * c j₂ ^ 2 else 0 := by split_ifs <;> positivity
          nlinarith [hnonneg (c j₁) (c j₂)]
        · simp only [true_and, ↓reduceIte]
          have h1 : (0 : ℤ) ≤ if j₁ = j₂ ∧ j₂ = j₁ then c j₁ ^ 2 * c j₂ ^ 2 else 0 := by split_ifs <;> positivity
          have h2 : (0 : ℤ) ≤ if j₁ = j₂ ∧ j₂ = j₁ then c j₁ ^ 2 * c j₂ ^ 2 else 0 := by split_ifs <;> positivity
          nlinarith [hnonneg (c j₁) (c j₂)]
      nlinarith
    · push Not at hp
      obtain ⟨h12, h13, h14⟩ := hp
      have hzero : (∑ x : Fin (2 ^ k), chi j₁.val x.val * chi j₂.val x.val * chi j₃.val x.val * chi j₄.val x.val) = 0 := by
        by_cases e12 : j₁ = j₂
        · have ne34 : j₃ ≠ j₄ := h12 e12
          by_cases e13 : j₁ = j₃
          · exact sum_chi_four_eq_zero k j₁.val j₂.val j₃.val j₄.val j₄.val (lt_of_lt_of_le j₄.isLt hrk)
              (by simp [e12, Fin.val_ne_of_ne ne34])
          · exact sum_chi_four_eq_zero k j₁.val j₂.val j₃.val j₄.val j₃.val (lt_of_lt_of_le j₃.isLt hrk)
              (by simp [e12, Fin.val_ne_of_ne (Ne.symm ne34)])
        · by_cases e13 : j₁ = j₃
          · have ne24 : j₂ ≠ j₄ := h13 e13
            exact sum_chi_four_eq_zero k j₁.val j₂.val j₃.val j₄.val j₂.val (lt_of_lt_of_le j₂.isLt hrk)
              (by simp [e13, Fin.val_ne_of_ne (Ne.symm ne24)])
          · by_cases e14 : j₁ = j₄
            · have ne23 : j₂ ≠ j₃ := h14 e14
              exact sum_chi_four_eq_zero k j₁.val j₂.val j₃.val j₄.val j₂.val (lt_of_lt_of_le j₂.isLt hrk)
                (by simp [e14, Fin.val_ne_of_ne (Ne.symm ne23)])
            · exact sum_chi_four_eq_zero k j₁.val j₂.val j₃.val j₄.val j₁.val (lt_of_lt_of_le j₁.isLt hrk)
                (by simp [Fin.val_ne_of_ne (Ne.symm e12), Fin.val_ne_of_ne (Ne.symm e13), Fin.val_ne_of_ne (Ne.symm e14)])
      rw [hzero, mul_zero]
      have h2k : (0 : ℤ) ≤ (2 ^ k : ℤ) := by positivity
      have h1 : (0 : ℤ) ≤ if j₁ = j₂ ∧ j₃ = j₄ then c j₁ ^ 2 * c j₃ ^ 2 else 0 := by split_ifs <;> positivity
      have h2 : (0 : ℤ) ≤ if j₁ = j₃ ∧ j₂ = j₄ then c j₁ ^ 2 * c j₂ ^ 2 else 0 := by split_ifs <;> positivity
      have h3 : (0 : ℤ) ≤ if j₁ = j₄ ∧ j₂ = j₃ then c j₁ ^ 2 * c j₂ ^ 2 else 0 := by split_ifs <;> positivity
      nlinarith
  have hsum_le : (∑ j₁ : Fin r, ∑ j₂ : Fin r, ∑ j₃ : Fin r, ∑ j₄ : Fin r,
        (c j₁ * c j₂ * c j₃ * c j₄) *
          (∑ x : Fin (2 ^ k), chi j₁.val x.val * chi j₂.val x.val * chi j₃.val x.val * chi j₄.val x.val)) ≤
      ∑ j₁ : Fin r, ∑ j₂ : Fin r, ∑ j₃ : Fin r, ∑ j₄ : Fin r,
        (2 ^ k : ℤ) *
          ((if j₁ = j₂ ∧ j₃ = j₄ then c j₁ ^ 2 * c j₃ ^ 2 else 0) +
           (if j₁ = j₃ ∧ j₂ = j₄ then c j₁ ^ 2 * c j₂ ^ 2 else 0) +
           (if j₁ = j₄ ∧ j₂ = j₃ then c j₁ ^ 2 * c j₂ ^ 2 else 0)) :=
    Finset.sum_le_sum fun j₁ _ => Finset.sum_le_sum fun j₂ _ =>
      Finset.sum_le_sum fun j₃ _ => Finset.sum_le_sum fun j₄ _ => hterm j₁ j₂ j₃ j₄
  refine le_trans hsum_le ?_
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hS1 : (∑ j₁ : Fin r, ∑ j₂ : Fin r, ∑ j₃ : Fin r, ∑ j₄ : Fin r,
      if j₁ = j₂ ∧ j₃ = j₄ then c j₁ ^ 2 * c j₃ ^ 2 else 0) = (∑ j : Fin r, c j ^ 2) ^ 2 := by
    have hinner : ∀ j₁ j₂ : Fin r, (∑ j₃ : Fin r, ∑ j₄ : Fin r,
        if j₁ = j₂ ∧ j₃ = j₄ then c j₁ ^ 2 * c j₃ ^ 2 else 0) =
        if j₁ = j₂ then c j₁ ^ 2 * (∑ j₃ : Fin r, c j₃ ^ 2) else 0 := by
      intro j₁ j₂
      by_cases h12 : j₁ = j₂
      · simp only [h12, true_and, ↓reduceIte, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j₃ _ => by simp
      · simp [h12]
    simp_rw [hinner]
    have houter : ∀ j₁ : Fin r, (∑ j₂ : Fin r, if j₁ = j₂ then c j₁ ^ 2 * ∑ j₃ : Fin r, c j₃ ^ 2 else 0) =
        c j₁ ^ 2 * ∑ j₃ : Fin r, c j₃ ^ 2 := fun j₁ => by simp
    simp_rw [houter, ← Finset.sum_mul, sq]
  have hS2 : (∑ j₁ : Fin r, ∑ j₂ : Fin r, ∑ j₃ : Fin r, ∑ j₄ : Fin r,
      if j₁ = j₃ ∧ j₂ = j₄ then c j₁ ^ 2 * c j₂ ^ 2 else 0) = (∑ j : Fin r, c j ^ 2) ^ 2 := by
    have h1 : ∀ j₁ j₂ j₃ : Fin r, (∑ j₄ : Fin r,
        if j₁ = j₃ ∧ j₂ = j₄ then c j₁ ^ 2 * c j₂ ^ 2 else 0) =
        if j₁ = j₃ then c j₁ ^ 2 * c j₂ ^ 2 else 0 := by
      intro j₁ j₂ j₃
      by_cases h : j₁ = j₃ <;> simp [h]
    simp_rw [h1]
    have h2 : ∀ j₁ j₂ : Fin r, (∑ j₃ : Fin r, if j₁ = j₃ then c j₁ ^ 2 * c j₂ ^ 2 else 0) =
        c j₁ ^ 2 * c j₂ ^ 2 := fun j₁ j₂ => by simp
    simp_rw [h2, ← Finset.mul_sum, ← Finset.sum_mul, sq]
  have hS3 : (∑ j₁ : Fin r, ∑ j₂ : Fin r, ∑ j₃ : Fin r, ∑ j₄ : Fin r,
      if j₁ = j₄ ∧ j₂ = j₃ then c j₁ ^ 2 * c j₂ ^ 2 else 0) = (∑ j : Fin r, c j ^ 2) ^ 2 := by
    have h1 : ∀ j₁ j₂ j₃ : Fin r, (∑ j₄ : Fin r,
        if j₁ = j₄ ∧ j₂ = j₃ then c j₁ ^ 2 * c j₂ ^ 2 else 0) =
        if j₂ = j₃ then c j₁ ^ 2 * c j₂ ^ 2 else 0 := by
      intro j₁ j₂ j₃
      by_cases h : j₂ = j₃ <;> simp [h]
    simp_rw [h1]
    have h2 : ∀ j₁ j₂ : Fin r, (∑ j₃ : Fin r, if j₂ = j₃ then c j₁ ^ 2 * c j₂ ^ 2 else 0) =
        c j₁ ^ 2 * c j₂ ^ 2 := fun j₁ j₂ => by simp
    simp_rw [h2, ← Finset.mul_sum, ← Finset.sum_mul, sq]
  rw [hS1, hS2, hS3]
  linarith

theorem int_sq_sum_le_card_mul_sum_sq {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℤ) * ∑ i ∈ s, f i ^ 2 := by
  have hnn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexp : (∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2) =
      2 * ((s.card : ℤ) * ∑ i ∈ s, f i ^ 2) - 2 * (∑ i ∈ s, f i) ^ 2 := by
    have h1 : ∀ i j : α, (f i - f j) ^ 2 = f i ^ 2 + f j ^ 2 - 2 * (f i * f j) :=
      fun i j => by ring
    simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul, sq]
    ring
  linarith

theorem level_one_bound (k a : ℕ) (ha : 6 ≤ a) (hk : 2 * 2 ^ a ≤ k)
    (A : Finset (Fin (2 ^ k))) (hA : 2 ^ a * A.card ≤ 2 ^ k) :
    4 * (∑ j : Fin (2 ^ a), (∑ x ∈ A, chi j.val x.val) ^ 2) ≤ (2 ^ k : ℤ) * (A.card : ℤ) := by
  let r : ℕ := 2 ^ a
  let N : ℤ := (2 ^ k : ℕ)
  let c : Fin r → ℤ := fun j => ∑ x ∈ A, chi j.val x.val
  let S : ℤ := ∑ j : Fin r, c j ^ 2
  let F : Fin (2 ^ k) → ℤ := fun x => ∑ j : Fin r, c j * chi j.val x.val
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg (c j)
  have hS_eq : S = ∑ x ∈ A, F x := by
    calc S = ∑ j : Fin r, c j * (∑ x ∈ A, chi j.val x.val) := by
          refine Finset.sum_congr rfl fun j _ => by dsimp [c]; ring
      _ = ∑ j : Fin r, ∑ x ∈ A, c j * chi j.val x.val := by
          refine Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
      _ = ∑ x ∈ A, F x := Finset.sum_comm
  have hcs1 : S ^ 2 ≤ (A.card : ℤ) * ∑ x ∈ A, F x ^ 2 := by
    rw [hS_eq]
    exact int_sq_sum_le_card_mul_sum_sq A F
  have hcs2 : (∑ x ∈ A, F x ^ 2) ^ 2 ≤ (A.card : ℤ) * ∑ x ∈ A, F x ^ 4 := by
    have h := int_sq_sum_le_card_mul_sum_sq A (fun x => F x ^ 2)
    have hpow : ∀ x : Fin (2 ^ k), (F x ^ 2) ^ 2 = F x ^ 4 := fun x => by ring
    simpa [hpow] using h
  have hF4_le : (∑ x ∈ A, F x ^ 4) ≤ ∑ x : Fin (2 ^ k), F x ^ 4 :=
    Finset.sum_le_univ_sum_of_nonneg fun x => by positivity
  have h4th : (∑ x : Fin (2 ^ k), F x ^ 4) ≤ 3 * N * S ^ 2 := by
    simpa [N, S, F] using sum_chi_four_le k r (by omega) c
  have hS4 : S ^ 4 ≤ (A.card : ℤ) ^ 3 * (3 * N * S ^ 2) := by
    have h1 : S ^ 4 ≤ ((A.card : ℤ) * ∑ x ∈ A, F x ^ 2) ^ 2 := by
      have hS2_nonneg : 0 ≤ S ^ 2 := sq_nonneg S
      calc S ^ 4 = (S ^ 2) ^ 2 := by ring
        _ ≤ ((A.card : ℤ) * ∑ x ∈ A, F x ^ 2) ^ 2 := by nlinarith
    have h2 : ((A.card : ℤ) * ∑ x ∈ A, F x ^ 2) ^ 2 = (A.card : ℤ) ^ 2 * (∑ x ∈ A, F x ^ 2) ^ 2 := by ring
    have hA2_nonneg : (0 : ℤ) ≤ (A.card : ℤ) ^ 2 := sq_nonneg _
    have hA3_nonneg : (0 : ℤ) ≤ (A.card : ℤ) ^ 3 := by positivity
    have h3 : (A.card : ℤ) ^ 2 * (∑ x ∈ A, F x ^ 2) ^ 2 ≤ (A.card : ℤ) ^ 3 * ∑ x ∈ A, F x ^ 4 := by
      calc (A.card : ℤ) ^ 2 * (∑ x ∈ A, F x ^ 2) ^ 2
          ≤ (A.card : ℤ) ^ 2 * ((A.card : ℤ) * ∑ x ∈ A, F x ^ 4) := mul_le_mul_of_nonneg_left hcs2 hA2_nonneg
        _ = (A.card : ℤ) ^ 3 * ∑ x ∈ A, F x ^ 4 := by ring
    have h4 : (A.card : ℤ) ^ 3 * ∑ x ∈ A, F x ^ 4 ≤ (A.card : ℤ) ^ 3 * (3 * N * S ^ 2) :=
      mul_le_mul_of_nonneg_left (le_trans hF4_le h4th) hA3_nonneg
    exact le_trans h1 (h2 ▸ le_trans h3 h4)
  have hS2_le : S ^ 2 ≤ 3 * N * (A.card : ℤ) ^ 3 := by
    by_cases hS0 : S = 0
    · rw [hS0]; positivity
    · have hS2_pos : 0 < S ^ 2 := by positivity
      have h4' : S ^ 2 * S ^ 2 ≤ S ^ 2 * (3 * N * (A.card : ℤ) ^ 3) := by linarith
      exact le_of_mul_le_mul_left h4' hS2_pos
  have hr64 : (64 : ℤ) ≤ (r : ℤ) := by
    have : 64 ≤ 2 ^ a := le_trans (by decide : 64 ≤ 2 ^ 6) (Nat.pow_le_pow_right (by omega) ha)
    exact_mod_cast this
  have hAr : (r : ℤ) * (A.card : ℤ) ≤ N := by
    have : ((r * A.card : ℕ) : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := Int.ofNat_le.mpr hA
    simpa [N, Int.natCast_mul] using this
  have hsq : (4 * S) ^ 2 ≤ (N * (A.card : ℤ)) ^ 2 := by
    have h1 : (64 : ℤ) * S ^ 2 ≤ (r : ℤ) * S ^ 2 := mul_le_mul_of_nonneg_right hr64 (sq_nonneg S)
    have h2 : (r : ℤ) * S ^ 2 ≤ (r : ℤ) * (3 * N * (A.card : ℤ) ^ 3) :=
      mul_le_mul_of_nonneg_left hS2_le (by positivity)
    have h3 : (r : ℤ) * (3 * N * (A.card : ℤ) ^ 3) = 3 * N * ((r : ℤ) * (A.card : ℤ)) * (A.card : ℤ) ^ 2 := by ring
    have h4 : 3 * N * ((r : ℤ) * (A.card : ℤ)) * (A.card : ℤ) ^ 2 ≤ 3 * N * N * (A.card : ℤ) ^ 2 := by
      have hnn : (0 : ℤ) ≤ 3 * N * (A.card : ℤ) ^ 2 := by positivity
      nlinarith
    have h5 : (4 * S) ^ 2 = 16 * S ^ 2 := by ring
    have h6 : (N * (A.card : ℤ)) ^ 2 = N * N * (A.card : ℤ) ^ 2 := by ring
    nlinarith
  have hNA_nonneg : 0 ≤ N * (A.card : ℤ) := by positivity
  have hfinal : 4 * S ≤ N * (A.card : ℤ) := by nlinarith
  simpa [S, N, c] using hfinal

theorem base_asym_lower (k a : ℕ) (ha : 6 ≤ a) (hk : 2 * 2 ^ a ≤ k)
    (π : Equiv.Perm (Fin (2 ^ k))) (U : Finset (Fin (2 ^ k))) :
    let r : ℕ := 2 ^ a
    let N : ℕ := 2 ^ k
    (4 * (U.card : ℤ) * (U.card : ℤ)) - (N : ℤ) * (U.card : ℤ) ≤
      8 * (((U ×ˢ U).filter (fun z : Fin N × Fin N =>
        z.1.val.testBit ((π z.2).val % r) ≠ z.2.val.testBit ((π z.1).val % r))).card : ℤ) := by
  classical
  dsimp only
  let r : ℕ := 2 ^ a
  let N : ℕ := 2 ^ k
  have hak : a ≤ k := by have := pow_two_ge_add_seven a ha; omega
  let Ui : Fin r → Finset (Fin N) := fun i => U.filter (fun x => (π x).val % r = i.val)
  let A : Fin r → Fin r → ℤ := fun i j => ∑ x ∈ Ui i, chi j.val x.val
  have hUi_le : ∀ i : Fin r, r * (Ui i).card ≤ N := by
    intro i
    have hsub : (Ui i).image π ⊆ Finset.univ.filter (fun y : Fin N => y.val % r = i.val) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ π.injective, card_mod_eq k a hak i.val i.isLt] at hcard
    have hpow : 2 ^ a * 2 ^ (k - a) = 2 ^ k := by rw [← Nat.pow_add, Nat.add_sub_cancel' hak]
    have hmul := Nat.mul_le_mul_left r hcard
    change 2 ^ a * (Ui i).card ≤ 2 ^ k
    rw [← hpow]
    exact hmul
  have hUi_sum : ∑ i : Fin r, (Ui i).card = U.card := by
    rw [show U.card = ∑ i : Fin r, (U.filter (fun x =>
      (⟨(π x).val % r, Nat.mod_lt _ (Nat.pow_pos (by omega))⟩ : Fin r) = i)).card from
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg Finset.card (by ext x; simp [Ui, Fin.ext_iff])
  have hsumA2 : 4 * (∑ i : Fin r, ∑ j : Fin r, A i j ^ 2) ≤ (N : ℤ) * (U.card : ℤ) := by
    have h1 : ∀ i : Fin r, 4 * (∑ j : Fin r, A i j ^ 2) ≤ (N : ℤ) * ((Ui i).card : ℤ) :=
      fun i => by simpa [A, N] using level_one_bound k a ha hk (Ui i) (hUi_le i)
    calc 4 * (∑ i : Fin r, ∑ j : Fin r, A i j ^ 2)
        = ∑ i : Fin r, 4 * (∑ j : Fin r, A i j ^ 2) := Finset.mul_sum _ _ _
      _ ≤ ∑ i : Fin r, (N : ℤ) * ((Ui i).card : ℤ) := Finset.sum_le_sum fun i _ => h1 i
      _ = (N : ℤ) * ∑ i : Fin r, ((Ui i).card : ℤ) := (Finset.mul_sum _ _ _).symm
      _ = (N : ℤ) * (U.card : ℤ) := by
          congr 1
          exact_mod_cast hUi_sum
  have hcross : (∑ i : Fin r, ∑ j : Fin r, A i j * A j i) ≤ ∑ i : Fin r, ∑ j : Fin r, A i j ^ 2 := by
    have hsq : 0 ≤ ∑ i : Fin r, ∑ j : Fin r, (A i j - A j i) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hexp : (∑ i : Fin r, ∑ j : Fin r, (A i j - A j i) ^ 2) =
        2 * (∑ i : Fin r, ∑ j : Fin r, A i j ^ 2) - 2 * (∑ i : Fin r, ∑ j : Fin r, A i j * A j i) := by
      have h1 : ∀ i j : Fin r, (A i j - A j i) ^ 2 = A i j ^ 2 + A j i ^ 2 - 2 * (A i j * A j i) :=
        fun i j => by ring
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hsym : (∑ i : Fin r, ∑ j : Fin r, A j i ^ 2) = ∑ i : Fin r, ∑ j : Fin r, A i j ^ 2 :=
        Finset.sum_comm
      rw [hsym]
      ring
    linarith
  have hpair_sum : (∑ z ∈ U ×ˢ U, chi ((π z.2).val % r) z.1.val * chi ((π z.1).val % r) z.2.val) =
      ∑ i : Fin r, ∑ j : Fin r, A i j * A j i := by
    have hprod : ∀ i j : Fin r, A i j * A j i =
        ∑ x ∈ Ui i, ∑ y ∈ Ui j, chi j.val x.val * chi i.val y.val := by
      intro i j
      dsimp [A]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
    simp_rw [hprod]
    have hUeq : U = Finset.univ.biUnion Ui := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Ui, Finset.mem_filter]
      constructor
      · intro hx; exact ⟨⟨(π x).val % r, Nat.mod_lt _ (Nat.pow_pos (by omega))⟩, hx, rfl⟩
      · rintro ⟨_, hx, _⟩; exact hx
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin r))) Ui := by
      intro i _ j _ hij
      change Disjoint (Ui i) (Ui j)
      rw [Finset.disjoint_left]
      intro x hxi hxj
      exact hij (Fin.ext ((Finset.mem_filter.mp hxi).2.symm.trans (Finset.mem_filter.mp hxj).2))
    rw [Finset.sum_product]
    dsimp only
    calc (∑ x ∈ U, ∑ y ∈ U, chi ((π y).val % r) x.val * chi ((π x).val % r) y.val)
        = ∑ i : Fin r, ∑ x ∈ Ui i, ∑ y ∈ U, chi ((π y).val % r) x.val * chi ((π x).val % r) y.val := by
          have hstep : (∑ x ∈ U, ∑ y ∈ U, chi ((π y).val % r) x.val * chi ((π x).val % r) y.val) =
              ∑ x ∈ Finset.univ.biUnion Ui, ∑ y ∈ U, chi ((π y).val % r) x.val * chi ((π x).val % r) y.val := by
            congr 1
          rw [hstep]
          exact Finset.sum_biUnion hdisj
      _ = ∑ i : Fin r, ∑ x ∈ Ui i, ∑ j : Fin r, ∑ y ∈ Ui j, chi j.val x.val * chi i.val y.val := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x hx => ?_
          have hxi : (π x).val % r = i.val := (Finset.mem_filter.mp hx).2
          conv_lhs => rw [hUeq]
          rw [Finset.sum_biUnion hdisj]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y hy => ?_
          have hyj : (π y).val % r = j.val := (Finset.mem_filter.mp hy).2
          rw [hxi, hyj]
      _ = ∑ i : Fin r, ∑ j : Fin r, ∑ x ∈ Ui i, ∑ y ∈ Ui j, chi j.val x.val * chi i.val y.val := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hdiff_id : (2 : ℤ) * (((U ×ˢ U).filter (fun z : Fin N × Fin N =>
        z.1.val.testBit ((π z.2).val % r) ≠ z.2.val.testBit ((π z.1).val % r))).card : ℤ) =
      (U.card : ℤ) * (U.card : ℤ) -
        ∑ z ∈ U ×ˢ U, chi ((π z.2).val % r) z.1.val * chi ((π z.1).val % r) z.2.val := by
    have hpoint : ∀ z : Fin N × Fin N,
        (1 - chi ((π z.2).val % r) z.1.val * chi ((π z.1).val % r) z.2.val : ℤ) =
        if z.1.val.testBit ((π z.2).val % r) ≠ z.2.val.testBit ((π z.1).val % r) then 2 else 0 := by
      intro z
      dsimp [chi]
      cases z.1.val.testBit ((π z.2).val % r) <;> cases z.2.val.testBit ((π z.1).val % r) <;> decide
    have hsum := Finset.sum_congr rfl (fun z (_ : z ∈ U ×ˢ U) => hpoint z)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_product, nsmul_eq_mul, mul_one,
      Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul] at hsum
    push_cast at hsum
    linarith
  linarith

theorem powersetCard_mem_count {α : Type*} [DecidableEq α] (Γ : Finset α) (t : ℕ) (d : α) (hd : d ∈ Γ) :
    Γ.card * ((Γ.powersetCard t).filter (fun D => d ∈ D)).card = t * (Γ.powersetCard t).card := by
  classical
  have hsum : ∑ x ∈ Γ, ((Γ.powersetCard t).filter (fun D => x ∈ D)).card =
      t * (Γ.powersetCard t).card := by
    calc ∑ x ∈ Γ, ((Γ.powersetCard t).filter (fun D => x ∈ D)).card
        = ∑ x ∈ Γ, ∑ D ∈ Γ.powersetCard t, if x ∈ D then 1 else 0 := by
          refine Finset.sum_congr rfl fun x _ => by rw [Finset.card_filter]
      _ = ∑ D ∈ Γ.powersetCard t, ∑ x ∈ Γ, if x ∈ D then 1 else 0 := Finset.sum_comm
      _ = ∑ D ∈ Γ.powersetCard t, t := by
          refine Finset.sum_congr rfl fun D hD => ?_
          obtain ⟨hDsub, hDcard⟩ := Finset.mem_powersetCard.mp hD
          rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hDsub, hDcard]
      _ = (Γ.powersetCard t).card * t := by rw [Finset.sum_const, smul_eq_mul]
      _ = t * (Γ.powersetCard t).card := Nat.mul_comm _ _
  have hconst : ∀ x ∈ Γ, ((Γ.powersetCard t).filter (fun D => x ∈ D)).card =
      ((Γ.powersetCard t).filter (fun D => d ∈ D)).card := by
    intro x hx
    let sw := Equiv.swap x d
    apply Finset.card_bij (fun D _ => D.map sw.toEmbedding)
    · intro D hD
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hD ⊢
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
        by_cases hzx : z = x
        · subst hzx; simpa [sw] using hd
        · by_cases hzd : z = d
          · subst hzd; simpa [sw] using hx
          · simp [sw, Equiv.swap_apply_of_ne_of_ne hzx hzd]; exact hD.1.1 hz
      · rw [Finset.card_map]; exact hD.1.2
      · rw [Finset.mem_map]
        exact ⟨x, hD.2, by simp [sw]⟩
    · intro D₁ _ D₂ _ heq
      ext y
      have hmem := congrArg (fun S => sw y ∈ S) heq
      simp only [Finset.mem_map, Equiv.coe_toEmbedding] at hmem
      have h1 : (∃ a ∈ D₁, sw a = sw y) ↔ y ∈ D₁ := ⟨fun ⟨a, ha, h⟩ => sw.injective h ▸ ha, fun hy => ⟨y, hy, rfl⟩⟩
      have h2 : (∃ a ∈ D₂, sw a = sw y) ↔ y ∈ D₂ := ⟨fun ⟨a, ha, h⟩ => sw.injective h ▸ ha, fun hy => ⟨y, hy, rfl⟩⟩
      exact h1.symm.trans (eq_iff_iff.mp hmem |>.trans h2)
    · intro D hD
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hD
      refine ⟨D.map sw.toEmbedding, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro y hy
          obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
          by_cases hzx : z = x
          · subst hzx; simpa [sw] using hd
          · by_cases hzd : z = d
            · subst hzd; simpa [sw] using hx
            · simp [sw, Equiv.swap_apply_of_ne_of_ne hzx hzd]; exact hD.1.1 hz
        · rw [Finset.card_map]; exact hD.1.2
        · rw [Finset.mem_map]
          exact ⟨d, hD.2, by simp [sw]⟩
      · ext y
        simp only [Finset.mem_map, Equiv.coe_toEmbedding]
        constructor
        · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩; simpa [sw] using hb
        · intro hy; exact ⟨sw y, ⟨y, hy, rfl⟩, by simp [sw]⟩
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at hsum
  exact hsum

theorem loss_powersetCard_avg (k a : ℕ) (Γ : Finset ℕ) (hΓ : Γ ⊆ Finset.range (2 ^ k))
    (f g : Fin (2 ^ k) → Bool) (t : ℕ) (ht : t ≤ Γ.card)
    (H : Fin (2 ^ k) → Fin (2 ^ k) → Bool) :
    let N := 2 ^ k
    let r := 2 ^ a
    let I := Fin N
    let target := fun (D : Finset ℕ) (x y : I) =>
      xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
    let loss := fun (M : I → I → Bool) (D : Finset ℕ) =>
      (Finset.univ.filter (fun z : I × I => M z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2)))).card
    let sets := Γ.powersetCard t
    let Q := Γ.card
    (sets.card * (N * min t (Q - t)) ≤ ∑ D ∈ sets, loss H D) ∧
    (Q < 2 * t → sets.card * (Q * (N * (Q - t)) + (2 * t - Q) * loss H Γ) ≤ Q * ∑ D ∈ sets, loss H D) := by
  classical
  dsimp only
  let N : ℕ := 2 ^ k
  let r : ℕ := 2 ^ a
  let Q : ℕ := Γ.card
  let sets : Finset (Finset ℕ) := Γ.powersetCard t
  let baseM : Fin N → Fin N → Bool := fun x y => xor (x.val.testBit (y.val % r)) (xor (f x) (g y))
  let target : Finset ℕ → Fin N → Fin N → Bool := fun D x y =>
    xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
  let loss : (Fin N → Fin N → Bool) → Finset ℕ → ℕ := fun M D =>
    (Finset.univ.filter (fun z : Fin N × Fin N => M z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2)))).card
  change (sets.card * (N * min t (Q - t)) ≤ ∑ D ∈ sets, loss H D) ∧
    (Q < 2 * t → sets.card * (Q * (N * (Q - t)) + (2 * t - Q) * loss H Γ) ≤ Q * ∑ D ∈ sets, loss H D)
  have hpoint : ∀ (D : Finset ℕ) (z : Fin N × Fin N),
      (H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2))) ↔
        (if Nat.xor z.1.val z.2.val ∈ D then H z.1 z.2 = baseM z.1 z.2 else H z.1 z.2 ≠ baseM z.1 z.2) := by
    intro D ⟨x, y⟩
    dsimp [target, baseM]
    by_cases hd : x.val ^^^ y.val ∈ D
    · rw [ite_eq_left_iff.mpr (fun hn => absurd hd hn), decide_eq_true hd]
      cases H x y <;> cases x.val.testBit (y.val % r) <;> cases f x <;> cases g y <;> decide
    · rw [ite_eq_right_iff.mpr (fun hm => absurd hm hd), decide_eq_false hd]
      cases H x y <;> cases x.val.testBit (y.val % r) <;> cases f x <;> cases g y <;> decide
  have hsum_swap : Q * ∑ D ∈ sets, loss H D =
      ∑ z : Fin N × Fin N,
        if Nat.xor z.1.val z.2.val ∈ Γ then
          (if H z.1 z.2 = baseM z.1 z.2 then t * sets.card else (Q - t) * sets.card)
        else
          (if H z.1 z.2 ≠ baseM z.1 z.2 then Q * sets.card else 0) := by
    have h1 : ∑ D ∈ sets, loss H D =
        ∑ z : Fin N × Fin N, (sets.filter (fun D => H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2)))).card := by
      calc ∑ D ∈ sets, loss H D
          = ∑ D ∈ sets, ∑ z : Fin N × Fin N,
              if H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2)) then 1 else 0 := by
            refine Finset.sum_congr rfl fun D _ => by dsimp [loss]; rw [Finset.card_filter]
        _ = ∑ z : Fin N × Fin N, ∑ D ∈ sets,
              if H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2)) then 1 else 0 := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun z _ => by rw [Finset.card_filter]
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : Nat.xor z.1.val z.2.val ∈ Γ
    · rw [ite_eq_left_iff.mpr (fun hn => absurd hz hn)]
      have hcnt : Q * (sets.filter (fun D => Nat.xor z.1.val z.2.val ∈ D)).card = t * sets.card :=
        powersetCard_mem_count Γ t (Nat.xor z.1.val z.2.val) hz
      by_cases hH : H z.1 z.2 = baseM z.1 z.2
      · rw [ite_eq_left_iff.mpr (fun hn => absurd hH hn)]
        have hf : sets.filter (fun D => H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2))) =
            sets.filter (fun D => Nat.xor z.1.val z.2.val ∈ D) := by
          ext D
          simp only [Finset.mem_filter, and_congr_right_iff]
          intro _
          rw [hpoint D z]
          by_cases hd : Nat.xor z.1.val z.2.val ∈ D
          · rw [ite_eq_left_iff.mpr (fun hn => absurd hd hn)]; exact iff_of_true hH hd
          · rw [ite_eq_right_iff.mpr (fun hm => absurd hm hd)]; exact iff_of_false (not_not.mpr hH) hd
        rw [hf]; exact hcnt
      · rw [ite_eq_right_iff.mpr (fun hm => absurd hm hH)]
        have hf : sets.filter (fun D => H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2))) =
            sets.filter (fun D => Nat.xor z.1.val z.2.val ∉ D) := by
          ext D
          simp only [Finset.mem_filter, and_congr_right_iff]
          intro _
          rw [hpoint D z]
          by_cases hd : Nat.xor z.1.val z.2.val ∈ D
          · rw [ite_eq_left_iff.mpr (fun hn => absurd hd hn)]; exact iff_of_false hH (not_not.mpr hd)
          · rw [ite_eq_right_iff.mpr (fun hm => absurd hm hd)]; exact iff_of_true hH hd
        rw [hf]
        have htot : (sets.filter (fun D => Nat.xor z.1.val z.2.val ∈ D)).card +
            (sets.filter (fun D => Nat.xor z.1.val z.2.val ∉ D)).card = sets.card := by
          have hd : Disjoint (sets.filter (fun D => Nat.xor z.1.val z.2.val ∈ D))
              (sets.filter (fun D => Nat.xor z.1.val z.2.val ∉ D)) := by
            rw [Finset.disjoint_filter]; intro _ _ h1 h2; exact h2 h1
          have hu : sets.filter (fun D => Nat.xor z.1.val z.2.val ∈ D) ∪
              sets.filter (fun D => Nat.xor z.1.val z.2.val ∉ D) = sets := by
            ext D
            simp only [Finset.mem_union, Finset.mem_filter]
            exact ⟨fun h => h.elim And.left And.left, fun hD =>
              (em (Nat.xor z.1.val z.2.val ∈ D)).elim (fun hm => Or.inl ⟨hD, hm⟩) (fun hm => Or.inr ⟨hD, hm⟩)⟩
          rw [← Finset.card_union_of_disjoint hd, hu]
        have hmul : Q * (sets.filter (fun D => Nat.xor z.1.val z.2.val ∈ D)).card +
            Q * (sets.filter (fun D => Nat.xor z.1.val z.2.val ∉ D)).card = Q * sets.card := by
          rw [← Nat.mul_add, htot]
        have hsub : (Q - t) * sets.card + t * sets.card = Q * sets.card := by
          rw [← Nat.add_mul, Nat.sub_add_cancel ht]
        omega
    · rw [ite_eq_right_iff.mpr (fun hm => absurd hm hz)]
      have hnot : ∀ D ∈ sets, Nat.xor z.1.val z.2.val ∉ D := fun D hD hmem =>
        hz ((Finset.mem_powersetCard.mp hD).1 hmem)
      by_cases hH : H z.1 z.2 ≠ baseM z.1 z.2
      · rw [ite_eq_left_iff.mpr (fun hn => absurd hH hn)]
        have hf : sets.filter (fun D => H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2))) = sets := by
          ext D
          simp only [Finset.mem_filter, and_iff_left_iff_imp]
          intro hD
          rw [hpoint D z, ite_eq_right_iff.mpr (fun hm => absurd hm (hnot D hD))]
          exact hH
        rw [hf]
      · rw [ite_eq_right_iff.mpr (fun hm => absurd hm hH)]
        have hf : sets.filter (fun D => H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2))) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro D hD
          rw [hpoint D z, ite_eq_right_iff.mpr (fun hm => absurd hm (hnot D hD))]
          exact hH
        rw [hf, Finset.card_empty, Nat.mul_zero]
  have hGamma_pairs : (Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ Γ)).card = N * Q := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := (Finset.univ : Finset (Fin N)))
      (fun _ _ => Finset.mem_univ _)]
    have hfib : ∀ x : Fin N,
        ((Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ Γ)).filter
          (fun z => z.1 = x)).card = Q := by
      intro x
      have heq : ((Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ Γ)).filter
          (fun z => z.1 = x)) =
          (Finset.univ.filter (fun y : Fin N => x.val ^^^ y.val ∈ Γ)).map
            ⟨fun y => (x, y), fun _ _ h => congrArg Prod.snd h⟩ := by
        ext ⟨x', y⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
        constructor
        · rintro ⟨h1, rfl⟩; exact ⟨y, h1, rfl⟩
        · rintro ⟨y', h1, h2⟩
          injection h2 with hx' hy'
          subst hx'; subst hy'; exact ⟨h1, rfl⟩
      rw [heq, Finset.card_map]
      exact card_xor_mem_gamma k Γ hΓ x
    rw [Finset.sum_congr rfl (fun x _ => hfib x), Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  constructor
  · by_cases hQ0 : Q = 0
    · have ht0 : t = 0 := by omega
      simp [hQ0, ht0]
    · have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
      have hterm : ∀ z : Fin N × Fin N,
          (if Nat.xor z.1.val z.2.val ∈ Γ then min t (Q - t) * sets.card else 0) ≤
          (if Nat.xor z.1.val z.2.val ∈ Γ then
            (if H z.1 z.2 = baseM z.1 z.2 then t * sets.card else (Q - t) * sets.card)
          else
            (if H z.1 z.2 ≠ baseM z.1 z.2 then Q * sets.card else 0)) := by
        intro z
        split_ifs
        · exact Nat.mul_le_mul_right _ (min_le_left _ _)
        · exact Nat.mul_le_mul_right _ (min_le_right _ _)
        · omega
        · omega
      have hle := Finset.sum_le_sum fun z (_ : z ∈ (Finset.univ : Finset (Fin N × Fin N))) => hterm z
      rw [← hsum_swap, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
        smul_eq_mul, hGamma_pairs] at hle
      have hmul : Q * (sets.card * (N * min t (Q - t))) ≤ Q * ∑ D ∈ sets, loss H D := by
        calc Q * (sets.card * (N * min t (Q - t)))
            = N * Q * (min t (Q - t) * sets.card) := by ring
          _ ≤ Q * ∑ D ∈ sets, loss H D := hle
      exact Nat.le_of_mul_le_mul_left hmul hQpos
  · intro hQt
    have hterm : ∀ z : Fin N × Fin N,
        (if Nat.xor z.1.val z.2.val ∈ Γ then (Q - t) * sets.card else 0) +
        (if H z.1 z.2 ≠ xor (target Γ z.1 z.2) (xor (f z.1) (g z.2)) then (2 * t - Q) * sets.card else 0) ≤
        (if Nat.xor z.1.val z.2.val ∈ Γ then
          (if H z.1 z.2 = baseM z.1 z.2 then t * sets.card else (Q - t) * sets.card)
        else
          (if H z.1 z.2 ≠ baseM z.1 z.2 then Q * sets.card else 0)) := by
      intro z
      have hp := hpoint Γ z
      by_cases hz : Nat.xor z.1.val z.2.val ∈ Γ
      · rw [ite_eq_left_iff.mpr (fun hn => absurd hz hn)] at hp
        rw [ite_eq_left_iff.mpr (fun hn => absurd hz hn), ite_eq_left_iff.mpr (fun hn => absurd hz hn)]
        by_cases hH : H z.1 z.2 = baseM z.1 z.2
        · have hne : H z.1 z.2 ≠ xor (target Γ z.1 z.2) (xor (f z.1) (g z.2)) := hp.mpr hH
          rw [ite_eq_left_iff.mpr (fun hn => absurd hne hn), ite_eq_left_iff.mpr (fun hn => absurd hH hn)]
          have : (Q - t) * sets.card + (2 * t - Q) * sets.card = t * sets.card := by
            rw [← Nat.add_mul]; congr 1; omega
          omega
        · have hne : ¬ (H z.1 z.2 ≠ xor (target Γ z.1 z.2) (xor (f z.1) (g z.2))) := fun h => hH (hp.mp h)
          rw [ite_eq_right_iff.mpr (fun hm => absurd hm hne), ite_eq_right_iff.mpr (fun hm => absurd hm hH), add_zero]
      · rw [ite_eq_right_iff.mpr (fun hm => absurd hm hz)] at hp
        rw [ite_eq_right_iff.mpr (fun hm => absurd hm hz), ite_eq_right_iff.mpr (fun hm => absurd hm hz), zero_add]
        by_cases hH : H z.1 z.2 ≠ baseM z.1 z.2
        · have hne : H z.1 z.2 ≠ xor (target Γ z.1 z.2) (xor (f z.1) (g z.2)) := hp.mpr hH
          rw [ite_eq_left_iff.mpr (fun hn => absurd hne hn), ite_eq_left_iff.mpr (fun hn => absurd hH hn)]
          exact Nat.mul_le_mul_right _ (by omega)
        · have hne : ¬ (H z.1 z.2 ≠ xor (target Γ z.1 z.2) (xor (f z.1) (g z.2))) := fun h => hH (hp.mp h)
          rw [ite_eq_right_iff.mpr (fun hm => absurd hm hne), ite_eq_right_iff.mpr (fun hm => absurd hm hH)]
    have hle := Finset.sum_le_sum fun z (_ : z ∈ (Finset.univ : Finset (Fin N × Fin N))) => hterm z
    rw [← hsum_swap, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
      smul_eq_mul, hGamma_pairs, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul] at hle
    have hlhs : sets.card * (Q * (N * (Q - t)) + (2 * t - Q) * loss H Γ) =
        N * Q * ((Q - t) * sets.card) + loss H Γ * ((2 * t - Q) * sets.card) := by ring
    rw [hlhs]
    exact hle

namespace Lit

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_eq_one_iff (b : Bool) : b2z b = 1 ↔ b = true := by
  cases b <;> decide

theorem b2z_foldl_xor {α : Type*} (l : List α) (f : α → Bool) (init : Bool) :
    b2z (l.foldl (fun acc x => xor acc (f x)) init) =
      b2z init + (l.map (fun x => b2z (f x))).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, b2z_xor]
    ring

theorem list_map_sum_eq_finset_sum {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (l : List α) (hnd : l.Nodup) (f : α → β) :
    (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simp [hnd.1]), ih hnd.2]

theorem poly_add_self (p : Polynomial (ZMod 2)) : p + p = 0 := by
  ext j
  rw [Polynomial.coeff_add, Polynomial.coeff_zero]
  have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
  exact h2 (p.coeff j)

theorem poly_add_sq (a b : Polynomial (ZMod 2)) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have h : (a + b) ^ 2 = a ^ 2 + (a * b + a * b) + b ^ 2 := by ring
  rw [h, poly_add_self, add_zero]

theorem poly_sum_sq {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Polynomial (ZMod 2)) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, (f i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, poly_add_sq, ih, Finset.sum_insert ha]

theorem sum_modByMonic {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Polynomial (ZMod 2))
    (P : Polynomial (ZMod 2)) :
    (∑ i ∈ s, f i) %ₘ P = ∑ i ∈ s, (f i) %ₘ P := by
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.zero_modByMonic]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Polynomial.add_modByMonic, ih, Finset.sum_insert ha]

def allPairs (m : ℕ) : List (Fin m × Fin m) :=
  (List.finRange m).flatMap (fun i => (List.finRange m).map (fun j => (i, j)))

theorem allPairs_length (m : ℕ) : (allPairs m).length = m * m := by
  unfold allPairs
  rw [List.length_flatMap]
  have hmap : List.map (fun i : Fin m => (List.map (fun j : Fin m => (i, j)) (List.finRange m)).length)
      (List.finRange m) = List.replicate m m := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2; simp
  rw [hmap, List.sum_replicate, smul_eq_mul]

theorem allPairs_nodup (m : ℕ) : (allPairs m).Nodup := by
  unfold allPairs
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => (List.nodup_finRange m).map (fun _ _ h => (Prod.mk.inj h).2), ?_⟩
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab p h1 h2
  simp only [List.mem_map] at h1 h2
  obtain ⟨_, _, rfl⟩ := h1
  obtain ⟨_, _, h2'⟩ := h2
  have heq := (Prod.mk.inj h2').1
  have hval := congrArg Fin.val heq
  simp only [List.getElem_finRange, Fin.val_cast] at hval
  omega

theorem mem_allPairs (m : ℕ) (p : Fin m × Fin m) : p ∈ allPairs m := by
  unfold allPairs
  rw [List.mem_flatMap]
  exact ⟨p.1, List.mem_finRange p.1, List.mem_map.mpr ⟨p.2, List.mem_finRange p.2, rfl⟩⟩

def pairsFor (m t : ℕ) : List (Fin m × Fin m) :=
  (allPairs m).filter (fun ij => decide (ij.1.val + 2 * ij.2.val = t))

theorem pairsFor_nodup (m t : ℕ) : (pairsFor m t).Nodup :=
  (allPairs_nodup m).filter _

theorem sum_pairsFor_length (m : ℕ) :
    ((List.finRange (3 * m)).map (fun t => (pairsFor m t.val).length)).sum = m * m := by
  let key : Fin m × Fin m → Fin (3 * m) := fun ij => ⟨ij.1.val + 2 * ij.2.val, by omega⟩
  have hpart := list_sum_filter_partition (allPairs m) (List.finRange (3 * m)) key
    (List.nodup_finRange (3 * m)) (fun _ _ => List.mem_finRange _)
  rw [allPairs_length] at hpart
  rw [← hpart]
  congr 1

def pBit (m u t : ℕ) : Bool :=
  (pairsFor m t).foldl (fun acc ij => xor acc (u.testBit ij.1.val && u.testBit ij.2.val)) false

theorem toPoly_cube_eq (m u : ℕ) :
    (toPoly m u) ^ 3 =
      ∑ t : Fin (3 * m), if pBit m u t.val then Polynomial.X ^ t.val else 0 := by
  classical
  have hsq : (toPoly m u) ^ 2 =
      ∑ j : Fin m, if u.testBit j.val then Polynomial.X ^ (2 * j.val) else 0 := by
    unfold toPoly
    rw [poly_sum_sq]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases u.testBit j.val
    · simp
    · simp only [↓reduceIte]; ring
  have hcube : (toPoly m u) ^ 3 =
      ∑ ij : Fin m × Fin m,
        if u.testBit ij.1.val && u.testBit ij.2.val then
          Polynomial.X ^ (ij.1.val + 2 * ij.2.val)
        else 0 := by
    have h3 : (toPoly m u) ^ 3 = toPoly m u * (toPoly m u) ^ 2 := by ring
    rw [h3, hsq]
    unfold toPoly
    rw [Finset.sum_mul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases u.testBit i.val <;> cases u.testBit j.val <;> simp [pow_add]
  rw [hcube]
  let f : Fin m × Fin m → Fin (3 * m) := fun ij => ⟨ij.1.val + 2 * ij.2.val, by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := (Finset.univ : Finset (Fin (3 * m))))
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hterm : ∀ ij ∈ Finset.univ.filter (fun ij : Fin m × Fin m => f ij = t),
      (if u.testBit ij.1.val && u.testBit ij.2.val then
        (Polynomial.X : Polynomial (ZMod 2)) ^ (ij.1.val + 2 * ij.2.val)
      else 0) =
      Polynomial.C (b2z (u.testBit ij.1.val && u.testBit ij.2.val)) * Polynomial.X ^ t.val := by
    intro ij hij
    have hf : ij.1.val + 2 * ij.2.val = t.val := congrArg Fin.val (Finset.mem_filter.mp hij).2
    rw [hf]
    cases u.testBit ij.1.val && u.testBit ij.2.val <;> simp [b2z]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]
  have hset : (pairsFor m t.val).toFinset =
      Finset.univ.filter (fun ij : Fin m × Fin m => f ij = t) := by
    ext ij
    simp only [List.mem_toFinset, pairsFor, List.mem_filter, mem_allPairs, true_and,
      decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, f, Fin.ext_iff]
  have hsum_eq : (∑ ij ∈ Finset.univ.filter (fun ij : Fin m × Fin m => f ij = t),
      b2z (u.testBit ij.1.val && u.testBit ij.2.val)) = b2z (pBit m u t.val) := by
    rw [← hset, ← list_map_sum_eq_finset_sum _ (pairsFor_nodup m t.val)]
    have hb := b2z_foldl_xor (pairsFor m t.val) (fun ij => u.testBit ij.1.val && u.testBit ij.2.val) false
    unfold pBit
    rw [hb]
    simp [b2z]
  rw [hsum_eq]
  cases pBit m u t.val <;> simp [b2z]

noncomputable def redTerms (m : ℕ) (P : Polynomial (ZMod 2)) (c : ℕ) : List (Fin (3 * m)) :=
  by classical exact (List.finRange (3 * m)).filter (fun t => decide (((Polynomial.X ^ t.val) %ₘ P).coeff c = 1))

theorem redTerms_nodup (m : ℕ) (P : Polynomial (ZMod 2)) (c : ℕ) : (redTerms m P c).Nodup := by
  classical
  unfold redTerms
  exact (List.nodup_finRange (3 * m)).filter _

theorem redTerms_length_le (m : ℕ) (P : Polynomial (ZMod 2)) (c : ℕ) :
    (redTerms m P c).length ≤ 3 * m := by
  classical
  unfold redTerms
  calc ((List.finRange (3 * m)).filter _).length
      ≤ (List.finRange (3 * m)).length := List.length_filter_le _ _
    _ = 3 * m := List.length_finRange

noncomputable def qBit (m : ℕ) (P : Polynomial (ZMod 2)) (u c : ℕ) : Bool :=
  (redTerms m P c).foldl (fun acc t => xor acc (pBit m u t.val)) false

theorem cubeNat_testBit_eq_qBit (m : ℕ) (P : Polynomial (ZMod 2)) (u c : ℕ) (hc : c < m) :
    (cubeNat m P u).testBit c = qBit m P u c := by
  classical
  unfold cubeNat
  rw [polyToNat_testBit, ite_eq_left_iff.mpr (fun hn => absurd hc hn), toPoly_cube_eq, sum_modByMonic]
  have hcoeff : (∑ t : Fin (3 * m),
      (if pBit m u t.val then (Polynomial.X : Polynomial (ZMod 2)) ^ t.val else 0) %ₘ P).coeff c =
      b2z (qBit m P u c) := by
    change (Polynomial.lcoeff (ZMod 2) c) _ = _
    rw [map_sum]
    simp only [Polynomial.lcoeff_apply]
    have hsplit : ∀ t : Fin (3 * m),
        ((if pBit m u t.val then (Polynomial.X : Polynomial (ZMod 2)) ^ t.val else 0) %ₘ P).coeff c =
        if ((Polynomial.X : Polynomial (ZMod 2)) ^ t.val %ₘ P).coeff c = 1 then b2z (pBit m u t.val) else 0 := by
      intro t
      have hz : ((Polynomial.X : Polynomial (ZMod 2)) ^ t.val %ₘ P).coeff c = 0 ∨
          ((Polynomial.X : Polynomial (ZMod 2)) ^ t.val %ₘ P).coeff c = 1 := by
        have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
        exact h2 _
      cases hp : pBit m u t.val
      · simp only [Bool.false_eq_true, ↓reduceIte, Polynomial.zero_modByMonic, Polynomial.coeff_zero, b2z]
        split_ifs <;> rfl
      · simp only [↓reduceIte, b2z]
        rcases hz with h0 | h1
        · rw [h0]; decide
        · simp [h1]
    rw [Finset.sum_congr rfl fun t _ => hsplit t, ← Finset.sum_filter]
    have hset : (redTerms m P c).toFinset =
        Finset.univ.filter (fun t : Fin (3 * m) =>
          ((Polynomial.X : Polynomial (ZMod 2)) ^ t.val %ₘ P).coeff c = 1) := by
      ext t
      simp only [List.mem_toFinset, redTerms, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ]
    rw [← hset, ← list_map_sum_eq_finset_sum _ (redTerms_nodup m P c)]
    have hb := b2z_foldl_xor (redTerms m P c) (fun t => pBit m u t.val) false
    unfold qBit
    rw [hb]
    simp [b2z]
  rw [hcoeff]
  cases qBit m P u c <;> decide

theorem toPoly_mod_two_pow (m d : ℕ) : toPoly m (d % 2 ^ m) = toPoly m d := by
  unfold toPoly
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_mod_two_pow]
  simp [i.isLt]

theorem cubeNat_mod_two_pow (m : ℕ) (P : Polynomial (ZMod 2)) (d : ℕ) :
    cubeNat m P (d % 2 ^ m) = cubeNat m P d := by
  unfold cubeNat
  rw [toPoly_mod_two_pow]

theorem mem_gammaSet_iff_bits (k : ℕ) (P : Polynomial (ZMod 2)) (d : ℕ) (hd : d < 2 ^ k) :
    d ∈ gammaSet (k / 2) P ↔
      (∀ c : Fin (k / 2), d.testBit (k / 2 + c.val) = qBit (k / 2) P d c.val) ∧
      (∀ _ : 2 * (k / 2) < k, d.testBit (2 * (k / 2)) = false) := by
  let m := k / 2
  constructor
  · intro hmem
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_range] at hu
    have hmod : (u + 2 ^ m * cubeNat m P u) % 2 ^ m = u := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
    have hcube_eq : cubeNat m P (u + 2 ^ m * cubeNat m P u) = cubeNat m P u := by
      rw [← cubeNat_mod_two_pow, hmod]
    constructor
    · intro c
      rw [← cubeNat_testBit_eq_qBit m P _ c.val c.isLt, hcube_eq, testBit_add_mul_two_pow hu]
      have h1 : ¬ m + c.val < m := by omega
      simp [m, h1]
    · intro _
      change (u + 2 ^ m * cubeNat m P u).testBit (2 * m) = false
      rw [testBit_add_mul_two_pow hu]
      have h1 : ¬ 2 * m < m := by omega
      have h2 : 2 * m - m = m := by omega
      rw [ite_eq_right_iff.mpr (fun hm => absurd hm h1), h2]
      exact Nat.testBit_lt_two_pow (cubeNat_lt m P u)
  · rintro ⟨hbits, htop⟩
    let u := d % 2 ^ m
    have hu : u < 2 ^ m := Nat.mod_lt d (Nat.pow_pos (by omega))
    have hcube_eq : cubeNat m P u = cubeNat m P d := cubeNat_mod_two_pow m P d
    have hdeq : d = u + 2 ^ m * cubeNat m P u := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [testBit_add_mul_two_pow hu]
      by_cases h1 : j < m
      · simp only [h1, ↓reduceIte, u, Nat.testBit_mod_two_pow, decide_true, Bool.true_and]
      · simp only [h1, ↓reduceIte]
        by_cases h2 : j < 2 * m
        · let c : Fin m := ⟨j - m, by omega⟩
          have hj : m + c.val = j := by dsimp [c]; omega
          rw [← hj, hbits c, ← cubeNat_testBit_eq_qBit m P d c.val c.isLt, hcube_eq]
          dsimp [c]
          have : m + (j - m) - m = j - m := by omega
          rw [this]
        · have hge : m ≤ j - m := by omega
          have hrhs : (cubeNat m P u).testBit (j - m) = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (cubeNat_lt m P u) (Nat.pow_le_pow_right (by omega) hge))
          rw [hrhs]
          by_cases h3 : j = 2 * m
          · subst h3
            by_cases h4 : 2 * m < k
            · exact htop h4
            · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by omega) (by omega)))
          · have hkj : k ≤ j := by omega
            exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by omega) hkj))
    rw [hdeq]
    exact Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr hu, rfl⟩

def isMono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem isMono_append {gs₁ gs₂ : List Gate} (h1 : isMono gs₁) (h2 : isMono gs₂) :
    isMono (gs₁ ++ gs₂) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact h1 g h
  · exact h2 g h

theorem isMono_to_Monotone2 {gs : List Gate} (h : isMono gs) (out : ℕ) :
    Monotone2 ⟨gs, out⟩ := by
  intro g hg
  obtain ⟨hop, hlen⟩ := h g hg
  exact ⟨by rcases hop with h1 | h1 <;> simp [h1], hlen⟩

def drValid (base : ℕ) (gs : List Gate) (w : ℕ × ℕ) : Prop :=
  w.1 < base + gs.length ∧ w.2 < base + gs.length

theorem drValid_append {base : ℕ} {gs extra : List Gate} {w : ℕ × ℕ} (hv : drValid base gs w) :
    drValid base (gs ++ extra) w := by
  simp only [drValid, List.length_append] at hv ⊢
  omega

def drHolds (gs : List Gate) (inp : List Bool) (w : ℕ × ℕ) (b : Bool) : Prop :=
  (runGates gs inp).getD w.1 false = b ∧ (runGates gs inp).getD w.2 false = !b

theorem drHolds_append {gs extra : List Gate} {inp : List Bool} {w : ℕ × ℕ} {b : Bool}
    (hv : drValid inp.length gs w) (hh : drHolds gs inp w b) :
    drHolds (gs ++ extra) inp w b := by
  exact ⟨(runGates_getD_append gs extra inp w.1 hv.1).trans hh.1,
    (runGates_getD_append gs extra inp w.2 hv.2).trans hh.2⟩

def drNot (w : ℕ × ℕ) : ℕ × ℕ := (w.2, w.1)

theorem drValid_not {base : ℕ} {gs : List Gate} {w : ℕ × ℕ} (hv : drValid base gs w) :
    drValid base gs (drNot w) := ⟨hv.2, hv.1⟩

theorem drHolds_not {gs : List Gate} {inp : List Bool} {w : ℕ × ℕ} {b : Bool}
    (hh : drHolds gs inp w b) : drHolds gs inp (drNot w) (!b) :=
  ⟨hh.2, by rw [Bool.not_not]; exact hh.1⟩

def drConsts (base : ℕ) (gs : List Gate) : List Gate × (ℕ × ℕ) :=
  (gs ++ [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩], (base + gs.length, base + gs.length + 1))

theorem drConsts_spec (base : ℕ) (gs : List Gate) :
    let res := drConsts base gs
    (∃ e, res.1 = gs ++ e ∧ isMono e ∧ e.length = 2) ∧
    drValid base res.1 res.2 ∧
    (∀ inp, inp.length = base → drHolds res.1 inp res.2 false) := by
  dsimp only [drConsts]
  let g1 : Gate := ⟨GateOp.or, []⟩
  let g2 : Gate := ⟨GateOp.and, []⟩
  refine ⟨⟨[g1, g2], rfl, ?_, rfl⟩, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp [g1, g2]
  · simp only [drValid, List.length_append, List.length_cons, List.length_nil]
    omega
  · intro inp hinp
    dsimp only [drHolds]
    have hsplit : gs ++ [g1, g2] = (gs ++ [g1]) ++ [g2] := by simp [List.append_assoc]
    constructor
    · rw [hsplit, runGates_getD_append (gs ++ [g1]) [g2] inp (base + gs.length)
        (by rw [hinp, List.length_append, List.length_singleton]; omega),
        ← hinp, runGates_getD_snoc]
      rfl
    · rw [hsplit]
      have hidx : base + gs.length + 1 = inp.length + (gs ++ [g1]).length := by
        rw [hinp, List.length_append, List.length_singleton]; omega
      rw [hidx, runGates_getD_snoc]
      rfl

def drAnd (base : ℕ) (gs : List Gate) (a b : ℕ × ℕ) : List Gate × (ℕ × ℕ) :=
  (gs ++ [⟨GateOp.and, [a.1, b.1]⟩, ⟨GateOp.or, [a.2, b.2]⟩], (base + gs.length, base + gs.length + 1))

theorem drAnd_spec (base : ℕ) (gs : List Gate) (a b : ℕ × ℕ) :
    let res := drAnd base gs a b
    (∃ e, res.1 = gs ++ e ∧ isMono e ∧ e.length = 2) ∧
    drValid base res.1 res.2 ∧
    (∀ inp va vb, inp.length = base → drValid base gs a → drValid base gs b →
      drHolds gs inp a va → drHolds gs inp b vb → drHolds res.1 inp res.2 (va && vb)) := by
  dsimp only [drAnd]
  let g1 : Gate := ⟨GateOp.and, [a.1, b.1]⟩
  let g2 : Gate := ⟨GateOp.or, [a.2, b.2]⟩
  refine ⟨⟨[g1, g2], rfl, ?_, rfl⟩, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp [g1, g2]
  · simp only [drValid, List.length_append, List.length_cons, List.length_nil]
    omega
  · intro inp va vb hinp hva hvb hha hhb
    dsimp only [drHolds]
    have hsplit : gs ++ [g1, g2] = (gs ++ [g1]) ++ [g2] := by simp [List.append_assoc]
    constructor
    · rw [hsplit, runGates_getD_append (gs ++ [g1]) [g2] inp
        (base + gs.length) (by rw [hinp, List.length_append, List.length_singleton]; omega),
        ← hinp, runGates_getD_snoc]
      simp only [g1, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true,
        hha.1, hhb.1]
    · rw [hsplit]
      have hidx : base + gs.length + 1 = inp.length + (gs ++ [g1]).length := by
        rw [hinp, List.length_append, List.length_singleton]; omega
      rw [hidx, runGates_getD_snoc]
      simp only [g2, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [runGates_getD_append gs [g1] inp a.2 (by rw [hinp]; exact hva.2),
        runGates_getD_append gs [g1] inp b.2 (by rw [hinp]; exact hvb.2),
        hha.2, hhb.2]
      cases va <;> cases vb <;> rfl

def drOr (base : ℕ) (gs : List Gate) (a b : ℕ × ℕ) : List Gate × (ℕ × ℕ) :=
  (gs ++ [⟨GateOp.or, [a.1, b.1]⟩, ⟨GateOp.and, [a.2, b.2]⟩], (base + gs.length, base + gs.length + 1))

theorem drOr_spec (base : ℕ) (gs : List Gate) (a b : ℕ × ℕ) :
    let res := drOr base gs a b
    (∃ e, res.1 = gs ++ e ∧ isMono e ∧ e.length = 2) ∧
    drValid base res.1 res.2 ∧
    (∀ inp va vb, inp.length = base → drValid base gs a → drValid base gs b →
      drHolds gs inp a va → drHolds gs inp b vb → drHolds res.1 inp res.2 (va || vb)) := by
  dsimp only [drOr]
  let g1 : Gate := ⟨GateOp.or, [a.1, b.1]⟩
  let g2 : Gate := ⟨GateOp.and, [a.2, b.2]⟩
  refine ⟨⟨[g1, g2], rfl, ?_, rfl⟩, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp [g1, g2]
  · simp only [drValid, List.length_append, List.length_cons, List.length_nil]
    omega
  · intro inp va vb hinp hva hvb hha hhb
    dsimp only [drHolds]
    have hsplit : gs ++ [g1, g2] = (gs ++ [g1]) ++ [g2] := by simp [List.append_assoc]
    constructor
    · rw [hsplit, runGates_getD_append (gs ++ [g1]) [g2] inp
        (base + gs.length) (by rw [hinp, List.length_append, List.length_singleton]; omega),
        ← hinp, runGates_getD_snoc]
      simp only [g1, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false,
        hha.1, hhb.1]
    · rw [hsplit]
      have hidx : base + gs.length + 1 = inp.length + (gs ++ [g1]).length := by
        rw [hinp, List.length_append, List.length_singleton]; omega
      rw [hidx, runGates_getD_snoc]
      simp only [g2, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      rw [runGates_getD_append gs [g1] inp a.2 (by rw [hinp]; exact hva.2),
        runGates_getD_append gs [g1] inp b.2 (by rw [hinp]; exact hvb.2),
        hha.2, hhb.2]
      cases va <;> cases vb <;> rfl

def drXor (base : ℕ) (gs : List Gate) (a b : ℕ × ℕ) : List Gate × (ℕ × ℕ) :=
  let g1 := drAnd base gs a (drNot b)
  let g2 := drAnd base g1.1 (drNot a) b
  drOr base g2.1 g1.2 g2.2

theorem drXor_spec (base : ℕ) (gs : List Gate) (a b : ℕ × ℕ) :
    let res := drXor base gs a b
    (∃ e, res.1 = gs ++ e ∧ isMono e ∧ e.length = 6) ∧
    drValid base res.1 res.2 ∧
    (∀ inp va vb, inp.length = base → drValid base gs a → drValid base gs b →
      drHolds gs inp a va → drHolds gs inp b vb → drHolds res.1 inp res.2 (xor va vb)) := by
  dsimp only [drXor]
  obtain ⟨⟨e1, he1, hm1, hl1⟩, hv1, hh1⟩ := drAnd_spec base gs a (drNot b)
  obtain ⟨⟨e2, he2, hm2, hl2⟩, hv2, hh2⟩ := drAnd_spec base (drAnd base gs a (drNot b)).1 (drNot a) b
  obtain ⟨⟨e3, he3, hm3, hl3⟩, hv3, hh3⟩ := drOr_spec base
    (drAnd base (drAnd base gs a (drNot b)).1 (drNot a) b).1
    (drAnd base gs a (drNot b)).2
    (drAnd base (drAnd base gs a (drNot b)).1 (drNot a) b).2
  refine ⟨⟨e1 ++ e2 ++ e3, ?_, ?_, ?_⟩, hv3, ?_⟩
  · rw [he3, he2, he1]; simp [List.append_assoc]
  · exact isMono_append (isMono_append hm1 hm2) hm3
  · simp [hl1, hl2, hl3]
  · intro inp va vb hinp hva hvb hha hhb
    have h1 := hh1 inp va (!vb) hinp hva (drValid_not hvb) hha (drHolds_not hhb)
    have hva1 : drValid base (drAnd base gs a (drNot b)).1 a := by rw [he1]; exact drValid_append hva
    have hvb1 : drValid base (drAnd base gs a (drNot b)).1 b := by rw [he1]; exact drValid_append hvb
    have hha1 : drHolds (drAnd base gs a (drNot b)).1 inp a va := by
      rw [he1]; exact drHolds_append (by rw [hinp]; exact hva) hha
    have hhb1 : drHolds (drAnd base gs a (drNot b)).1 inp b vb := by
      rw [he1]; exact drHolds_append (by rw [hinp]; exact hvb) hhb
    have h2 := hh2 inp (!va) vb hinp (drValid_not hva1) hvb1 (drHolds_not hha1) hhb1
    have hv1' : drValid base (drAnd base (drAnd base gs a (drNot b)).1 (drNot a) b).1
        (drAnd base gs a (drNot b)).2 := by rw [he2]; exact drValid_append hv1
    have h1' : drHolds (drAnd base (drAnd base gs a (drNot b)).1 (drNot a) b).1 inp
        (drAnd base gs a (drNot b)).2 (va && !vb) := by
      rw [he2]; exact drHolds_append (by rw [hinp]; exact hv1) h1
    have h3 := hh3 inp (va && !vb) (!va && vb) hinp hv1' hv2 h1' h2
    have hbool : ((va && !vb) || (!va && vb)) = xor va vb := by cases va <;> cases vb <;> rfl
    rwa [hbool] at h3

def drFoldXor {α : Type*} (base : ℕ) (gs : List Gate) (init : ℕ × ℕ)
    (w : α → ℕ × ℕ) (xs : List α) : List Gate × (ℕ × ℕ) :=
  xs.foldl (fun p x => drXor base p.1 p.2 (w x)) (gs, init)

theorem drFoldXor_spec {α : Type*} (base : ℕ) (gs : List Gate) (init : ℕ × ℕ)
    (w : α → ℕ × ℕ) (xs : List α) :
    let res := drFoldXor base gs init w xs
    (∃ e, res.1 = gs ++ e ∧ isMono e ∧ e.length = 6 * xs.length) ∧
    (drValid base gs init → (∀ x ∈ xs, drValid base gs (w x)) → drValid base res.1 res.2) ∧
    (∀ inp vi (val : α → Bool), inp.length = base →
      drValid base gs init → (∀ x ∈ xs, drValid base gs (w x)) →
      drHolds gs inp init vi → (∀ x ∈ xs, drHolds gs inp (w x) (val x)) →
      drHolds res.1 inp res.2 (xs.foldl (fun acc x => xor acc (val x)) vi)) := by
  induction xs generalizing gs init with
  | nil =>
    refine ⟨⟨[], by simp [drFoldXor], (fun _ h => nomatch h), by simp⟩, fun hi _ => hi, ?_⟩
    intro inp vi val _ _ _ hhi _
    exact hhi
  | cons a rest ih =>
    dsimp only
    have hdef : drFoldXor base gs init w (a :: rest) =
        drFoldXor base (drXor base gs init (w a)).1 (drXor base gs init (w a)).2 w rest := rfl
    rw [hdef]
    obtain ⟨⟨e1, he1, hm1, hl1⟩, hv1, hh1⟩ := drXor_spec base gs init (w a)
    obtain ⟨⟨e2, he2, hm2, hl2⟩, hv2, hh2⟩ := ih (drXor base gs init (w a)).1 (drXor base gs init (w a)).2
    refine ⟨⟨e1 ++ e2, ?_, isMono_append hm1 hm2, ?_⟩, ?_, ?_⟩
    · rw [he2, he1, List.append_assoc]
    · simp only [List.length_append, hl1, hl2, List.length_cons]; omega
    · intro hi hall
      apply hv2 hv1
      intro u hu
      rw [he1]
      exact drValid_append (hall u (List.mem_cons_of_mem a hu))
    · intro inp vi val hinp hi hall hhi hhall
      have hstep := hh1 inp vi (val a) hinp hi (hall a (List.mem_cons_self ..)) hhi
        (hhall a (List.mem_cons_self ..))
      simp only [List.foldl_cons]
      apply hh2 inp (xor vi (val a)) val hinp hv1
      · intro u hu; rw [he1]; exact drValid_append (hall u (List.mem_cons_of_mem a hu))
      · exact hstep
      · intro u hu
        rw [he1]
        exact drHolds_append (by rw [hinp]; exact hall u (List.mem_cons_of_mem a hu))
          (hhall u (List.mem_cons_of_mem a hu))

def drFoldAnd {α : Type*} (base : ℕ) (gs : List Gate) (init : ℕ × ℕ)
    (w : α → ℕ × ℕ) (xs : List α) : List Gate × (ℕ × ℕ) :=
  xs.foldl (fun p x => drAnd base p.1 p.2 (w x)) (gs, init)

theorem drFoldAnd_spec {α : Type*} (base : ℕ) (gs : List Gate) (init : ℕ × ℕ)
    (w : α → ℕ × ℕ) (xs : List α) :
    let res := drFoldAnd base gs init w xs
    (∃ e, res.1 = gs ++ e ∧ isMono e ∧ e.length = 2 * xs.length) ∧
    (drValid base gs init → (∀ x ∈ xs, drValid base gs (w x)) → drValid base res.1 res.2) ∧
    (∀ inp vi (val : α → Bool), inp.length = base →
      drValid base gs init → (∀ x ∈ xs, drValid base gs (w x)) →
      drHolds gs inp init vi → (∀ x ∈ xs, drHolds gs inp (w x) (val x)) →
      drHolds res.1 inp res.2 (xs.foldl (fun acc x => acc && val x) vi)) := by
  induction xs generalizing gs init with
  | nil =>
    refine ⟨⟨[], by simp [drFoldAnd], (fun _ h => nomatch h), by simp⟩, fun hi _ => hi, ?_⟩
    intro inp vi val _ _ _ hhi _
    exact hhi
  | cons a rest ih =>
    dsimp only
    have hdef : drFoldAnd base gs init w (a :: rest) =
        drFoldAnd base (drAnd base gs init (w a)).1 (drAnd base gs init (w a)).2 w rest := rfl
    rw [hdef]
    obtain ⟨⟨e1, he1, hm1, hl1⟩, hv1, hh1⟩ := drAnd_spec base gs init (w a)
    obtain ⟨⟨e2, he2, hm2, hl2⟩, hv2, hh2⟩ := ih (drAnd base gs init (w a)).1 (drAnd base gs init (w a)).2
    refine ⟨⟨e1 ++ e2, ?_, isMono_append hm1 hm2, ?_⟩, ?_, ?_⟩
    · rw [he2, he1, List.append_assoc]
    · simp only [List.length_append, hl1, hl2, List.length_cons]; omega
    · intro hi hall
      apply hv2 hv1
      intro u hu
      rw [he1]
      exact drValid_append (hall u (List.mem_cons_of_mem a hu))
    · intro inp vi val hinp hi hall hhi hhall
      have hstep := hh1 inp vi (val a) hinp hi (hall a (List.mem_cons_self ..)) hhi
        (hhall a (List.mem_cons_self ..))
      simp only [List.foldl_cons]
      apply hh2 inp (vi && val a) val hinp hv1
      · intro u hu; rw [he1]; exact drValid_append (hall u (List.mem_cons_of_mem a hu))
      · exact hstep
      · intro u hu
        rw [he1]
        exact drHolds_append (by rw [hinp]; exact hall u (List.mem_cons_of_mem a hu))
          (hhall u (List.mem_cons_of_mem a hu))

def drFoldOr {α : Type*} (base : ℕ) (gs : List Gate) (init : ℕ × ℕ)
    (w : α → ℕ × ℕ) (xs : List α) : List Gate × (ℕ × ℕ) :=
  xs.foldl (fun p x => drOr base p.1 p.2 (w x)) (gs, init)

theorem drFoldOr_spec {α : Type*} (base : ℕ) (gs : List Gate) (init : ℕ × ℕ)
    (w : α → ℕ × ℕ) (xs : List α) :
    let res := drFoldOr base gs init w xs
    (∃ e, res.1 = gs ++ e ∧ isMono e ∧ e.length = 2 * xs.length) ∧
    (drValid base gs init → (∀ x ∈ xs, drValid base gs (w x)) → drValid base res.1 res.2) ∧
    (∀ inp vi (val : α → Bool), inp.length = base →
      drValid base gs init → (∀ x ∈ xs, drValid base gs (w x)) →
      drHolds gs inp init vi → (∀ x ∈ xs, drHolds gs inp (w x) (val x)) →
      drHolds res.1 inp res.2 (xs.foldl (fun acc x => acc || val x) vi)) := by
  induction xs generalizing gs init with
  | nil =>
    refine ⟨⟨[], by simp [drFoldOr], (fun _ h => nomatch h), by simp⟩, fun hi _ => hi, ?_⟩
    intro inp vi val _ _ _ hhi _
    exact hhi
  | cons a rest ih =>
    dsimp only
    have hdef : drFoldOr base gs init w (a :: rest) =
        drFoldOr base (drOr base gs init (w a)).1 (drOr base gs init (w a)).2 w rest := rfl
    rw [hdef]
    obtain ⟨⟨e1, he1, hm1, hl1⟩, hv1, hh1⟩ := drOr_spec base gs init (w a)
    obtain ⟨⟨e2, he2, hm2, hl2⟩, hv2, hh2⟩ := ih (drOr base gs init (w a)).1 (drOr base gs init (w a)).2
    refine ⟨⟨e1 ++ e2, ?_, isMono_append hm1 hm2, ?_⟩, ?_, ?_⟩
    · rw [he2, he1, List.append_assoc]
    · simp only [List.length_append, hl1, hl2, List.length_cons]; omega
    · intro hi hall
      apply hv2 hv1
      intro u hu
      rw [he1]
      exact drValid_append (hall u (List.mem_cons_of_mem a hu))
    · intro inp vi val hinp hi hall hhi hhall
      have hstep := hh1 inp vi (val a) hinp hi (hall a (List.mem_cons_self ..)) hhi
        (hhall a (List.mem_cons_self ..))
      simp only [List.foldl_cons]
      apply hh2 inp (vi || val a) val hinp hv1
      · intro u hu; rw [he1]; exact drValid_append (hall u (List.mem_cons_of_mem a hu))
      · exact hstep
      · intro u hu
        rw [he1]
        exact drHolds_append (by rw [hinp]; exact hall u (List.mem_cons_of_mem a hu))
          (hhall u (List.mem_cons_of_mem a hu))

def drFoldXorPairs {α : Type*} (base : ℕ) (gs : List Gate) (init : ℕ × ℕ)
    (w1 w2 : α → ℕ × ℕ) (xs : List α) : List Gate × (ℕ × ℕ) :=
  xs.foldl (fun p x =>
    let p1 := drAnd base p.1 (w1 x) (w2 x)
    drXor base p1.1 p.2 p1.2) (gs, init)

theorem drFoldXorPairs_spec {α : Type*} (base : ℕ) (gs : List Gate) (init : ℕ × ℕ)
    (w1 w2 : α → ℕ × ℕ) (xs : List α) :
    let res := drFoldXorPairs base gs init w1 w2 xs
    (∃ e, res.1 = gs ++ e ∧ isMono e ∧ e.length = 8 * xs.length) ∧
    (drValid base gs init → (∀ x ∈ xs, drValid base gs (w1 x) ∧ drValid base gs (w2 x)) →
      drValid base res.1 res.2) ∧
    (∀ inp vi (v1 v2 : α → Bool), inp.length = base →
      drValid base gs init → (∀ x ∈ xs, drValid base gs (w1 x) ∧ drValid base gs (w2 x)) →
      drHolds gs inp init vi → (∀ x ∈ xs, drHolds gs inp (w1 x) (v1 x) ∧ drHolds gs inp (w2 x) (v2 x)) →
      drHolds res.1 inp res.2 (xs.foldl (fun acc x => xor acc (v1 x && v2 x)) vi)) := by
  induction xs generalizing gs init with
  | nil =>
    refine ⟨⟨[], by simp [drFoldXorPairs], (fun _ h => nomatch h), by simp⟩, fun hi _ => hi, ?_⟩
    intro inp vi v1 v2 _ _ _ hhi _
    exact hhi
  | cons a rest ih =>
    dsimp only
    have hdef : drFoldXorPairs base gs init w1 w2 (a :: rest) =
        drFoldXorPairs base
          (drXor base (drAnd base gs (w1 a) (w2 a)).1 init (drAnd base gs (w1 a) (w2 a)).2).1
          (drXor base (drAnd base gs (w1 a) (w2 a)).1 init (drAnd base gs (w1 a) (w2 a)).2).2
          w1 w2 rest := rfl
    rw [hdef]
    obtain ⟨⟨e1, he1, hm1, hl1⟩, hv1, hh1⟩ := drAnd_spec base gs (w1 a) (w2 a)
    obtain ⟨⟨e2, he2, hm2, hl2⟩, hv2, hh2⟩ := drXor_spec base (drAnd base gs (w1 a) (w2 a)).1 init
      (drAnd base gs (w1 a) (w2 a)).2
    obtain ⟨⟨e3, he3, hm3, hl3⟩, hv3, hh3⟩ := ih
      (drXor base (drAnd base gs (w1 a) (w2 a)).1 init (drAnd base gs (w1 a) (w2 a)).2).1
      (drXor base (drAnd base gs (w1 a) (w2 a)).1 init (drAnd base gs (w1 a) (w2 a)).2).2
    refine ⟨⟨e1 ++ e2 ++ e3, ?_, isMono_append (isMono_append hm1 hm2) hm3, ?_⟩, ?_, ?_⟩
    · rw [he3, he2, he1]; simp [List.append_assoc]
    · simp only [List.length_append, hl1, hl2, hl3, List.length_cons]; omega
    · intro hi hall
      apply hv3 hv2
      intro x hx
      have hxv := hall x (List.mem_cons_of_mem a hx)
      rw [he2, he1, List.append_assoc]
      exact ⟨drValid_append hxv.1, drValid_append hxv.2⟩
    · intro inp vi v1 v2 hinp hi hall hhi hhall
      have ha_v := hall a (List.mem_cons_self ..)
      have ha_h := hhall a (List.mem_cons_self ..)
      have hprod := hh1 inp (v1 a) (v2 a) hinp ha_v.1 ha_v.2 ha_h.1 ha_h.2
      have hi1 : drValid base (drAnd base gs (w1 a) (w2 a)).1 init := by rw [he1]; exact drValid_append hi
      have hhi1 : drHolds (drAnd base gs (w1 a) (w2 a)).1 inp init vi := by
        rw [he1]; exact drHolds_append (by rw [hinp]; exact hi) hhi
      have hstep := hh2 inp vi (v1 a && v2 a) hinp hi1 hv1 hhi1 hprod
      simp only [List.foldl_cons]
      apply hh3 inp (xor vi (v1 a && v2 a)) v1 v2 hinp hv2
      · intro x hx
        have hxv := hall x (List.mem_cons_of_mem a hx)
        rw [he2, he1, List.append_assoc]
        exact ⟨drValid_append hxv.1, drValid_append hxv.2⟩
      · exact hstep
      · intro x hx
        have hxv := hall x (List.mem_cons_of_mem a hx)
        have hxh := hhall x (List.mem_cons_of_mem a hx)
        rw [he2, he1, List.append_assoc]
        exact ⟨drHolds_append (by rw [hinp]; exact hxv.1) hxh.1,
          drHolds_append (by rw [hinp]; exact hxv.2) hxh.2⟩

def drBuildList {α : Type*} [DecidableEq α] (gs : List Gate)
    (keys : List α) (build : List Gate → α → List Gate × (ℕ × ℕ)) :
    List Gate × (α → ℕ × ℕ) :=
  match keys with
  | [] => (gs, fun _ => (0, 0))
  | a :: rest =>
    let p1 := build gs a
    let p2 := drBuildList p1.1 rest build
    (p2.1, fun b => if b = a then p1.2 else p2.2 b)

theorem drBuildList_spec {α : Type*} [DecidableEq α] (base : ℕ) (gs : List Gate)
    (keys : List α) (hnd : keys.Nodup)
    (Pinp : List Bool → Prop) (hPinp : ∀ inp, Pinp inp → inp.length = base)
    (build : List Gate → α → List Gate × (ℕ × ℕ))
    (cost : α → ℕ) (val : List Bool → α → Bool)
    (hbuild : ∀ (a : α), a ∈ keys → ∀ (ext : List Gate),
      let r := build (gs ++ ext) a
      (∃ e, r.1 = (gs ++ ext) ++ e ∧ isMono e ∧ e.length ≤ cost a) ∧
      drValid base r.1 r.2 ∧
      (∀ inp, Pinp inp → drHolds r.1 inp r.2 (val inp a))) :
    let res := drBuildList gs keys build
    (∃ extra, res.1 = gs ++ extra ∧ isMono extra ∧ extra.length ≤ (keys.map cost).sum) ∧
    (∀ a ∈ keys, drValid base res.1 (res.2 a)) ∧
    (∀ inp, Pinp inp → ∀ a ∈ keys, drHolds res.1 inp (res.2 a) (val inp a)) := by
  have hgen : ∀ (ks : List α), ks.Nodup → (∀ a ∈ ks, a ∈ keys) → ∀ (ext : List Gate),
      let res := drBuildList (gs ++ ext) ks build
      (∃ extra, res.1 = (gs ++ ext) ++ extra ∧ isMono extra ∧ extra.length ≤ (ks.map cost).sum) ∧
      (∀ a ∈ ks, drValid base res.1 (res.2 a)) ∧
      (∀ inp, Pinp inp → ∀ a ∈ ks, drHolds res.1 inp (res.2 a) (val inp a)) := by
    intro ks
    induction ks with
    | nil =>
      intro _ _ ext
      refine ⟨⟨[], by simp [drBuildList], (fun _ h => nomatch h), by simp⟩,
        (fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    | cons a rest ih =>
      intro hnd' hsub ext
      rw [List.nodup_cons] at hnd'
      obtain ⟨hanot, hnd_rest⟩ := hnd'
      dsimp only [drBuildList]
      obtain ⟨⟨e1, he1, hm1, hl1⟩, hv1, hh1⟩ := hbuild a (hsub a (List.mem_cons_self ..)) ext
      have h1eq : (build (gs ++ ext) a).1 = gs ++ (ext ++ e1) := by
        rw [he1, List.append_assoc]
      have hih := ih hnd_rest (fun b hb => hsub b (List.mem_cons_of_mem a hb)) (ext ++ e1)
      rw [← h1eq] at hih
      obtain ⟨⟨e2, he2, hm2, hl2⟩, hv2, hh2⟩ := hih
      refine ⟨⟨e1 ++ e2, ?_, isMono_append hm1 hm2, ?_⟩, ?_, ?_⟩
      · rw [he2, he1, List.append_assoc]
      · simp only [List.length_append, List.map_cons, List.sum_cons]
        omega
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · simp only [↓reduceIte]
          rw [he2]
          exact drValid_append hv1
        · have hba : b ≠ a := fun h => hanot (h ▸ hb)
          simp only [hba, ↓reduceIte]
          exact hv2 b hb
      · intro inp hinp b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · simp only [↓reduceIte]
          rw [he2]
          exact drHolds_append (by rw [hPinp inp hinp]; exact hv1) (hh1 inp hinp)
        · have hba : b ≠ a := fun h => hanot (h ▸ hb)
          simp only [hba, ↓reduceIte]
          exact hh2 inp hinp b hb
  simpa using hgen keys hnd (fun _ h => h) []

theorem foldl_and_eq_decide {α : Type*} (l : List α) (f : α → Bool) :
    l.foldl (fun acc x => acc && f x) true = decide (∀ x ∈ l, f x = true) := by
  have hgen : ∀ (init : Bool),
      l.foldl (fun acc x => acc && f x) init = (init && decide (∀ x ∈ l, f x = true)) := by
    induction l with
    | nil => intro init; simp
    | cons a rest ih =>
      intro init
      simp only [List.foldl_cons, ih]
      by_cases h1 : f a = true <;> by_cases h2 : ∀ x ∈ rest, f x = true
      · simp [h1]
      · simp [h1, h2]
      · have h1f : f a = false := Bool.eq_false_iff.mpr h1
        simp [h1f]
      · have h1f : f a = false := Bool.eq_false_iff.mpr h1
        simp [h1f]
  simpa using hgen true

theorem foldl_or_eq_decide {α : Type*} (l : List α) (f : α → Bool) :
    l.foldl (fun acc x => acc || f x) false = decide (∃ x ∈ l, f x = true) := by
  have hgen : ∀ (init : Bool),
      l.foldl (fun acc x => acc || f x) init = (init || decide (∃ x ∈ l, f x = true)) := by
    induction l with
    | nil => intro init; simp
    | cons a rest ih =>
      intro init
      simp only [List.foldl_cons, ih]
      by_cases h1 : f a = true <;> by_cases h2 : ∃ x ∈ rest, f x = true
      · simp [h1, h2]
      · simp [h1, h2]
      · obtain ⟨x, hx, hfx⟩ := h2
        have h1f : f a = false := Bool.eq_false_iff.mpr h1
        simp [h1f, show ∃ x ∈ rest, f x = true from ⟨x, hx, hfx⟩]
      · have h1f : f a = false := Bool.eq_false_iff.mpr h1
        simp [h1f, h2]
  simpa using hgen false

theorem tableIndex_lt {n : ℕ} (x : Fin n → Bool) : tableIndex x < 2 ^ n :=
  sum_bool_pow_two_lt n x

theorem tableIndex_testBit {n : ℕ} (x : Fin n → Bool) (j : ℕ) :
    (tableIndex x).testBit j = if hj : j < n then x ⟨j, hj⟩ else false :=
  sum_pow_two_testBit n x j

theorem litInput_length {n : ℕ} (z : Fin n → Bool) :
    (List.ofFn z ++ List.ofFn fun i => !z i).length = n + n := by
  simp

theorem litInput_getD_pos {n : ℕ} (z : Fin n → Bool) (i : Fin n) :
    (List.ofFn z ++ List.ofFn fun j => !z j).getD i.val false = z i := by
  rw [list_getD_append_left _ _ _ _ (by simp [i.isLt])]
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem litInput_getD_neg {n : ℕ} (z : Fin n → Bool) (i : Fin n) :
    (List.ofFn z ++ List.ofFn fun j => !z j).getD (n + i.val) false = !z i := by
  rw [list_getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem hasLitSize_target_gamma (k a : ℕ) (ha : 6 ≤ a) (hk : 2 * 2 ^ a ≤ k)
    (P : Polynomial (ZMod 2)) :
    let N := 2 ^ k
    let r := 2 ^ a
    let I := Fin N
    let target := fun (D : Finset ℕ) (x y : I) =>
      xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
    HasLitSize (k + k) (adjFun (k := k) (l := k) (target (gammaSet (k / 2) P))) (150 * (k + 1) ^ 2) := by
  classical
  dsimp only
  let m : ℕ := k / 2
  let r : ℕ := 2 ^ a
  let base : ℕ := (k + k) + (k + k)
  have har : a < r := Nat.lt_two_pow_self
  have hrk : r ≤ k := by omega
  have hak : a ≤ k := le_trans (le_of_lt har) hrk
  have h2mk : 2 * m ≤ k := by dsimp [m]; omega
  let xW : Fin k → ℕ × ℕ := fun i => (i.val, (k + k) + i.val)
  let yW : Fin k → ℕ × ℕ := fun i => (k + i.val, (k + k) + (k + i.val))
  have hxW_v : ∀ i : Fin k, drValid base [] (xW i) := fun i => by
    simp only [drValid, xW, List.length_nil, base]; omega
  have hyW_v : ∀ i : Fin k, drValid base [] (yW i) := fun i => by
    simp only [drValid, yW, List.length_nil, base]; omega
  let xBit : List Bool → Fin k → Bool := fun inp i => inp.getD i.val false
  let yBit : List Bool → Fin k → Bool := fun inp i => inp.getD (k + i.val) false
  let dBit : List Bool → Fin k → Bool := fun inp i => xor (xBit inp i) (yBit inp i)
  let isLitInp : List Bool → Prop := fun inp =>
    inp.length = base ∧ ∀ i : Fin (k + k), inp.getD ((k + k) + i.val) false = !inp.getD i.val false
  have hPinp : ∀ inp, isLitInp inp → inp.length = base := fun _ h => h.1
  have hxW_h : ∀ inp, isLitInp inp → ∀ i : Fin k, drHolds [] inp (xW i) (xBit inp i) := by
    intro inp hinp i
    dsimp only [drHolds, runGates, xW, xBit]
    exact ⟨rfl, hinp.2 ⟨i.val, by omega⟩⟩
  have hyW_h : ∀ inp, isLitInp inp → ∀ i : Fin k, drHolds [] inp (yW i) (yBit inp i) := by
    intro inp hinp i
    dsimp only [drHolds, runGates, yW, yBit]
    exact ⟨rfl, hinp.2 ⟨k + i.val, by omega⟩⟩
  obtain ⟨⟨ec, hec, hmc, hlc⟩, hvc, hhc⟩ := drConsts_spec base []
  generalize hgc : (drConsts base []).1 = gsC at hec hvc hhc
  generalize hwc : (drConsts base []).2 = wF at hvc hhc
  clear hgc hwc
  let wT : ℕ × ℕ := drNot wF
  have hgsC_m : isMono gsC := by rw [hec]; simpa using hmc
  have hgsC_l : gsC.length = 2 := by rw [hec]; simp [hlc]
  have hxW_vc : ∀ i : Fin k, drValid base gsC (xW i) := fun i => by rw [hec]; exact drValid_append (hxW_v i)
  have hyW_vc : ∀ i : Fin k, drValid base gsC (yW i) := fun i => by rw [hec]; exact drValid_append (hyW_v i)
  have hxW_hc : ∀ inp, isLitInp inp → ∀ i : Fin k, drHolds gsC inp (xW i) (xBit inp i) := fun inp hinp i => by
    rw [hec]; exact drHolds_append (by rw [hinp.1]; exact hxW_v i) (hxW_h inp hinp i)
  have hyW_hc : ∀ inp, isLitInp inp → ∀ i : Fin k, drHolds gsC inp (yW i) (yBit inp i) := fun inp hinp i => by
    rw [hec]; exact drHolds_append (by rw [hinp.1]; exact hyW_v i) (hyW_h inp hinp i)
  let buildD : List Gate → Fin k → List Gate × (ℕ × ℕ) := fun g i => drXor base g (xW i) (yW i)
  have hresD := drBuildList_spec base gsC (List.finRange k) (List.nodup_finRange k) isLitInp hPinp
    buildD (fun _ => 6) dBit (by
      intro i _ ext
      dsimp only [buildD, dBit]
      obtain ⟨⟨e, he, hm, hl⟩, hv, hh⟩ := drXor_spec base (gsC ++ ext) (xW i) (yW i)
      refine ⟨⟨e, he, hm, by omega⟩, hv, ?_⟩
      intro inp hinp
      exact hh inp (xBit inp i) (yBit inp i) hinp.1 (drValid_append (hxW_vc i)) (drValid_append (hyW_vc i))
        (drHolds_append (by rw [hinp.1]; exact hxW_vc i) (hxW_hc inp hinp i))
        (drHolds_append (by rw [hinp.1]; exact hyW_vc i) (hyW_hc inp hinp i)))
  obtain ⟨⟨eD, heD, hmD, hlD⟩, hvD, hhD⟩ := hresD
  generalize hgD : (drBuildList gsC (List.finRange k) buildD).1 = gsD at heD hvD hhD
  generalize hwD : (drBuildList gsC (List.finRange k) buildD).2 = dW at hvD hhD
  clear hgD hwD
  have hgsD_m : isMono gsD := by rw [heD]; exact isMono_append hgsC_m hmD
  have hgsD_l : gsD.length ≤ 2 + 6 * k := by
    have hsum : ((List.finRange k).map (fun _ : Fin k => (6 : ℕ))).sum ≤ k * 6 := by
      simp
    rw [heD, List.length_append, hgsC_l]; omega
  have hwF_vD : drValid base gsD wF := by rw [heD]; exact drValid_append hvc
  have hwF_hD : ∀ inp, isLitInp inp → drHolds gsD inp wF false := fun inp hinp => by
    rw [heD]; exact drHolds_append (by rw [hinp.1]; exact hvc) (hhc inp hinp.1)
  have hdW_v : ∀ i : Fin k, drValid base gsD (dW i) := fun i => hvD i (List.mem_finRange i)
  have hdW_h : ∀ inp, isLitInp inp → ∀ i : Fin k, drHolds gsD inp (dW i) (dBit inp i) :=
    fun inp hinp i => hhD inp hinp i (List.mem_finRange i)
  let dLo : Fin m → ℕ × ℕ := fun i => dW ⟨i.val, by omega⟩
  let dLoBit : List Bool → Fin m → Bool := fun inp i => dBit inp ⟨i.val, by omega⟩
  let pVal : List Bool → Fin (3 * m) → Bool := fun inp t =>
    (pairsFor m t.val).foldl (fun acc ij => xor acc (dLoBit inp ij.1 && dLoBit inp ij.2)) false
  let buildP : List Gate → Fin (3 * m) → List Gate × (ℕ × ℕ) := fun g t =>
    drFoldXorPairs base g wF (fun ij => dLo ij.1) (fun ij => dLo ij.2) (pairsFor m t.val)
  have hresP := drBuildList_spec base gsD (List.finRange (3 * m)) (List.nodup_finRange (3 * m)) isLitInp hPinp
    buildP (fun t => 8 * (pairsFor m t.val).length) pVal (by
      intro t _ ext
      dsimp only [buildP, pVal]
      obtain ⟨⟨e, he, hm, hl⟩, hv, hh⟩ := drFoldXorPairs_spec base (gsD ++ ext) wF
        (fun ij => dLo ij.1) (fun ij => dLo ij.2) (pairsFor m t.val)
      refine ⟨⟨e, he, hm, by omega⟩, ?_, ?_⟩
      · exact hv (drValid_append hwF_vD) (fun ij _ => ⟨drValid_append (hdW_v _), drValid_append (hdW_v _)⟩)
      · intro inp hinp
        exact hh inp false (fun ij => dLoBit inp ij.1) (fun ij => dLoBit inp ij.2) hinp.1
          (drValid_append hwF_vD)
          (fun ij _ => ⟨drValid_append (hdW_v _), drValid_append (hdW_v _)⟩)
          (drHolds_append (by rw [hinp.1]; exact hwF_vD) (hwF_hD inp hinp))
          (fun ij _ => ⟨drHolds_append (by rw [hinp.1]; exact hdW_v _) (hdW_h inp hinp _),
            drHolds_append (by rw [hinp.1]; exact hdW_v _) (hdW_h inp hinp _)⟩))
  obtain ⟨⟨eP, heP, hmP, hlP⟩, hvP, hhP⟩ := hresP
  generalize hgP : (drBuildList gsD (List.finRange (3 * m)) buildP).1 = gsP at heP hvP hhP
  generalize hwP : (drBuildList gsD (List.finRange (3 * m)) buildP).2 = pW at hvP hhP
  clear hgP hwP
  have hgsP_m : isMono gsP := by rw [heP]; exact isMono_append hgsD_m hmP
  have hgsP_l : gsP.length ≤ gsD.length + 8 * (m * m) := by
    have hsum : ((List.finRange (3 * m)).map (fun t => 8 * (pairsFor m t.val).length)).sum = 8 * (m * m) := by
      have hmul : ∀ (l : List (Fin (3 * m))) (f : Fin (3 * m) → ℕ),
          (l.map (fun t => 8 * f t)).sum = 8 * (l.map f).sum := by
        intro l f
        induction l with
        | nil => simp
        | cons a rest ih => simp only [List.map_cons, List.sum_cons, ih]; omega
      rw [hmul, sum_pairsFor_length]
    rw [heP, List.length_append]; omega
  have hwF_vP : drValid base gsP wF := by rw [heP]; exact drValid_append hwF_vD
  have hwF_hP : ∀ inp, isLitInp inp → drHolds gsP inp wF false := fun inp hinp => by
    rw [heP]; exact drHolds_append (by rw [hinp.1]; exact hwF_vD) (hwF_hD inp hinp)
  have hpW_v : ∀ t : Fin (3 * m), drValid base gsP (pW t) := fun t => hvP t (List.mem_finRange t)
  have hpW_h : ∀ inp, isLitInp inp → ∀ t : Fin (3 * m), drHolds gsP inp (pW t) (pVal inp t) :=
    fun inp hinp t => hhP inp hinp t (List.mem_finRange t)
  let qVal : List Bool → Fin m → Bool := fun inp c =>
    (redTerms m P c.val).foldl (fun acc t => xor acc (pVal inp t)) false
  let buildQ : List Gate → Fin m → List Gate × (ℕ × ℕ) := fun g c =>
    drFoldXor base g wF pW (redTerms m P c.val)
  have hresQ := drBuildList_spec base gsP (List.finRange m) (List.nodup_finRange m) isLitInp hPinp
    buildQ (fun _ => 18 * m) qVal (by
      intro c _ ext
      dsimp only [buildQ, qVal]
      obtain ⟨⟨e, he, hm, hl⟩, hv, hh⟩ := drFoldXor_spec base (gsP ++ ext) wF pW (redTerms m P c.val)
      have hlen : (redTerms m P c.val).length ≤ 3 * m := redTerms_length_le m P c.val
      refine ⟨⟨e, he, hm, by omega⟩, ?_, ?_⟩
      · exact hv (drValid_append hwF_vP) (fun t _ => drValid_append (hpW_v t))
      · intro inp hinp
        exact hh inp false (pVal inp) hinp.1 (drValid_append hwF_vP)
          (fun t _ => drValid_append (hpW_v t))
          (drHolds_append (by rw [hinp.1]; exact hwF_vP) (hwF_hP inp hinp))
          (fun t _ => drHolds_append (by rw [hinp.1]; exact hpW_v t) (hpW_h inp hinp t)))
  obtain ⟨⟨eQ, heQ, hmQ, hlQ⟩, hvQ, hhQ⟩ := hresQ
  generalize hgQ : (drBuildList gsP (List.finRange m) buildQ).1 = gsQ at heQ hvQ hhQ
  generalize hwQ : (drBuildList gsP (List.finRange m) buildQ).2 = qW at hvQ hhQ
  clear hgQ hwQ
  have hgsQ_m : isMono gsQ := by rw [heQ]; exact isMono_append hgsP_m hmQ
  have hgsQ_l : gsQ.length ≤ gsP.length + 18 * (m * m) := by
    have hsum : ((List.finRange m).map (fun _ : Fin m => 18 * m)).sum ≤ m * (18 * m) := by
      simp
    rw [heQ, List.length_append]
    have : m * (18 * m) = 18 * (m * m) := by ring
    omega
  have hgsD_to_Q : ∃ eDQ, gsQ = gsD ++ eDQ := ⟨eP ++ eQ, by rw [heQ, heP, List.append_assoc]⟩
  obtain ⟨eDQ, heDQ⟩ := hgsD_to_Q
  have hwF_vQ : drValid base gsQ wF := by rw [heDQ]; exact drValid_append hwF_vD
  have hwF_hQ : ∀ inp, isLitInp inp → drHolds gsQ inp wF false := fun inp hinp => by
    rw [heDQ]; exact drHolds_append (by rw [hinp.1]; exact hwF_vD) (hwF_hD inp hinp)
  have hdW_vQ : ∀ i : Fin k, drValid base gsQ (dW i) := fun i => by rw [heDQ]; exact drValid_append (hdW_v i)
  have hdW_hQ : ∀ inp, isLitInp inp → ∀ i : Fin k, drHolds gsQ inp (dW i) (dBit inp i) := fun inp hinp i => by
    rw [heDQ]; exact drHolds_append (by rw [hinp.1]; exact hdW_v i) (hdW_h inp hinp i)
  have hqW_v : ∀ c : Fin m, drValid base gsQ (qW c) := fun c => hvQ c (List.mem_finRange c)
  have hqW_h : ∀ inp, isLitInp inp → ∀ c : Fin m, drHolds gsQ inp (qW c) (qVal inp c) :=
    fun inp hinp c => hhQ inp hinp c (List.mem_finRange c)
  let eqVal : List Bool → Fin m → Bool := fun inp c => decide (dBit inp ⟨m + c.val, by omega⟩ = qVal inp c)
  let buildEq : List Gate → Fin m → List Gate × (ℕ × ℕ) := fun g c =>
    let res := drXor base g (dW ⟨m + c.val, by omega⟩) (qW c)
    (res.1, drNot res.2)
  have hresEq := drBuildList_spec base gsQ (List.finRange m) (List.nodup_finRange m) isLitInp hPinp
    buildEq (fun _ => 6) eqVal (by
      intro c _ ext
      dsimp only [buildEq, eqVal]
      obtain ⟨⟨e, he, hm, hl⟩, hv, hh⟩ := drXor_spec base (gsQ ++ ext) (dW ⟨m + c.val, by omega⟩) (qW c)
      refine ⟨⟨e, he, hm, by omega⟩, drValid_not hv, ?_⟩
      intro inp hinp
      have h1 := drHolds_not (hh inp (dBit inp ⟨m + c.val, by omega⟩) (qVal inp c) hinp.1
        (drValid_append (hdW_vQ _)) (drValid_append (hqW_v c))
        (drHolds_append (by rw [hinp.1]; exact hdW_vQ _) (hdW_hQ inp hinp _))
        (drHolds_append (by rw [hinp.1]; exact hqW_v c) (hqW_h inp hinp c)))
      have hbool : (!(xor (dBit inp ⟨m + c.val, by omega⟩) (qVal inp c))) =
          decide (dBit inp ⟨m + c.val, by omega⟩ = qVal inp c) := by
        cases dBit inp ⟨m + c.val, by omega⟩ <;> cases qVal inp c <;> decide
      rwa [hbool] at h1)
  obtain ⟨⟨eEq, heEq, hmEq, hlEq⟩, hvEq, hhEq⟩ := hresEq
  generalize hgEq : (drBuildList gsQ (List.finRange m) buildEq).1 = gsEq at heEq hvEq hhEq
  generalize hwEq : (drBuildList gsQ (List.finRange m) buildEq).2 = eqW at hvEq hhEq
  clear hgEq hwEq
  have hgsEq_m : isMono gsEq := by rw [heEq]; exact isMono_append hgsQ_m hmEq
  have hgsEq_l : gsEq.length ≤ gsQ.length + 6 * m := by
    have hsum : ((List.finRange m).map (fun _ : Fin m => (6 : ℕ))).sum ≤ m * 6 := by
      simp
    rw [heEq, List.length_append]; omega
  have hwF_vEq : drValid base gsEq wF := by rw [heEq]; exact drValid_append hwF_vQ
  have hwF_hEq : ∀ inp, isLitInp inp → drHolds gsEq inp wF false := fun inp hinp => by
    rw [heEq]; exact drHolds_append (by rw [hinp.1]; exact hwF_vQ) (hwF_hQ inp hinp)
  have hdW_vEq : ∀ i : Fin k, drValid base gsEq (dW i) := fun i => by rw [heEq]; exact drValid_append (hdW_vQ i)
  have hdW_hEq : ∀ inp, isLitInp inp → ∀ i : Fin k, drHolds gsEq inp (dW i) (dBit inp i) := fun inp hinp i => by
    rw [heEq]; exact drHolds_append (by rw [hinp.1]; exact hdW_vQ i) (hdW_hQ inp hinp i)
  obtain ⟨⟨eG0, heG0, hmG0, hlG0⟩, hvG0, hhG0⟩ := drFoldAnd_spec base gsEq wT eqW (List.finRange m)
  generalize hgG0 : (drFoldAnd base gsEq wT eqW (List.finRange m)).1 = gsG0 at heG0 hvG0 hhG0
  generalize hwG0 : (drFoldAnd base gsEq wT eqW (List.finRange m)).2 = wG0 at hvG0 hhG0
  clear hgG0 hwG0
  have hgsG0_m : isMono gsG0 := by rw [heG0]; exact isMono_append hgsEq_m hmG0
  have hgsG0_l : gsG0.length ≤ gsEq.length + 2 * m := by
    rw [heG0, List.length_append, hlG0, List.length_finRange]
  have hwG0_v : drValid base gsG0 wG0 :=
    hvG0 (drValid_not hwF_vEq) (fun c _ => hvEq c (List.mem_finRange c))
  have hwG0_h : ∀ inp, isLitInp inp →
      drHolds gsG0 inp wG0 (decide (∀ c : Fin m, eqVal inp c = true)) := by
    intro inp hinp
    have h1 := hhG0 inp true (eqVal inp) hinp.1 (drValid_not hwF_vEq)
      (fun c _ => hvEq c (List.mem_finRange c)) (drHolds_not (hwF_hEq inp hinp))
      (fun c _ => hhEq inp hinp c (List.mem_finRange c))
    rw [foldl_and_eq_decide] at h1
    have hiff : (∀ c ∈ List.finRange m, eqVal inp c = true) ↔ (∀ c : Fin m, eqVal inp c = true) :=
      ⟨fun h c => h c (List.mem_finRange c), fun h c _ => h c⟩
    rwa [decide_eq_decide.mpr hiff] at h1
  let gammaVal : List Bool → Bool := fun inp =>
    decide ((∀ c : Fin m, eqVal inp c = true) ∧ (∀ h : 2 * m < k, dBit inp ⟨2 * m, h⟩ = false))
  have hG_step : ∃ (gsG : List Gate) (wG : ℕ × ℕ) (eG : List Gate),
      gsG = gsG0 ++ eG ∧ isMono eG ∧ eG.length ≤ 2 ∧
      drValid base gsG wG ∧ (∀ inp, isLitInp inp → drHolds gsG inp wG (gammaVal inp)) := by
    by_cases hodd : 2 * m < k
    · obtain ⟨⟨e1, he1, hm1, hl1⟩, hv1, hh1⟩ :=
        drAnd_spec base gsG0 wG0 (drNot (dW ⟨2 * m, hodd⟩))
      refine ⟨(drAnd base gsG0 wG0 (drNot (dW ⟨2 * m, hodd⟩))).1,
        (drAnd base gsG0 wG0 (drNot (dW ⟨2 * m, hodd⟩))).2, e1, he1, hm1, by omega, hv1, ?_⟩
      intro inp hinp
      have hdv : drValid base gsG0 (dW ⟨2 * m, hodd⟩) := by rw [heG0]; exact drValid_append (hdW_vEq _)
      have hdh : drHolds gsG0 inp (dW ⟨2 * m, hodd⟩) (dBit inp ⟨2 * m, hodd⟩) := by
        rw [heG0]; exact drHolds_append (by rw [hinp.1]; exact hdW_vEq _) (hdW_hEq inp hinp _)
      have h1 := hh1 inp (decide (∀ c : Fin m, eqVal inp c = true)) (!dBit inp ⟨2 * m, hodd⟩)
        hinp.1 hwG0_v (drValid_not hdv) (hwG0_h inp hinp) (drHolds_not hdh)
      have hbool : (decide (∀ c : Fin m, eqVal inp c = true) && !dBit inp ⟨2 * m, hodd⟩) = gammaVal inp := by
        dsimp only [gammaVal]
        by_cases ha1 : ∀ c : Fin m, eqVal inp c = true <;> cases hb1 : dBit inp ⟨2 * m, hodd⟩
        · have h2 : ∀ h : 2 * m < k, dBit inp ⟨2 * m, h⟩ = false := fun _ => hb1
          simp [ha1, h2]
        · have h2 : ¬ ∀ h : 2 * m < k, dBit inp ⟨2 * m, h⟩ = false := fun h => by have := h hodd; rw [hb1] at this; contradiction
          simp [ha1, h2]
        · simp [ha1]
        · simp [ha1]
      rwa [hbool] at h1
    · refine ⟨gsG0, wG0, [], by simp, (fun _ h => nomatch h), by simp, hwG0_v, ?_⟩
      intro inp hinp
      have hbool : decide (∀ c : Fin m, eqVal inp c = true) = gammaVal inp := by
        dsimp only [gammaVal]
        exact decide_eq_decide.mpr ⟨fun h => ⟨h, fun h' => absurd h' hodd⟩, fun h => h.1⟩
      rw [← hbool]
      exact hwG0_h inp hinp
  obtain ⟨gsG, wG, eG, heG, hmG, hlG, hwG_v, hwG_h⟩ := hG_step
  have hgsG_m : isMono gsG := by rw [heG]; exact isMono_append hgsG0_m hmG
  have hgsG_l : gsG.length ≤ gsG0.length + 2 := by rw [heG, List.length_append]; omega
  have hgsC_to_G : ∃ eCG, gsG = gsC ++ eCG := by
    refine ⟨eD ++ eDQ ++ eEq ++ eG0 ++ eG, ?_⟩
    rw [heG, heG0, heEq, heDQ, heD]
    simp [List.append_assoc]
  obtain ⟨eCG, heCG⟩ := hgsC_to_G
  have hwF_vG : drValid base gsG wF := by rw [heCG]; exact drValid_append hvc
  have hwF_hG : ∀ inp, isLitInp inp → drHolds gsG inp wF false := fun inp hinp => by
    rw [heCG]; exact drHolds_append (by rw [hinp.1]; exact hvc) (hhc inp hinp.1)
  have hxW_vG : ∀ i : Fin k, drValid base gsG (xW i) := fun i => by rw [heCG]; exact drValid_append (hxW_vc i)
  have hyW_vG : ∀ i : Fin k, drValid base gsG (yW i) := fun i => by rw [heCG]; exact drValid_append (hyW_vc i)
  have hxW_hG : ∀ inp, isLitInp inp → ∀ i : Fin k, drHolds gsG inp (xW i) (xBit inp i) := fun inp hinp i => by
    rw [heCG]; exact drHolds_append (by rw [hinp.1]; exact hxW_vc i) (hxW_hc inp hinp i)
  have hyW_hG : ∀ inp, isLitInp inp → ∀ i : Fin k, drHolds gsG inp (yW i) (yBit inp i) := fun inp hinp i => by
    rw [heCG]; exact drHolds_append (by rw [hinp.1]; exact hyW_vc i) (hyW_hc inp hinp i)
  let termVal : List Bool → Fin r → Bool := fun inp j =>
    (decide (∀ b : Fin a, yBit inp ⟨b.val, by omega⟩ = j.val.testBit b.val)) &&
      xBit inp ⟨j.val, lt_of_lt_of_le j.isLt hrk⟩
  let buildTerm : List Gate → Fin r → List Gate × (ℕ × ℕ) := fun g j =>
    let p1 := drFoldAnd base g wT
      (fun b : Fin a => if j.val.testBit b.val then yW ⟨b.val, by omega⟩ else drNot (yW ⟨b.val, by omega⟩))
      (List.finRange a)
    drAnd base p1.1 p1.2 (xW ⟨j.val, lt_of_lt_of_le j.isLt hrk⟩)
  have hresT := drBuildList_spec base gsG (List.finRange r) (List.nodup_finRange r) isLitInp hPinp
    buildTerm (fun _ => 2 * a + 2) termVal (by
      intro j _ ext
      dsimp only [buildTerm, termVal]
      let yLit : Fin a → ℕ × ℕ := fun b =>
        if j.val.testBit b.val then yW ⟨b.val, by omega⟩ else drNot (yW ⟨b.val, by omega⟩)
      obtain ⟨⟨e1, he1, hm1, hl1⟩, hv1, hh1⟩ := drFoldAnd_spec base (gsG ++ ext) wT yLit (List.finRange a)
      obtain ⟨⟨e2, he2, hm2, hl2⟩, hv2, hh2⟩ := drAnd_spec base
        (drFoldAnd base (gsG ++ ext) wT yLit (List.finRange a)).1
        (drFoldAnd base (gsG ++ ext) wT yLit (List.finRange a)).2
        (xW ⟨j.val, lt_of_lt_of_le j.isLt hrk⟩)
      have hyLit_v : ∀ b ∈ List.finRange a, drValid base (gsG ++ ext) (yLit b) := by
        intro b _
        dsimp only [yLit]
        split_ifs
        · exact drValid_append (hyW_vG _)
        · exact drValid_not (drValid_append (hyW_vG _))
      have hv1' : drValid base (drFoldAnd base (gsG ++ ext) wT yLit (List.finRange a)).1
          (drFoldAnd base (gsG ++ ext) wT yLit (List.finRange a)).2 :=
        hv1 (drValid_not (drValid_append hwF_vG)) hyLit_v
      refine ⟨⟨e1 ++ e2, ?_, isMono_append hm1 hm2, ?_⟩, hv2, ?_⟩
      · rw [he2, he1, List.append_assoc]
      · simp only [List.length_append, hl1, hl2, List.length_finRange]; omega
      · intro inp hinp
        have hyLit_h : ∀ b ∈ List.finRange a,
            drHolds (gsG ++ ext) inp (yLit b) (decide (yBit inp ⟨b.val, by omega⟩ = j.val.testBit b.val)) := by
          intro b _
          dsimp only [yLit]
          have hbase : drHolds (gsG ++ ext) inp (yW ⟨b.val, by omega⟩) (yBit inp ⟨b.val, by omega⟩) :=
            drHolds_append (extra := ext) (by rw [hinp.1]; exact hyW_vG _) (hyW_hG inp hinp ⟨b.val, by omega⟩)
          cases hj : j.val.testBit b.val
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hnot := drHolds_not hbase
            have hb : (!yBit inp ⟨b.val, by omega⟩) = decide (yBit inp ⟨b.val, by omega⟩ = false) := by
              cases yBit inp ⟨b.val, by omega⟩ <;> decide
            rwa [hb] at hnot
          · simp only [↓reduceIte]
            have hb : yBit inp ⟨b.val, by omega⟩ = decide (yBit inp ⟨b.val, by omega⟩ = true) := by
              cases yBit inp ⟨b.val, by omega⟩ <;> decide
            rwa [hb] at hbase
        have hfold := hh1 inp true (fun b => decide (yBit inp ⟨b.val, by omega⟩ = j.val.testBit b.val))
          hinp.1 (drValid_not (drValid_append hwF_vG)) hyLit_v
          (drHolds_not (drHolds_append (by rw [hinp.1]; exact hwF_vG) (hwF_hG inp hinp))) hyLit_h
        rw [foldl_and_eq_decide] at hfold
        have hiff : (∀ b ∈ List.finRange a, decide (yBit inp ⟨b.val, by omega⟩ = j.val.testBit b.val) = true) ↔
            (∀ b : Fin a, yBit inp ⟨b.val, by omega⟩ = j.val.testBit b.val) := by
          constructor
          · intro h b; exact of_decide_eq_true (h b (List.mem_finRange b))
          · intro h b _; exact decide_eq_true (h b)
        rw [decide_eq_decide.mpr hiff] at hfold
        have hx_v1 : drValid base (drFoldAnd base (gsG ++ ext) wT yLit (List.finRange a)).1
            (xW ⟨j.val, lt_of_lt_of_le j.isLt hrk⟩) := by
          rw [he1]; exact drValid_append (drValid_append (hxW_vG _))
        have hx_h1 : drHolds (drFoldAnd base (gsG ++ ext) wT yLit (List.finRange a)).1 inp
            (xW ⟨j.val, lt_of_lt_of_le j.isLt hrk⟩) (xBit inp ⟨j.val, lt_of_lt_of_le j.isLt hrk⟩) := by
          rw [he1, List.append_assoc]
          exact drHolds_append (by rw [hinp.1]; exact hxW_vG _) (hxW_hG inp hinp _)
        exact hh2 inp (decide (∀ b : Fin a, yBit inp ⟨b.val, by omega⟩ = j.val.testBit b.val))
          (xBit inp ⟨j.val, lt_of_lt_of_le j.isLt hrk⟩) hinp.1 hv1' hx_v1 hfold hx_h1)
  obtain ⟨⟨eT, heT, hmT, hlT⟩, hvT, hhT⟩ := hresT
  generalize hgT : (drBuildList gsG (List.finRange r) buildTerm).1 = gsT at heT hvT hhT
  generalize hwT : (drBuildList gsG (List.finRange r) buildTerm).2 = termW at hvT hhT
  clear hgT hwT
  have hgsT_m : isMono gsT := by rw [heT]; exact isMono_append hgsG_m hmT
  have hgsT_l : gsT.length ≤ gsG.length + r * (2 * a + 2) := by
    have hsum : ((List.finRange r).map (fun _ : Fin r => 2 * a + 2)).sum ≤ r * (2 * a + 2) := by
      simp
    rw [heT, List.length_append]; omega
  have hwF_vT : drValid base gsT wF := by rw [heT]; exact drValid_append hwF_vG
  have hwF_hT : ∀ inp, isLitInp inp → drHolds gsT inp wF false := fun inp hinp => by
    rw [heT]; exact drHolds_append (by rw [hinp.1]; exact hwF_vG) (hwF_hG inp hinp)
  have hwG_vT : drValid base gsT wG := by rw [heT]; exact drValid_append hwG_v
  have hwG_hT : ∀ inp, isLitInp inp → drHolds gsT inp wG (gammaVal inp) := fun inp hinp => by
    rw [heT]; exact drHolds_append (by rw [hinp.1]; exact hwG_v) (hwG_h inp hinp)
  obtain ⟨⟨eB, heB, hmB, hlB⟩, hvB, hhB⟩ := drFoldOr_spec base gsT wF termW (List.finRange r)
  generalize hgB : (drFoldOr base gsT wF termW (List.finRange r)).1 = gsB at heB hvB hhB
  generalize hwB : (drFoldOr base gsT wF termW (List.finRange r)).2 = wB at hvB hhB
  clear hgB hwB
  have hgsB_m : isMono gsB := by rw [heB]; exact isMono_append hgsT_m hmB
  have hgsB_l : gsB.length ≤ gsT.length + 2 * r := by
    rw [heB, List.length_append, hlB, List.length_finRange]
  have hwB_v : drValid base gsB wB := hvB hwF_vT (fun j _ => hvT j (List.mem_finRange j))
  have hwG_vB : drValid base gsB wG := by rw [heB]; exact drValid_append hwG_vT
  have hwG_hB : ∀ inp, isLitInp inp → drHolds gsB inp wG (gammaVal inp) := fun inp hinp => by
    rw [heB]; exact drHolds_append (by rw [hinp.1]; exact hwG_vT) (hwG_hT inp hinp)
  let baseVal : List Bool → Bool := fun inp => decide (∃ j : Fin r, termVal inp j = true)
  have hwB_h : ∀ inp, isLitInp inp → drHolds gsB inp wB (baseVal inp) := by
    intro inp hinp
    have h1 := hhB inp false (termVal inp) hinp.1 hwF_vT (fun j _ => hvT j (List.mem_finRange j))
      (hwF_hT inp hinp) (fun j _ => hhT inp hinp j (List.mem_finRange j))
    rw [foldl_or_eq_decide] at h1
    have hiff : (∃ j ∈ List.finRange r, termVal inp j = true) ↔ (∃ j : Fin r, termVal inp j = true) :=
      ⟨fun ⟨j, _, hj⟩ => ⟨j, hj⟩, fun ⟨j, hj⟩ => ⟨j, List.mem_finRange j, hj⟩⟩
    rwa [decide_eq_decide.mpr hiff] at h1
  obtain ⟨⟨eO, heO, hmO, hlO⟩, hvO, hhO⟩ := drXor_spec base gsB wB wG
  generalize hgO : (drXor base gsB wB wG).1 = gsO at heO hvO hhO
  generalize hwO : (drXor base gsB wB wG).2 = wO at hvO hhO
  clear hgO hwO
  have hgsO_m : isMono gsO := by rw [heO]; exact isMono_append hgsB_m hmO
  have hgsO_l : gsO.length ≤ 150 * (k + 1) ^ 2 := by
    have hmle : m ≤ k := by dsimp [m]; omega
    have h1 : m * m ≤ k * k := Nat.mul_le_mul hmle hmle
    have h2 : r * (2 * a + 2) ≤ k * (2 * k + 2) := Nat.mul_le_mul hrk (by omega)
    rw [heO, List.length_append, hlO]
    nlinarith
  refine ⟨⟨gsO, wO.1⟩, isMono_to_Monotone2 hgsO_m wO.1, hgsO_l, ?_⟩
  intro z
  let inp : List Bool := List.ofFn z ++ List.ofFn fun i => !z i
  have hli : isLitInp inp := by
    refine ⟨litInput_length z, ?_⟩
    intro i
    rw [litInput_getD_neg z i, litInput_getD_pos z i]
  have hout := (hhO inp (baseVal inp) (gammaVal inp) hli.1 hwB_v hwG_vB (hwB_h inp hli) (hwG_hB inp hli)).1
  change (runGates gsO inp).getD wO.1 false = _
  rw [hout]
  dsimp only [adjFun]
  let X : ℕ := tableIndex fun i : Fin k => z (Fin.castAdd k i)
  let Y : ℕ := tableIndex fun j : Fin k => z (Fin.natAdd k j)
  have hXlt : X < 2 ^ k := tableIndex_lt _
  have hYlt : Y < 2 ^ k := tableIndex_lt _
  have hXval : (Fin.ofNat (2 ^ k) X).val = X := by
    simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hXlt]
  have hYval : (Fin.ofNat (2 ^ k) Y).val = Y := by
    simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hYlt]
  rw [hXval, hYval]
  have hxBit_eq : ∀ i : Fin k, xBit inp i = X.testBit i.val := by
    intro i
    dsimp only [xBit, X]
    rw [tableIndex_testBit]
    simp only [i.isLt, ↓reduceDIte]
    have h := litInput_getD_pos z (Fin.castAdd k i)
    dsimp only [Fin.castAdd] at h
    exact h
  have hyBit_eq : ∀ i : Fin k, yBit inp i = Y.testBit i.val := by
    intro i
    dsimp only [yBit, Y]
    rw [tableIndex_testBit]
    simp only [i.isLt, ↓reduceDIte]
    have h := litInput_getD_pos z (Fin.natAdd k i)
    dsimp only [Fin.natAdd] at h
    exact h
  have hdBit_eq : ∀ i : Fin k, dBit inp i = (X ^^^ Y).testBit i.val := by
    intro i
    dsimp only [dBit]
    rw [hxBit_eq i, hyBit_eq i, Nat.testBit_xor]
  have hbase_eq : baseVal inp = X.testBit (Y % r) := by
    dsimp only [baseVal, termVal]
    have hyMod : ∀ j : Fin r,
        (∀ b : Fin a, yBit inp ⟨b.val, by omega⟩ = j.val.testBit b.val) ↔ Y % r = j.val := by
      intro j
      constructor
      · intro hb
        apply Nat.eq_of_testBit_eq
        intro t
        by_cases ht : t < a
        · rw [Nat.testBit_mod_two_pow, decide_eq_true ht, Bool.true_and]
          have := hb ⟨t, ht⟩
          rw [hyBit_eq ⟨t, by omega⟩] at this
          exact this
        · have hge : a ≤ t := by omega
          have h1 : (Y % r).testBit t = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt Y (Nat.pow_pos (by omega)))
              (Nat.pow_le_pow_right (by omega) hge))
          have h2 : j.val.testBit t = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by omega) hge))
          rw [h1, h2]
      · intro heq b
        rw [hyBit_eq ⟨b.val, by omega⟩, ← heq, Nat.testBit_mod_two_pow, decide_eq_true b.isLt, Bool.true_and]
    have hlt_r : Y % r < r := Nat.mod_lt Y (Nat.pow_pos (by omega))
    cases hxt : X.testBit (Y % r)
    · rw [decide_eq_false_iff_not]
      rintro ⟨j, hj⟩
      rw [Bool.and_eq_true, decide_eq_true_eq] at hj
      have heq := (hyMod j).mp hj.1
      rw [hxBit_eq, ← heq] at hj
      rw [hxt] at hj
      exact Bool.false_ne_true hj.2
    · rw [decide_eq_true_iff]
      refine ⟨⟨Y % r, hlt_r⟩, ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨(hyMod ⟨Y % r, hlt_r⟩).mpr rfl, by rw [hxBit_eq]; exact hxt⟩
  have hgamma_eq : gammaVal inp = decide (Nat.xor X Y ∈ gammaSet m P) := by
    have hpVal_eq : ∀ t : Fin (3 * m), pVal inp t = pBit m (X ^^^ Y) t.val := by
      intro t
      dsimp only [pVal, pBit, dLoBit]
      have hcongr : ∀ (l : List (Fin m × Fin m)) (init : Bool),
          l.foldl (fun acc ij => xor acc (dBit inp ⟨ij.1.val, by omega⟩ && dBit inp ⟨ij.2.val, by omega⟩)) init =
          l.foldl (fun acc ij => xor acc ((X ^^^ Y).testBit ij.1.val && (X ^^^ Y).testBit ij.2.val)) init := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons ij rest ih =>
          intro init
          simp only [List.foldl_cons, hdBit_eq]
      exact hcongr (pairsFor m t.val) false
    have hqVal_eq : ∀ c : Fin m, qVal inp c = qBit m P (X ^^^ Y) c.val := by
      intro c
      dsimp only [qVal, qBit]
      have hcongr : ∀ (l : List (Fin (3 * m))) (init : Bool),
          l.foldl (fun acc t => xor acc (pVal inp t)) init =
          l.foldl (fun acc t => xor acc (pBit m (X ^^^ Y) t.val)) init := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons t rest ih =>
          intro init
          simp only [List.foldl_cons, hpVal_eq]
      exact hcongr (redTerms m P c.val) false
    have hd_lt : X ^^^ Y < 2 ^ k := xor_lt_pow_two hXlt hYlt
    dsimp only [gammaVal, eqVal]
    apply decide_eq_decide.mpr
    change ((∀ c : Fin m, decide (dBit inp ⟨m + c.val, _⟩ = qVal inp c) = true) ∧
        (∀ h : 2 * m < k, dBit inp ⟨2 * m, h⟩ = false)) ↔
      (X ^^^ Y) ∈ gammaSet (k / 2) P
    rw [mem_gammaSet_iff_bits k P (X ^^^ Y) hd_lt]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun c => ?_, fun h => ?_⟩
      · have := of_decide_eq_true (h1 c)
        rw [hdBit_eq, hqVal_eq] at this
        exact this
      · have := h2 h
        rwa [hdBit_eq] at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun c => ?_, fun h => ?_⟩
      · rw [decide_eq_true_eq, hdBit_eq, hqVal_eq]
        exact h1 c
      · rw [hdBit_eq]
        exact h2 h
  rw [hbase_eq, hgamma_eq]

end Lit

end PEqualNP.Outside.L_meta_25879

namespace PEqualNP.Outside.L_meta_25879.Struct

open Finset

def dist {α : Type*} [Fintype α] (f g : α → Bool) : ℕ :=
  (univ.filter fun i => f i ≠ g i).card

theorem dist_triangle {α : Type*} [Fintype α] (f g h : α → Bool) :
    dist f h ≤ dist f g + dist g h := by
  classical
  apply le_trans (card_le_card (t := (univ.filter fun i => f i ≠ g i) ∪
      (univ.filter fun i => g i ≠ h i)) _ ) (card_union_le _ _)
  intro i hi
  simp only [mem_filter, mem_univ, true_and, mem_union] at hi ⊢
  by_cases e : f i = g i
  · exact Or.inr fun eq => hi (e.trans eq)
  · exact Or.inl e

theorem dist_symm {α : Type*} [Fintype α] (f g : α → Bool) : dist f g = dist g f := by
  simp [dist, ne_comm]

theorem dist_le_of_agree {α : Type*} [Fintype α] (f g : α → Bool) (s : Finset α)
    (h : ∀ i ∉ s, f i = g i) : dist f g ≤ s.card := by
  apply card_le_card
  intro i hi
  by_contra hs
  exact (mem_filter.mp hi).2 (h i hs)

theorem good_dist {α : Type*} [Fintype α] (f g f' g' : α → Bool) (v : ℕ)
    (hv : 0 < v) (hf : dist f f' < v) (hg : dist g g' < v)
    (hd : 17 + 2 * (v - 1) ≤ dist f' g') : 17 ≤ dist f g := by
  have h1 := dist_triangle f' f g'
  have h2 := dist_triangle f g g'
  rw [dist_symm f' f] at h1
  omega

theorem error_rows {α : Type*} [Fintype α] (H T : α → α → Bool) (v : ℕ) :
    (univ.filter fun i => v ≤ dist (H i) (T i)).card ≤
      (univ.filter (fun z : α × α => H z.1 z.2 ≠ T z.1 z.2)).card / v ∨ v = 0 := by
  classical
  by_cases hv : v = 0
  · exact Or.inr hv
  left
  rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hv)]
  let s := univ.filter fun i => v ≤ dist (H i) (T i)
  let E := univ.filter fun z : α × α => H z.1 z.2 ≠ T z.1 z.2
  change s.card * v ≤ E.card
  have he : E.card = ∑ i : α, dist (H i) (T i) := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
    apply sum_congr rfl
    intro i _
    have hm : (E.filter fun z => z.1 = i) =
        (univ.filter fun j => H i j ≠ T i j).map
          ⟨fun j => (i,j), fun _ _ h => congrArg Prod.snd h⟩ := by
      ext ⟨x,y⟩
      simp only [E, mem_filter, mem_univ, true_and, mem_map]
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨y, h, rfl⟩
      · rintro ⟨j, h, heq⟩
        cases heq
        exact ⟨h, rfl⟩
    rw [hm, card_map]
    rfl
  rw [he, ← sum_const_nat (f := fun _ : α => v) (fun _ _ => rfl)]
  exact (sum_le_sum fun i hi => (mem_filter.mp hi).2).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _)

theorem error_transpose {α : Type*} [Fintype α] (H T : α → α → Bool) :
    (univ.filter (fun z : α × α => H z.2 z.1 ≠ T z.2 z.1)).card =
      (univ.filter (fun z : α × α => H z.1 z.2 ≠ T z.1 z.2)).card := by
  classical
  apply card_bij' (fun z _ => z.swap) (fun z _ => z.swap)
  all_goals simp_all

theorem ordered_pairs {α : Type*} [LinearOrder α] (s : Finset α) (h : s.card ≤ 3) :
    ((s ×ˢ s).filter fun z => z.1 < z.2).card ≤ s.card := by
  let A := (s ×ˢ s).filter fun z => z.1 < z.2
  let B := A.map (Equiv.prodComm α α).toEmbedding
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hz ha
    obtain ⟨w, hw, rfl⟩ := mem_map.mp ha
    exact (not_lt_of_gt (mem_filter.mp hw).2) (mem_filter.mp hz).2
  have hsub : A ∪ B ⊆ s.offDiag := by
    intro z hz
    rw [mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨hh, hlt⟩ := mem_filter.mp hz
      exact mem_offDiag.mpr ⟨(mem_product.mp hh).1, (mem_product.mp hh).2, ne_of_lt hlt⟩
    · obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
      obtain ⟨hh, hlt⟩ := mem_filter.mp hw
      exact mem_offDiag.mpr ⟨(mem_product.mp hh).2, (mem_product.mp hh).1, ne_of_gt hlt⟩
  have hb : B.card = A.card := card_map _
  have hh := card_le_card hsub
  rw [card_union_of_disjoint hAB, hb, offDiag_card] at hh
  change A.card ≤ s.card
  rcases (by omega : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3) with hm | hm | hm | hm <;> rw [hm] at hh ⊢ <;> omega

theorem conflict_bound {α : Type*} [LinearOrder α] (T H : α → α → Bool)
    (π : Equiv.Perm α) (S : Finset α) (p : α → ℕ)
    (hm : ∀ t, (S.filter fun i => p i = t).card ≤ 3)
    (hs : ∀ i ∈ S, ∀ j ∈ S, p i ≠ p j → H i (π j) = H j (π i))
    (U : Finset α) (hU : U ⊆ S) :
    ((U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))).card ≤
      U.card + ((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).card := by
  classical
  let A := (U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))
  let E := (U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))
  let same := A.filter fun z => p z.1 = p z.2
  let diff := A.filter fun z => p z.1 ≠ p z.2
  have hpart : same.card + diff.card = A.card := card_filter_add_card_filter_not ..
  have hsame : same.card ≤ U.card := by
    rw [card_eq_sum_card_fiberwise (f := fun z : α × α => p z.1) (t := U.image p),
      card_eq_sum_card_image p U]
    · apply sum_le_sum
      intro t _
      let V := U.filter fun i => p i = t
      change (same.filter fun z => p z.1 = t).card ≤ V.card
      have hv : V.card ≤ 3 := (card_le_card (filter_subset_filter _ hU)).trans (hm t)
      apply le_trans (card_le_card (t := (V ×ˢ V).filter fun z => z.1 < z.2) ?_) (ordered_pairs V hv)
      intro z hz
      rcases mem_filter.mp hz with ⟨hz, hzt⟩
      rcases mem_filter.mp hz with ⟨hz, hze⟩
      rcases mem_filter.mp hz with ⟨hz, hlt, _⟩
      rcases mem_product.mp hz with ⟨hi, hj⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨hi,hzt⟩,
        mem_filter.mpr ⟨hj,hze.symm.trans hzt⟩⟩, hlt⟩
    · intro z hz
      exact mem_image_of_mem p (mem_product.mp (mem_filter.mp (mem_filter.mp hz).1).1).1
  have hdiff : diff.card ≤ E.card := by
    let f : α × α → α × α := fun z => if T z.1 (π z.2) ≠ H z.1 (π z.2) then z else z.swap
    apply card_le_card_of_injOn f
    · intro z hz
      rcases mem_filter.mp hz with ⟨hz, hne⟩
      rcases mem_filter.mp hz with ⟨hz, _, htt⟩
      rcases mem_product.mp hz with ⟨hi,hj⟩
      by_cases he : T z.1 (π z.2) ≠ H z.1 (π z.2)
      · change f z ∈ E
        simp only [f, ite_eq_left he]
        exact mem_filter.mpr ⟨hz, he⟩
      · have he' : T z.2 (π z.1) ≠ H z.2 (π z.1) := by
          intro hk
          exact htt ((not_ne_iff.mp he).trans ((hs _ (hU hi) _ (hU hj) hne).trans hk.symm))
        change f z ∈ E
        simp only [f, ite_eq_right he]
        exact mem_filter.mpr ⟨mem_product.mpr ⟨hj, hi⟩, he'⟩
    · intro a ha b hb hab
      have ha' := (mem_filter.mp (mem_filter.mp ha).1).2.1
      have hb' := (mem_filter.mp (mem_filter.mp hb).1).2.1
      unfold f at hab
      split at hab <;> split at hab
      · exact hab
      · subst a
        exact (lt_asymm hb' ha').elim
      · subst b
        exact (lt_asymm ha' hb').elim
      · exact congrArg Prod.swap hab
  change A.card ≤ U.card + E.card
  omega

theorem match_keys {α κ : Type*} [Fintype α] [DecidableEq α] [DecidableEq κ]
    (A B : Finset α) (a b : α → κ) (ha : Set.InjOn a A) (hb : Set.InjOn b B) :
    ∃ (π : Equiv.Perm α) (S : Finset α),
      S.card + (A.image a ∪ B.image b).card = A.card + B.card ∧
      S ⊆ A ∧ ∀ i ∈ S, π i ∈ B ∧ a i = b (π i) := by
  classical
  let S := A.filter fun i => a i ∈ B.image b
  have hm : ∀ i ∈ S, ∃ j ∈ B, b j = a i := fun i hi => mem_image.mp (mem_filter.mp hi).2
  let f : α → α := fun i => if h : i ∈ S then (hm i h).choose else i
  have hf : ∀ i ∈ S, f i ∈ B ∧ b (f i) = a i := by
    intro i hi
    simpa only [f, dite_eq_left hi] using (hm i hi).choose_spec
  have hinj : Set.InjOn f S := by
    intro i hi j hj hij
    apply ha (filter_subset _ _ hi) (filter_subset _ _ hj)
    rw [← (hf i hi).2, ← (hf j hj).2, hij]
  obtain ⟨π, hπ⟩ := exists_equiv_extend_of_card_eq (t := univ) (by simp)
    (show S.image f ⊆ univ from subset_univ _) hinj
  let idu : (univ : Finset α) ≃ α :=
    ⟨Subtype.val, fun x => ⟨x, mem_univ x⟩, fun _ => rfl, fun _ => rfl⟩
  refine ⟨π.trans idu, S, ?_, filter_subset _ _, ?_⟩
  · have hS : S.image a = A.image a ∩ B.image b := by
      ext k
      simp only [S, mem_image, mem_filter, mem_inter]
      constructor
      · rintro ⟨i, ⟨hi, hk⟩, rfl⟩
        exact ⟨⟨i, hi, rfl⟩, hk⟩
      · rintro ⟨⟨i, hi, rfl⟩, hk⟩
        exact ⟨i, ⟨hi, hk⟩, rfl⟩
    have hk := card_union_add_card_inter (A.image a) (B.image b)
    rw [← hS, card_image_of_injOn (ha.mono (filter_subset _ _)),
      card_image_of_injOn ha, card_image_of_injOn hb] at hk
    simpa [S, add_comm] using hk
  · intro i hi
    change (π i : α) ∈ B ∧ a i = b (π i : α)
    rw [hπ i hi]
    exact ⟨(hf i hi).1, (hf i hi).2.symm⟩

open Finset

inductive Op where
  | raw
  | lit (b : Bool)
  | one (f : Bool → Bool) (a : ℕ)
  | two (f : Bool → Bool → Bool) (a b : ℕ)

def Op.pin : Op → Bool → Option ℕ
  | .one _ a, s => if s then none else some a
  | .two _ a b, s => some (if s then b else a)
  | _, _ => none

def Op.arity : Op → ℕ
  | .raw | .lit _ => 0
  | .one .. => 1
  | .two .. => 2

def Op.value : Op → Bool → (ℕ → Bool) → Bool
  | .raw, x, _ => x
  | .lit b, _, _ => b
  | .one f a, _, v => f (v a)
  | .two f a b, _, v => f (v a) (v b)

structure Net where
  code : ℕ → Op
  out : ℕ
  back : ∀ {w s a}, (code w).pin s = some a → a < w

def Net.run (N : Net) (x : ℕ → Bool) (w : ℕ) : Bool :=
  (N.code w).value (x w) fun a => if a < w then N.run x a else false
termination_by w

theorem Net.run_eq (N : Net) (x : ℕ → Bool) (w : ℕ) :
    N.run x w = (N.code w).value (x w) (N.run x) := by
  rw [Net.run]
  cases h : N.code w with
  | raw => rfl
  | lit b => rfl
  | one f a =>
    have ha : a < w := N.back (s := false) (by simp [h, Op.pin])
    simp [Op.value, ha]
  | two f a b =>
    have ha : a < w := N.back (s := false) (by simp [h, Op.pin])
    have hb : b < w := N.back (s := true) (by simp [h, Op.pin])
    simp [Op.value, ha, hb]

inductive Net.Reach (N : Net) : ℕ → Prop where
  | top : Reach N N.out
  | child {w a s : _} : Reach N w → (N.code w).pin s = some a → Reach N a

theorem Net.reach_le (N : Net) {w : ℕ} (hw : N.Reach w) : w ≤ N.out := by
  induction hw with
  | top => rfl
  | child _ hp ih => exact (N.back hp).le.trans ih

noncomputable section

def Net.live (N : Net) : Finset ℕ := by
  classical
  exact (range (N.out + 1)).filter N.Reach

@[simp] theorem Net.mem_live (N : Net) {a} : a ∈ N.live ↔ N.Reach a := by
  classical
  simp only [live, mem_filter, mem_range]
  exact ⟨And.right, fun h => ⟨Nat.lt_succ_of_le (N.reach_le h), h⟩⟩

def Net.edges (N : Net) : Finset (ℕ × Bool) :=
  (N.live ×ˢ univ).filter fun z => ((N.code z.1).pin z.2).isSome

def Net.src (N : Net) (e : ℕ × Bool) : ℕ := ((N.code e.1).pin e.2).getD 0

theorem Net.pin_src {N : Net} {e} (he : e ∈ N.edges) :
    (N.code e.1).pin e.2 = some (N.src e) := by
  have h := (mem_filter.mp he).2
  cases hc : (N.code e.1).pin e.2 <;> simp_all [Net.src]

theorem Net.edge_of_pin {N : Net} {w s a} (hw : w ∈ N.live)
    (h : (N.code w).pin s = some a) : (w,s) ∈ N.edges ∧ N.src (w,s) = a := by
  simp [Net.edges, Net.src, hw, h]

theorem Net.edge_live {N : Net} {e} (he : e ∈ N.edges) : e.1 ∈ N.live :=
  (mem_product.mp (mem_filter.mp he).1).1

theorem Net.src_live {N : Net} {e} (he : e ∈ N.edges) : N.src e ∈ N.live :=
  N.mem_live.mpr (.child (N.mem_live.mp (N.edge_live he)) (N.pin_src he))

def Net.uses (N : Net) (a : ℕ) : Finset (ℕ × Bool) := N.edges.filter fun e => N.src e = a

def Net.deg (N : Net) (a : ℕ) : ℕ := (N.uses a).card

def Net.shared (N : Net) (a : ℕ) : Prop := 2 ≤ N.deg a

instance (N : Net) (a : ℕ) : Decidable (N.shared a) :=
  inferInstanceAs (Decidable (2 ≤ N.deg a))

theorem Net.deg_pos {N : Net} {a} (ha : a ∈ N.live) (hne : a ≠ N.out) : 0 < N.deg a := by
  rcases N.mem_live.mp ha with ht | @⟨w, a, s, hw, hp⟩
  · exact (hne rfl).elim
  · obtain ⟨he, hs⟩ := N.edge_of_pin (N.mem_live.mpr hw) hp
    exact card_pos.mpr ⟨(w,s), mem_filter.mpr ⟨he, hs⟩⟩

theorem Net.not_out_src {N : Net} {e} (he : e ∈ N.edges) : N.src e ≠ N.out := by
  have hlt := N.back (N.pin_src he)
  have hle := N.reach_le (N.mem_live.mp (N.edge_live he))
  omega

theorem Net.deg_out (N : Net) : N.deg N.out = 0 := by
  rw [Net.deg, card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  exact N.not_out_src (mem_filter.mp he).1 (mem_filter.mp he).2

theorem Net.use_unique {N : Net} {e e' : ℕ × Bool} (he : e ∈ N.edges) (he' : e' ∈ N.edges)
    (hs : N.src e = N.src e') (hc : ¬N.shared (N.src e)) : e = e' := by
  by_contra h
  have hsub : {e,e'} ⊆ N.uses (N.src e) := by simp [insert_subset_iff, Net.uses, he, he', hs]
  have hcard := card_le_card hsub
  exact hc (by simpa [h, Net.deg, Net.shared] using hcard)

def Net.excess (N : Net) : ℕ := ∑ a ∈ N.live, (N.deg a - 1)

theorem Net.card_pin_fiber (N : Net) {w : ℕ} (hw : w ∈ N.live) :
    (N.edges.filter fun e => e.1 = w).card = (N.code w).arity := by
  let f : Bool ↪ ℕ × Bool := ⟨fun b => (w,b), fun _ _ h => congrArg Prod.snd h⟩
  have hh : (N.edges.filter fun e => e.1 = w) =
      (univ.filter fun s => ((N.code w).pin s).isSome).map f := by
    ext ⟨p,s⟩
    simp only [Net.edges, mem_filter, mem_product, mem_univ, and_true, true_and, mem_map]
    constructor
    · rintro ⟨⟨_,h⟩,rfl⟩
      exact ⟨s,h,rfl⟩
    · rintro ⟨t,h,he⟩
      cases he
      exact ⟨⟨hw,h⟩,rfl⟩
  rw [hh, card_map]
  cases N.code w <;> simp [Op.pin, Op.arity]
  have h : ({s ∈ ({true,false} : Finset Bool) | s = false} : Finset Bool) = {false} := by
    ext s; cases s <;> simp
  rw [h, card_singleton]

theorem Net.ledger (N : Net) :
    N.excess + (N.live.filter fun a => (N.code a).arity = 0).card =
      (N.live.filter fun a => (N.code a).arity = 2).card + 1 := by
  classical
  have h1 : N.edges.card = ∑ a ∈ N.live, N.deg a :=
    card_eq_sum_card_fiberwise (f := N.src) fun _ ha => N.src_live ha
  have h2 : N.edges.card = ∑ a ∈ N.live, (N.code a).arity := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := N.live) fun _ he => N.edge_live he]
    exact sum_congr rfl fun _ ha => N.card_pin_fiber ha
  have ho : N.out ∈ N.live := N.mem_live.mpr .top
  have h3 : (∑ a ∈ N.live, N.deg a) + 1 = N.excess + N.live.card := by
    have hh : (∑ a ∈ N.live, (N.deg a + if a = N.out then 1 else 0)) =
        ∑ a ∈ N.live, ((N.deg a - 1) + 1) := by
      apply sum_congr rfl
      intro a ha
      by_cases h : a = N.out
      · subst a; simp [N.deg_out]
      · have := N.deg_pos ha h
        simp only [ite_eq_right h]; omega
    simpa [sum_add_distrib, ho, Net.excess] using hh
  have h4 : (∑ a ∈ N.live, (N.code a).arity) + (N.live.filter fun a => (N.code a).arity = 0).card =
      N.live.card + (N.live.filter fun a => (N.code a).arity = 2).card := by
    have hh : (∑ a ∈ N.live, ((N.code a).arity + if (N.code a).arity = 0 then 1 else 0)) =
        ∑ a ∈ N.live, (1 + if (N.code a).arity = 2 then 1 else 0) := by
      apply sum_congr rfl
      intro a _
      cases N.code a <;> simp [Op.arity]
    simpa [sum_add_distrib, sum_filter] using hh
  omega

theorem Net.shared_le (N : Net) : (N.live.filter N.shared).card ≤ N.excess := by
  classical
  calc
    _ = ∑ a ∈ N.live.filter N.shared, 1 := by simp
    _ ≤ ∑ a ∈ N.live.filter N.shared, (N.deg a - 1) := by
      apply sum_le_sum
      intro a ha
      exact Nat.le_sub_of_add_le (mem_filter.mp ha).2
    _ ≤ N.excess := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

def Net.cut (N : Net) (bad : Finset ℕ) (a : ℕ) : Prop := N.shared a ∨ a ∈ bad

def Net.holeEdges (N : Net) (bad : Finset ℕ) : Finset (ℕ × Bool) := by
  classical
  exact N.edges.filter fun e => N.cut bad (N.src e)

theorem Net.cut_edges_le (N : Net) (bad : Finset ℕ) :
    (N.holeEdges bad).card ≤ 2 * N.excess + bad.card := by
  classical
  rw [card_eq_sum_card_fiberwise (s := N.holeEdges bad) (f := N.src) (t := N.live)
    (fun _ he => N.src_live (mem_filter.mp he).1)]
  have hb : (∑ a ∈ N.live, (if a ∈ bad then 1 else 0)) ≤ bad.card := by
    rw [← sum_filter]
    simpa using (card_le_card (show N.live.filter (· ∈ bad) ⊆ bad from fun _ h => (mem_filter.mp h).2))
  have hh : (∑ a ∈ N.live, ((N.holeEdges bad).filter fun e => N.src e = a).card) ≤
      ∑ a ∈ N.live, (2 * (N.deg a - 1) + if a ∈ bad then 1 else 0) := by
    apply sum_le_sum
    intro a _
    by_cases hc : N.cut bad a
    · have hEq : ((N.holeEdges bad).filter fun e => N.src e = a) = N.uses a := by
        ext e
        simp only [Net.holeEdges, Net.uses, mem_filter]
        grind
      rw [hEq, ← Net.deg]
      rcases hc with he | he
      · have : 2 ≤ N.deg a := he
        omega
      · simp [he]; omega
    · have he : ((N.holeEdges bad).filter fun e => N.src e = a) = ∅ := by
        ext e
        simp only [Net.holeEdges, mem_filter, notMem_empty, iff_false]
        grind
      simp [he]
  rw [sum_add_distrib, ← mul_sum, ← Net.excess] at hh
  omega

end

open Finset

structure Frag where
  raw : Finset ℕ
  hole : Option ℕ
  f : (ℕ → Bool) → Bool → Bool
  congrRaw : ∀ (x y : ℕ → Bool), (∀ a ∈ raw, x a = y a) → ∀ b, f x b = f y b
  ignore : hole = none → ∀ x b c, f x b = f x c

def Frag.eval (F : Frag) (x y : ℕ → Bool) : Bool := F.f x (F.hole.elim false y)

def Frag.bit (a : ℕ) : Frag := by
  refine ⟨{a}, none, fun x _ => x a, ?_, fun _ _ _ _ => rfl⟩
  exact fun x y h _ => h a (mem_singleton_self a)

def Frag.lit (b : Bool) : Frag :=
  ⟨∅, none, fun _ _ => b, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def Frag.entry (a : ℕ) : Frag :=
  ⟨∅, some a, fun _ b => b, fun _ _ _ _ => rfl, fun h => by cases h⟩

def Frag.unary (f : Bool → Bool) (A : Frag) : Frag :=
  ⟨A.raw, A.hole, fun x b => f (A.f x b),
    fun x y h b => congrArg f (A.congrRaw x y h b),
    fun h x b c => congrArg f (A.ignore h x b c)⟩

def Frag.binary (f : Bool → Bool → Bool) (A B : Frag) : Frag := by
  refine ⟨A.raw ∪ B.raw, A.hole.or B.hole, fun x b => f (A.f x b) (B.f x b), ?_, ?_⟩
  · intro x y h b
    rw [A.congrRaw x y (fun a ha => h a (mem_union_left _ ha)),
      B.congrRaw x y (fun a ha => h a (mem_union_right _ ha))]
  · intro h x b c
    have ha : A.hole = none := by cases ah : A.hole <;> simp_all [Option.or]
    have hb : B.hole = none := by simpa [ha, Option.or] using h
    rw [A.ignore ha x b c, B.ignore hb x b c]

theorem Frag.binary_eval (f : Bool → Bool → Bool) (A B : Frag) (x y : ℕ → Bool)
    (h : ¬(A.hole.isSome && B.hole.isSome) = true) :
    (Frag.binary f A B).eval x y = f (A.eval x y) (B.eval x y) := by
  obtain ⟨as, ah, af, ac, ai⟩ := A
  obtain ⟨bs, bh, bf, bc, bi⟩ := B
  cases ah <;> cases bh <;> simp_all [Frag.eval, Frag.binary, Option.or]
  all_goals first | rw [ai rfl] | rw [bi rfl]

noncomputable section

def Net.mask (N : Net) (bad : Finset ℕ) (a : ℕ) (F : Frag) : Frag := by
  classical
  exact if N.cut bad a then Frag.entry a else F

def Net.build (N : Net) (bad : Finset ℕ) (w : ℕ) : Bool × Frag :=
  let arg := fun a => N.mask bad a (if a < w then (N.build bad a).2 else Frag.lit false)
  match N.code w with
  | .raw => (false, Frag.bit w)
  | .lit b => (false, Frag.lit b)
  | .one f a =>
    (false, Frag.unary f (arg a))
  | .two f a b =>
    let A := arg a
    let B := arg b
    if A.hole.isSome && B.hole.isSome then (true, Frag.entry w) else (false, Frag.binary f A B)
termination_by w

def Net.frag (N : Net) (bad : Finset ℕ) (w : ℕ) : Frag := (N.build bad w).2

def Net.join (N : Net) (bad : Finset ℕ) (w : ℕ) : Prop := (N.build bad w).1 = true

def Net.arg (N : Net) (bad : Finset ℕ) (w : ℕ) : Frag := N.mask bad w (N.frag bad w)

theorem Net.build_raw {N : Net} {bad : Finset ℕ} {w} (h : N.code w = .raw) :
    N.build bad w = (false, Frag.bit w) := by
  rw [Net.build]; simp only [h]

theorem Net.build_lit {N : Net} {bad : Finset ℕ} {w b} (h : N.code w = .lit b) :
    N.build bad w = (false, Frag.lit b) := by
  rw [Net.build]; simp only [h]

theorem Net.build_one {N : Net} {bad : Finset ℕ} {w f a} (h : N.code w = .one f a) :
    N.build bad w = (false, Frag.unary f (N.arg bad a)) := by
  have ha : a < w := N.back (s := false) (by simp [h, Op.pin])
  rw [Net.build]; simp only [h, Net.arg, Net.frag, ite_eq_left ha]

theorem Net.build_two {N : Net} {bad : Finset ℕ} {w f a b} (h : N.code w = .two f a b) :
    N.build bad w = if (N.arg bad a).hole.isSome && (N.arg bad b).hole.isSome then
      (true, Frag.entry w) else (false, Frag.binary f (N.arg bad a) (N.arg bad b)) := by
  have ha : a < w := N.back (s := false) (by simp [h, Op.pin])
  have hb : b < w := N.back (s := true) (by simp [h, Op.pin])
  rw [Net.build]; simp only [h, Net.arg, Net.frag, ite_eq_left ha, ite_eq_left hb]
  split <;> simp_all

theorem Net.arg_eval {N : Net} {bad : Finset ℕ} {w} {x : ℕ → Bool}
    (h : (N.frag bad w).eval x (N.run x) = N.run x w) :
    (N.arg bad w).eval x (N.run x) = N.run x w := by
  classical
  by_cases hc : N.cut bad w
  · simp [Net.arg, Net.mask, hc, Frag.eval, Frag.entry]
  · simpa [Net.arg, Net.mask, hc] using h

theorem Net.frag_eval (N : Net) (bad : Finset ℕ) (x : ℕ → Bool) (w : ℕ) :
    (N.frag bad w).eval x (N.run x) = N.run x w := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    conv_rhs => rw [Net.run_eq]
    cases h : N.code w with
    | raw => simp [Net.frag, N.build_raw h, Frag.eval, Frag.bit, Op.value]
    | lit b => simp [Net.frag, N.build_lit h, Frag.eval, Frag.lit, Op.value]
    | one f a =>
      rw [Op.value, Net.frag, N.build_one h]
      have ha := N.arg_eval (ih a (N.back (s := false) (by simp [h, Op.pin])))
      exact congrArg f ha
    | two f a b =>
      rw [Op.value, Net.frag, N.build_two h]
      split
      · change N.run x w = f (N.run x a) (N.run x b)
        rw [Net.run_eq, h, Op.value]
      · rename_i hp
        rw [Frag.binary_eval _ _ _ _ _ hp, N.arg_eval (ih a (N.back (s := false) (by simp [h, Op.pin]))),
          N.arg_eval (ih b (N.back (s := true) (by simp [h, Op.pin])))]

theorem Net.join_entry {N : Net} {bad : Finset ℕ} {w} (h : N.join bad w) :
    N.frag bad w = Frag.entry w := by
  cases he : N.code w with
  | raw => simp [Net.join, N.build_raw he] at h
  | lit b => simp [Net.join, N.build_lit he] at h
  | one f a => simp [Net.join, N.build_one he] at h
  | two f a b =>
    simp only [Net.join, Net.frag, N.build_two he] at h ⊢
    split at h <;> simp_all

theorem Net.join_two {N : Net} {bad : Finset ℕ} {w f a b} (h : N.code w = .two f a b) :
    N.join bad w ↔ (N.arg bad a).hole.isSome ∧ (N.arg bad b).hole.isSome := by
  unfold Net.join
  rw [N.build_two h]
  split <;> simp_all

theorem Net.hole_back {N : Net} {bad : Finset ℕ} {w a}
    (h : (N.frag bad w).hole = some a) :
    a ≤ w ∧ (N.cut bad a ∨ N.join bad a) ∧
      (w ∈ N.live → a ∈ N.live) ∧ (a = w → N.join bad w) := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hc (v : ℕ) {s : Bool} (hp : (N.code w).pin s = some v) (hh : (N.arg bad v).hole = some a) :
        a ≤ w ∧ (N.cut bad a ∨ N.join bad a) ∧
          (w ∈ N.live → a ∈ N.live) ∧ (a = w → N.join bad w) := by
      have hv := N.back hp
      have he (hw : w ∈ N.live) : v ∈ N.live := N.mem_live.mpr (.child (N.mem_live.mp hw) hp)
      by_cases hv' : N.cut bad v
      · have : v = a := by simpa [Net.arg, Net.mask, hv', Frag.entry] using hh
        subst a
        exact ⟨hv.le, Or.inl hv', he, fun h => (hv.ne h).elim⟩
      · obtain ⟨ha, hb, hreach, _⟩ := ih v hv (by simpa [Net.arg, Net.mask, hv'] using hh)
        have hlt := ha.trans_lt hv
        exact ⟨hlt.le, hb, fun hw => hreach (he hw), fun h => (hlt.ne h).elim⟩
    cases hw : N.code w with
    | raw => simp [Net.frag, N.build_raw hw, Frag.bit] at h
    | lit b => simp [Net.frag, N.build_lit hw, Frag.lit] at h
    | one f v =>
      apply hc v (s := false) (by simp [hw, Op.pin])
      simpa [Net.frag, N.build_one hw, Frag.unary] using h
    | two f v u =>
      by_cases hj : N.join bad w
      · have : w = a := by simpa [N.join_entry hj, Frag.entry] using h
        subst a
        exact ⟨le_rfl, Or.inr hj, id, fun _ => hj⟩
      · have hn : ¬((N.arg bad v).hole.isSome && (N.arg bad u).hole.isSome) = true := by
          simpa [N.join_two hw] using hj
        simp only [Net.frag, N.build_two hw, ite_eq_right hn, Frag.binary] at h
        cases he : (N.arg bad v).hole with
        | none => exact hc u (s := true) (by simp [hw, Op.pin]) (by simpa [he, Option.or] using h)
        | some k => exact hc v (s := false) (by simp [hw, Op.pin]) (by simpa [he, Option.or] using h)

theorem Net.hole_lt {N : Net} {bad : Finset ℕ} {w a} (hj : ¬N.join bad w)
    (h : (N.frag bad w).hole = some a) : a < w := by
  obtain ⟨h₁, _, _, h₂⟩ := N.hole_back h
  exact lt_of_le_of_ne h₁ (fun e => hj (h₂ e))

end

open Finset

noncomputable section

def Net.terminal (N : Net) (bad : Finset ℕ) (a : ℕ) : Prop :=
  N.cut bad a ∨ a = N.out ∨ ∃ e ∈ N.edges, N.src e = a ∧ N.join bad e.1

def Net.root (N : Net) (bad : Finset ℕ) (w : ℕ) : Prop :=
  w ∈ N.live ∧ N.terminal bad w ∧ ¬N.join bad w ∧
    ¬(N.code w = .raw ∧ N.cut bad w) ∧ (N.frag bad w).raw.Nonempty

def Net.roots (N : Net) (bad : Finset ℕ) : Finset ℕ := by
  classical
  exact N.live.filter (N.root bad)

@[simp] theorem Net.mem_roots {N : Net} {bad : Finset ℕ} {w} :
    w ∈ N.roots bad ↔ N.root bad w := by
  classical
  exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨h.1,h⟩⟩

structure Net.Link (N : Net) (bad : Finset ℕ) (a w : ℕ) : Prop where
  edge : ∃ e ∈ N.edges, N.src e = a ∧ e.1 = w
  uncut : ¬N.cut bad a
  unjoined : ¬N.join bad w

inductive Net.Route (N : Net) (bad : Finset ℕ) : ℕ → ℕ → Prop where
  | nil (a : ℕ) : Route N bad a a
  | cons {a p w : ℕ} : N.Link bad a p → Route N bad p w → Route N bad a w

theorem Net.Route.snoc {N : Net} {bad : Finset ℕ} {a w p : ℕ}
    (h : N.Route bad a w) (hp : N.Link bad w p) : N.Route bad a p := by
  induction h with
  | nil w => exact .cons hp (.nil p)
  | cons h _ ih => exact .cons h (ih hp)

theorem Net.link_not_terminal {N : Net} {bad : Finset ℕ} {a w} (h : N.Link bad a w) :
    ¬N.terminal bad a := by
  rcases h.edge with ⟨e,he,hsa,hpa⟩
  rintro (hc | ho | ⟨e',he',hs',hj⟩)
  · exact h.uncut hc
  · exact N.not_out_src he (hsa.trans ho)
  · have hEq := N.use_unique he he' (hsa.trans hs'.symm) (fun hh => h.uncut (Or.inl (hsa ▸ hh)))
    exact h.unjoined (hpa ▸ hEq.symm ▸ hj)

theorem Net.link_unique {N : Net} {bad : Finset ℕ} {a w w'}
    (h : N.Link bad a w) (h' : N.Link bad a w') : w = w' := by
  rcases h.edge with ⟨e,he,hsa,rfl⟩
  rcases h'.edge with ⟨e',he',hsa',rfl⟩
  exact congrArg Prod.fst (N.use_unique he he' (hsa.trans hsa'.symm)
    (fun hh => h.uncut (Or.inl (hsa ▸ hh))))

theorem Net.Route.unique {N : Net} {bad : Finset ℕ} {a w w'}
    (h : N.Route bad a w) (h' : N.Route bad a w')
    (hw : N.terminal bad w) (hw' : N.terminal bad w') : w = w' := by
  induction h generalizing w' with
  | nil a =>
    cases h' with
    | nil => rfl
    | cons h _ => exact (N.link_not_terminal h hw).elim
  | cons h _ ih =>
    cases h' with
    | nil => exact (N.link_not_terminal h hw').elim
    | cons h' hp' =>
      have he := N.link_unique h h'
      subst he
      exact ih hp' hw hw'

theorem Net.find_terminal (N : Net) (bad : Finset ℕ) {a} (ha : a ∈ N.live) :
    ∃ w ∈ N.live, N.terminal bad w ∧ N.Route bad a w := by
  classical
  by_cases h : N.terminal bad a
  · exact ⟨a,ha,h,.nil a⟩
  · have hd := N.deg_pos ha (fun he => h (Or.inr (Or.inl he)))
    obtain ⟨e,he'⟩ := card_pos.mp hd
    obtain ⟨he,hs⟩ := mem_filter.mp he'
    have ha' : e.1 ∈ N.live := N.edge_live he
    obtain ⟨w,hw,ht,hr⟩ := N.find_terminal bad ha'
    exact ⟨w,hw,ht,.cons ⟨⟨e,he,hs,rfl⟩, fun hc => h (Or.inl hc),
      fun hj => h (Or.inr (Or.inr ⟨e,he,hs,hj⟩))⟩ hr⟩
termination_by N.out - a
decreasing_by
  have hlt := N.back (N.pin_src he)
  have hle := N.reach_le (N.mem_live.mp ha')
  omega

theorem Net.mem_arg_raw {N : Net} {bad : Finset ℕ} {a z} :
    a ∈ (N.arg bad z).raw ↔ ¬N.cut bad z ∧ a ∈ (N.frag bad z).raw := by
  classical
  by_cases h : N.cut bad z <;> simp [Net.arg, Net.mask, h, Frag.entry]

theorem Net.pin_into_frag {N : Net} {bad : Finset ℕ} {a w p s} (hj : ¬N.join bad p)
    (hp : (N.code p).pin s = some w) (ha : a ∈ (N.arg bad w).raw) :
    a ∈ (N.frag bad p).raw := by
  cases h : N.code p with
  | raw => simp [h, Op.pin] at hp
  | lit b => simp [h, Op.pin] at hp
  | one f v =>
    cases s <;> simp [h, Op.pin] at hp
    subst w
    simpa [Net.frag, N.build_one h, Frag.unary] using ha
  | two f v u =>
    have hn : ¬((N.arg bad v).hole.isSome && (N.arg bad u).hole.isSome) = true := by
      simpa [N.join_two h] using hj
    cases s <;> simp [h, Op.pin] at hp <;> subst w
    · simp only [Net.frag, N.build_two h, ite_eq_right hn, Frag.binary]
      exact mem_union_left _ ha
    · simp only [Net.frag, N.build_two h, ite_eq_right hn, Frag.binary]
      exact mem_union_right _ ha

theorem Net.Route.preserves_raw {N : Net} {bad : Finset ℕ} {u w a}
    (h : N.Route bad u w) (ha : a ∈ (N.frag bad u).raw) : a ∈ (N.frag bad w).raw := by
  induction h with
  | nil => exact ha
  | cons h _ ih =>
    obtain ⟨e,he,hs,hp⟩ := h.edge
    apply ih
    exact N.pin_into_frag h.unjoined (hp ▸ hs ▸ N.pin_src he) (N.mem_arg_raw.mpr ⟨h.uncut,ha⟩)

theorem Net.raw_route {N : Net} {bad : Finset ℕ} {w a} (hw : w ∈ N.live)
    (ha : a ∈ (N.frag bad w).raw) : a ∈ N.live ∧ N.code a = .raw ∧ N.Route bad a w := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have step {p s} (hp : (N.code w).pin s = some p) (hj : ¬N.join bad w)
        (hm : a ∈ (N.arg bad p).raw) : a ∈ N.live ∧ N.code a = .raw ∧ N.Route bad a w := by
      obtain ⟨hc, hm'⟩ := N.mem_arg_raw.mp hm
      obtain ⟨he,hs⟩ := N.edge_of_pin hw hp
      obtain ⟨h1,h2,h3⟩ := ih p (N.back hp) (hs ▸ N.src_live he) hm'
      exact ⟨h1,h2,h3.snoc ⟨⟨(w,s),he,hs,rfl⟩,hc,hj⟩⟩
    cases hh : N.code w with
    | raw =>
      have he : a = w := by simpa [Net.frag, N.build_raw hh, Frag.bit] using ha
      subst a
      exact ⟨hw,hh,.nil _⟩
    | lit b => simp [Net.frag, N.build_lit hh, Frag.lit] at ha
    | one f p =>
      apply step (p := p) (s := false) (by simp [hh, Op.pin]) (by simp [Net.join, N.build_one hh])
      simpa [Net.frag, N.build_one hh, Frag.unary] using ha
    | two f p q =>
      by_cases h : N.join bad w
      · simp [N.join_entry h, Frag.entry] at ha
      · have hn : ¬((N.arg bad p).hole.isSome && (N.arg bad q).hole.isSome) = true := by
          simpa [N.join_two hh] using h
        simp only [Net.frag, N.build_two hh, ite_eq_right hn, Frag.binary, mem_union] at ha
        exact ha.elim (step (p := p) (s := false) (by simp [hh, Op.pin]) h)
          (step (p := q) (s := true) (by simp [hh, Op.pin]) h)

theorem Net.root_support {N : Net} {bad : Finset ℕ} {a w}
    (hw : N.root bad w) (ha : a ∈ (N.frag bad w).raw) :
    a ∈ N.live ∧ N.code a = .raw ∧ ¬N.cut bad a := by
  obtain ⟨h1,h2,h3⟩ := N.raw_route hw.1 ha
  refine ⟨h1,h2,?_⟩
  cases h3 with
  | nil => exact fun hh => hw.2.2.2.1 ⟨h2,hh⟩
  | cons hh _ => exact hh.uncut

theorem Net.owner_exists {N : Net} {bad : Finset ℕ} {a} (ha : a ∈ N.live)
    (hr : N.code a = .raw) (hc : ¬N.cut bad a) :
    ∃! w, N.root bad w ∧ a ∈ (N.frag bad w).raw := by
  obtain ⟨w,hw,ht,hp⟩ := N.find_terminal bad ha
  have hbit : a ∈ (N.frag bad a).raw := by simp [Net.frag, N.build_raw hr, Frag.bit]
  have hm := hp.preserves_raw hbit
  have hj : ¬N.join bad w := fun h => by simp [N.join_entry h, Frag.entry] at hm
  have hn : ¬(N.code w = .raw ∧ N.cut bad w) := by
    rintro ⟨hrw,hcw⟩
    have he : a = w := by simpa [Net.frag, N.build_raw hrw, Frag.bit] using hm
    exact hc (he ▸ hcw)
  refine ⟨w, ⟨⟨hw,ht,hj,hn,⟨a,hm⟩⟩,hm⟩, ?_⟩
  intro w' hh
  exact (N.raw_route hh.1.1 hh.2).2.2.unique hp hh.1.2.1 ht

theorem Net.transfer {N : Net} {bad : Finset ℕ} (x y : ℕ → Bool)
    (hr : ∀ a ∈ N.live, N.code a = .raw → N.cut bad a → x a = y a)
    (hk : ∀ w, N.root bad w → ∀ b, (N.frag bad w).f x b = (N.frag bad w).f y b) :
    N.run x N.out = N.run y N.out := by
  have all (w : ℕ) (hw : w ∈ N.live) (ht : N.terminal bad w ∨ N.join bad w) :
      N.run x w = N.run y w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hj : N.join bad w
      · have descend {s a} (hp : (N.code w).pin s = some a) : N.run x a = N.run y a := by
          obtain ⟨he,hs⟩ := N.edge_of_pin hw hp
          exact ih a (N.back hp) (hs ▸ N.src_live he) (Or.inl (Or.inr (Or.inr ⟨(w,s),he,hs,hj⟩)))
        rw [Net.run_eq N x w, Net.run_eq N y w]
        cases he : N.code w with
        | raw => simp [Net.join, N.build_raw he] at hj
        | lit b => rfl
        | one f a => simp [Net.join, N.build_one he] at hj
        | two f a b =>
          simp only [Op.value]
          rw [descend (s := false) (by simp [he, Op.pin]), descend (s := true) (by simp [he, Op.pin])]
      · have ht' := ht.resolve_right hj
        by_cases hc : N.code w = .raw ∧ N.cut bad w
        · rw [Net.run_eq N x w, Net.run_eq N y w, hc.1, Op.value, Op.value]
          exact hr w hw hc.1 hc.2
        · rw [← N.frag_eval bad x w, ← N.frag_eval bad y w]
          have hf (b : Bool) : (N.frag bad w).f x b = (N.frag bad w).f y b := by
            by_cases hh : (N.frag bad w).raw.Nonempty
            · exact hk w ⟨hw,ht',hj,hc,hh⟩ b
            · exact (N.frag bad w).congrRaw x y (fun a ha => (hh ⟨a,ha⟩).elim) b
          unfold Frag.eval
          rw [hf]
          congr 1
          cases he : (N.frag bad w).hole with
          | none => rfl
          | some a =>
            have hb := (N.hole_back he).2.1
            have ha := N.hole_lt hj he
            have hl := (N.hole_back he).2.2.1 hw
            exact ih a ha hl (hb.imp Or.inl id)
  exact all N.out (N.mem_live.mpr .top) (Or.inl (Or.inr (Or.inl rfl)))

theorem Net.diff_routes {N : Net} {bad : Finset ℕ} (x y : ℕ → Bool) (w : ℕ)
    (hr : ∀ a ∈ N.live, N.code a = .raw → x a ≠ y a → N.Route bad a w) :
    ∀ t ∈ N.live, (t < w ∨ N.run x w = N.run y w) → N.run x t ≠ N.run y t →
      ¬N.join bad t ∧ N.Route bad t w := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht hb hd
    have pass {a s} (hp : (N.code t).pin s = some a) (h : N.run x a ≠ N.run y a) :
        ¬N.join bad t ∧ N.Route bad t w := by
      obtain ⟨he,hs⟩ := N.edge_of_pin ht hp
      have ha := N.back hp
      have hbw : a < w ∨ N.run x w = N.run y w := hb.imp (ha.trans ·) id
      have hh := (ih a ha (hs ▸ N.src_live he) hbw h).2
      cases hh with
      | nil => exact (hb.elim (fun hlt => (Nat.lt_asymm hlt ha).elim) (fun heq => (h heq).elim))
      | cons hl hr =>
        obtain ⟨e',he',hs',ht'⟩ := hl.edge
        have hslot := N.use_unique he' he (hs'.trans hs.symm)
          (fun h => hl.uncut (Or.inl (hs' ▸ h)))
        have heq : _ = t := ht'.symm.trans (congrArg Prod.fst hslot)
        exact heq ▸ ⟨hl.unjoined,hr⟩
    rw [Net.run_eq N x t, Net.run_eq N y t] at hd
    cases hh : N.code t with
    | raw => exact ⟨by simp [Net.join, N.build_raw hh], hr t ht hh (by simpa [hh, Op.value] using hd)⟩
    | lit b => simp [hh, Op.value] at hd
    | one f a =>
      simp only [hh, Op.value] at hd
      apply pass (a := a) (s := false) (by simp [hh, Op.pin])
      intro h; exact hd (congrArg f h)
    | two f a b =>
      simp only [hh, Op.value] at hd
      by_cases ha : N.run x a = N.run y a
      · apply pass (a := b) (s := true) (by simp [hh, Op.pin])
        intro hb; exact hd (congrArg₂ f ha hb)
      · exact pass (a := a) (s := false) (by simp [hh, Op.pin]) ha

theorem Net.transfer_local {N : Net} {bad : Finset ℕ} (x y : ℕ → Bool) (w : ℕ)
    (hw : w ∈ N.live) (hj : ¬N.join bad w)
    (hr : ∀ a ∈ N.live, N.code a = .raw → x a ≠ y a → N.Route bad a w)
    (hf : ∀ b, (N.frag bad w).f x b = (N.frag bad w).f y b) :
    N.run x N.out = N.run y N.out := by
  have he : N.run x w = N.run y w := by
    rw [← N.frag_eval bad x w, ← N.frag_eval bad y w]
    unfold Frag.eval
    rw [hf]
    congr 1
    cases hh : (N.frag bad w).hole with
    | none => rfl
    | some a =>
      by_contra h
      obtain ⟨_,he,hl,_⟩ := N.hole_back hh
      have hd := N.diff_routes x y w hr a (hl hw) (Or.inl (N.hole_lt hj hh)) h
      rcases he with hc | hc
      · cases hd.2 with
        | nil => exact (hj ((N.hole_back hh).2.2.2 rfl)).elim
        | cons he _ => exact he.uncut hc
      · exact hd.1 hc
  by_contra hh
  have hd := (N.diff_routes x y w hr N.out (N.mem_live.mpr .top) (Or.inr he) hh).2
  cases hd with
  | nil => exact hh he
  | cons hd _ =>
    exact N.link_not_terminal hd (Or.inr (Or.inl rfl))

end

open Finset

noncomputable section

theorem Net.arg_cut {N : Net} {bad : Finset ℕ} {a} (h : N.cut bad a) :
    N.arg bad a = Frag.entry a := by
  classical
  simp [Net.arg, Net.mask, h]

theorem Net.arg_uncut {N : Net} {bad : Finset ℕ} {a} (h : ¬N.cut bad a) :
    N.arg bad a = N.frag bad a := by
  classical
  simp [Net.arg, Net.mask, h]

theorem Net.pin_join {N : Net} {bad : Finset ℕ} {w s a}
    (hj : N.join bad w) (hp : (N.code w).pin s = some a) :
    (N.arg bad a).hole.isSome := by
  cases h : N.code w with
  | raw => simp [h, Op.pin] at hp
  | lit b => simp [h, Op.pin] at hp
  | one f b => simp [Net.join, N.build_one h] at hj
  | two f b c =>
    have hh := (N.join_two h).mp hj
    cases s <;> simp [h, Op.pin] at hp <;> subst a
    · exact hh.1
    · exact hh.2

theorem Net.join_arity {N : Net} {bad : Finset ℕ} {w} (h : N.join bad w) :
    (N.code w).arity = 2 := by
  cases he : N.code w with
  | raw => simp [Net.join, N.build_raw he] at h
  | lit b => simp [Net.join, N.build_lit he] at h
  | one f a => simp [Net.join, N.build_one he] at h
  | two f a b => rfl

theorem Net.has_input_hole {N : Net} {bad : Finset ℕ} {w} (hj : ¬N.join bad w)
    (hh : (N.frag bad w).hole.isSome) :
    ∃ s a, (N.code w).pin s = some a ∧ (N.arg bad a).hole.isSome := by
  cases h : N.code w with
  | raw => simp [Net.frag, N.build_raw h, Frag.bit] at hh
  | lit b => simp [Net.frag, N.build_lit h, Frag.lit] at hh
  | one f a =>
    exact ⟨false,a,by simp [Op.pin], by simpa [Net.frag, N.build_one h, Frag.unary] using hh⟩
  | two f a b =>
    have hn : ¬((N.arg bad a).hole.isSome && (N.arg bad b).hole.isSome) = true := by
      simpa [N.join_two h] using hj
    by_cases ha : (N.arg bad a).hole.isSome
    · exact ⟨false,a,by simp [Op.pin],ha⟩
    · have he : (N.arg bad a).hole = none := by
        cases he : (N.arg bad a).hole <;> simp_all
      exact ⟨true,b,by simp [Op.pin],by
        simpa [Net.frag, N.build_two h, ite_eq_right hn, Frag.binary, he, Option.or] using hh⟩

def Net.pure (N : Net) (bad : Finset ℕ) : Finset ℕ :=
  (N.roots bad).filter fun w => (N.frag bad w).hole = none

def Net.unary (N : Net) (bad : Finset ℕ) : Finset ℕ :=
  (N.roots bad).filter fun w => (N.frag bad w).hole.isSome

theorem Net.pure_bound (N : Net) (bad : Finset ℕ) (hb : ∀ a ∈ bad, N.code a = .raw) :
    (N.pure bad).card ≤ 2 * N.excess + 1 := by
  classical
  have hsub : N.pure bad ⊆ insert N.out (N.live.filter N.shared) := by
    intro w hw
    obtain ⟨hr,hh⟩ := mem_filter.mp hw
    have hr' := N.mem_roots.mp hr
    rcases hr'.2.1 with hc | h | ⟨e,he,hs,hj⟩
    · rcases hc with hv | hv
      · exact mem_insert_of_mem (mem_filter.mpr ⟨hr'.1,hv⟩)
      · exact (hr'.2.2.2.1 ⟨hb _ hv,Or.inr hv⟩).elim
    · exact mem_insert.mpr (Or.inl h)
    · by_cases hc : N.cut bad w
      · rcases hc with hc | hc
        · exact mem_insert_of_mem (mem_filter.mpr ⟨hr'.1,hc⟩)
        · exact (hr'.2.2.2.1 ⟨hb _ hc,Or.inr hc⟩).elim
      · have hp := N.pin_join hj (N.pin_src he)
        rw [hs, N.arg_uncut hc, hh] at hp
        contradiction
  have h₁ := card_le_card hsub
  have h₂ := card_insert_le N.out (N.live.filter N.shared)
  have h₃ := N.shared_le
  omega

theorem Net.unary_bound (N : Net) (bad : Finset ℕ) :
    (N.unary bad).card ≤ 4 * N.excess + 2 * bad.card := by
  classical
  let J := N.live.filter (N.join bad)
  let U := N.live.filter fun w => ¬N.join bad w ∧ (N.frag bad w).hole.isSome
  let End := U.filter fun w => N.cut bad w ∨ w = N.out
  let E := N.edges.filter fun e => (N.arg bad (N.src e)).hole.isSome
  let Jedge := N.edges.filter fun e => e.1 ∈ J
  have hJedge : Jedge.card = 2 * J.card := by
    rw [card_eq_sum_card_fiberwise (s := Jedge) (f := Prod.fst) (t := J)
      (fun _ he => (mem_filter.mp he).2)]
    have hs : (∑ w ∈ J, (Jedge.filter fun e => e.1 = w).card) = ∑ _ ∈ J, 2 := by
      apply sum_congr rfl
      intro w hw
      have hm : (Jedge.filter fun e => e.1 = w) = N.edges.filter fun e => e.1 = w := by
        ext e
        simp only [Jedge, mem_filter]
        grind
      rw [hm, N.card_pin_fiber (mem_filter.mp hw).1, N.join_arity (mem_filter.mp hw).2]
    simpa [Nat.mul_comm] using hs
  have hJsub : Jedge ⊆ E := by
    intro e he
    obtain ⟨he,hw⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨he,N.pin_join (mem_filter.mp hw).2 (N.pin_src he)⟩
  have hLower : 2 * J.card + U.card ≤ E.card := by
    let Eother := E.filter fun e => e.1 ∈ U
    have hUimg : U ⊆ Eother.image Prod.fst := by
      intro w hw
      obtain ⟨hw',hj,hh⟩ := mem_filter.mp hw
      obtain ⟨s,a,hp,ha⟩ := N.has_input_hole hj hh
      obtain ⟨he,hs⟩ := N.edge_of_pin hw' hp
      exact mem_image.mpr ⟨(w,s),mem_filter.mpr ⟨mem_filter.mpr ⟨he,hs ▸ ha⟩,hw⟩,rfl⟩
    have hUle := (card_le_card hUimg).trans card_image_le
    have hdis : Disjoint Jedge Eother := by
      apply disjoint_left.mpr
      intro e he he'
      exact (mem_filter.mp (mem_filter.mp he').2).2.1 (mem_filter.mp (mem_filter.mp he).2).2
    have hs : Jedge ∪ Eother ⊆ E := union_subset hJsub (filter_subset _ _)
    have h := card_le_card hs
    rw [card_union_of_disjoint hdis, hJedge] at h
    omega
  have hUpper : E.card + End.card ≤ (N.holeEdges bad).card + J.card + U.card := by
    let Q := E.filter fun e => ¬N.cut bad (N.src e)
    have hpart : (E.filter fun e => N.cut bad (N.src e)).card + Q.card = E.card :=
      card_filter_add_card_filter_not ..
    have hb : (E.filter fun e => N.cut bad (N.src e)).card ≤ (N.holeEdges bad).card :=
      card_le_card fun _ h => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp h).1).1,(mem_filter.mp h).2⟩
    have hinj : Set.InjOn N.src Q := by
      intro e he f hf h
      have h₁ := mem_filter.mp he
      have h₂ := mem_filter.mp hf
      exact N.use_unique (mem_filter.mp h₁.1).1 (mem_filter.mp h₂.1).1 h (fun hh => h₁.2 (Or.inl hh))
    have hdis : Disjoint (Q.image N.src) End := by
      apply disjoint_left.mpr
      intro w hw ha
      obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨he,hn⟩ := mem_filter.mp he
      exact (mem_filter.mp ha).2.elim hn (N.not_out_src (mem_filter.mp he).1)
    have hsub : Q.image N.src ∪ End ⊆ J ∪ U := by
      intro w hw
      rcases mem_union.mp hw with hh | hh
      · obtain ⟨e,he,rfl⟩ := mem_image.mp hh
        obtain ⟨he,hc⟩ := mem_filter.mp he
        obtain ⟨he, hh⟩ := mem_filter.mp he
        rw [N.arg_uncut hc] at hh
        by_cases hj : N.join bad (N.src e)
        · exact mem_union_left _ (mem_filter.mpr ⟨N.src_live he,hj⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨N.src_live he,hj,hh⟩)
      · exact mem_union_right _ (mem_filter.mp hh).1
    have h := (card_le_card hsub).trans (card_union_le J U)
    rw [card_union_of_disjoint hdis, card_image_of_injOn hinj] at h
    omega
  have hRoots : (N.unary bad).card ≤ End.card + 2 * J.card := by
    have hsub : N.unary bad ⊆ End ∪ Jedge.image N.src := by
      intro w hw
      obtain ⟨hr,hh⟩ := mem_filter.mp hw
      have hr' := N.mem_roots.mp hr
      have hU : w ∈ U := mem_filter.mpr ⟨hr'.1,hr'.2.2.1,hh⟩
      rcases hr'.2.1 with hc | ho | ⟨e,he,hs,hj⟩
      · exact mem_union_left _ (mem_filter.mpr ⟨hU,Or.inl hc⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hU,Or.inr ho⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨e,mem_filter.mpr ⟨he,
          mem_filter.mpr ⟨N.edge_live he,hj⟩⟩,hs⟩)
    have h := (card_le_card hsub).trans (card_union_le End (Jedge.image N.src))
    have hc := card_image_le (s := Jedge) (f := N.src)
    omega
  have hB := N.cut_edges_le bad
  omega

end

open Finset PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) : W (gs ++ [g]) x = stp (W gs x) g := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [stp, ih]; omega

theorem getD_app_l (l l' : List Bool) (i : ℕ) (h : i < l.length) : (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_m (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem W_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]; exact ih

theorem W_stable (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (W (gs ++ [g]) x).getD i false = (W gs x).getD i false := by
  rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]

theorem W_take (gs : List Gate) (x : List Bool) (k i : ℕ) (hi : i < x.length + k) :
    (W gs x).getD i false = (W (gs.take k) x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    by_cases hk : k ≤ gs.length
    · rw [List.take_append_of_le_length hk, W_stable _ _ _ _ (by omega)]; exact ih
    · rw [List.take_of_length_le (by simp; omega)]

theorem W_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (W (gs.take j) x).getD i false) := by
  have h1 : gs.take (j + 1) = gs.take j ++ [gs[j]] := by
    rw [List.take_add_one]; simp [List.getElem?_eq_getElem hj]
  rw [W_take gs x (j + 1) _ (by omega), h1, W_snoc, stp]
  have hl : (W (gs.take j) x).length = x.length + j := by
    rw [W_len, List.length_take]; omega
  rw [← hl, getD_app_m]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = (decide (i = u.val) || decide (i = n + v.val)) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    have : i ≠ n + v.val := by omega
    simp [h, this, Fin.ext_iff]
  · rw [List.getElem?_append_right (by simpa using h)]
    have hu : i ≠ u.val := by have := u.isLt; omega
    by_cases h2 : i - n < m
    · simp [h2, hu, Fin.ext_iff]; omega
    · have : i ≠ n + v.val := by have := v.isLt; omega
      simp [h2, hu, this]

def prevWire (w i : ℕ) : ℕ := if i + 1 < w then i + 1 else 0

def ofGate (w : ℕ) (g : Gate) : Op :=
  match g.inputs with
  | [] => .lit (g.op.eval [])
  | [a] => .one (fun p => g.op.eval [p]) (prevWire w a)
  | [a,b] => .two (fun p q => g.op.eval [p,q]) (prevWire w a) (prevWire w b)
  | _ => .lit false

theorem ofGate_arity (w : ℕ) (g : Gate) (h : g.inputs.length ≤ 2) :
    (ofGate w g).arity = g.inputs.length := by
  rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
  all_goals simp [ofGate, hi, Op.arity] at h ⊢

def codeAt (k : ℕ) (C : Circuit) (w : ℕ) : Op :=
  if w = 0 then .lit false else if w ≤ k then .raw else
    (C.gates[w - (k + 1)]?).elim (.lit false) (ofGate w)

theorem prevWire_lt {w i : ℕ} (hw : 0 < w) : prevWire w i < w := by
  unfold prevWire; split <;> omega

theorem ofGate_back {w a s} (g : Gate) (hw : 0 < w)
    (h : (ofGate w g).pin s = some a) : a < w := by
  rcases hi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨c,l⟩⟩⟩
  all_goals cases s <;> simp [ofGate, hi, Op.pin] at h
  all_goals subst a; exact prevWire_lt hw

def ofCircuit (k : ℕ) (C : Circuit) : Net where
  code := codeAt k C
  out := if C.output < k + C.gates.length then C.output + 1 else 0
  back := by
    intro w s a h
    by_cases h0 : w = 0
    · simp [codeAt, h0, Op.pin] at h
    by_cases hk : w ≤ k
    · simp [codeAt, h0, hk, Op.pin] at h
    cases he : C.gates[w-(k+1)]? with
    | none => simp [codeAt, h0, hk, he, Op.pin] at h
    | some g => exact ofGate_back g (Nat.pos_of_ne_zero h0) (by simpa [codeAt, h0, hk, he] using h)

theorem codeAt_raw {k : ℕ} {C : Circuit} {w : ℕ} :
    (ofCircuit k C).code w = .raw ↔ 0 < w ∧ w ≤ k := by
  by_cases h0 : w = 0
  · simp [ofCircuit, codeAt, h0]
  by_cases hk : w ≤ k
  · simp [ofCircuit, codeAt, h0, hk, Nat.pos_of_ne_zero h0]
  cases he : C.gates[w-(k+1)]? with
  | none => simp [ofCircuit, codeAt, h0, hk, he]
  | some g =>
    rcases hi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨c,l⟩⟩⟩ <;>
      simp [ofCircuit, codeAt, h0, hk, he, ofGate, hi]

theorem codeAt_g {k w : ℕ} {C : Circuit} (hk : k < w) (hj : w - (k+1) < C.gates.length) :
    (ofCircuit k C).code w = ofGate w (C.gates[w-(k+1)]) := by
  simp [ofCircuit, codeAt, show w ≠ 0 by omega, show ¬w ≤ k by omega, hj]

theorem ofCircuit_value (C : Circuit) (x : List Bool) (X : ℕ → Bool)
    (hx : ∀ i < x.length, X (i+1) = x.getD i false)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (w : ℕ) (hw : w ≤ x.length + C.gates.length) :
    (ofCircuit x.length C).run X w = if w = 0 then false else (W C.gates x).getD (w-1) false := by
  let N := ofCircuit x.length C
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h0 : w = 0
    · simp [Net.run_eq, ofCircuit, codeAt, h0, Op.value]
    by_cases hr : w ≤ x.length
    · have hw' : w - 1 < x.length := by omega
      simp only [Net.run_eq, (codeAt_raw.mpr ⟨Nat.pos_of_ne_zero h0,hr⟩), Op.value, ite_eq_right h0]
      rw [W_lt _ _ _ hw']
      simpa [show w - 1 + 1 = w by omega] using hx (w-1) hw'
    have hj : w - (x.length+1) < C.gates.length := by omega
    let j := w - (x.length+1)
    have hi : j < C.gates.length := hj
    let g := C.gates[j]
    have hg' := hg g (List.getElem_mem hi)
    have hwj : w - 1 = x.length + j := by dsimp [j]; omega
    have hread (a : ℕ) : N.run X (prevWire w a) = (W (C.gates.take j) x).getD a false := by
      by_cases ha : a + 1 < w
      · rw [prevWire, ite_eq_left ha, ih _ ha (by omega), ite_eq_right (by omega), show a + 1 - 1 = a by omega]
        exact W_take _ _ _ _ (by omega)
      · rw [prevWire, ite_eq_right ha, ih 0 (by omega) (by omega), ite_eq_left rfl]
        exact (getD_big _ _ (by rw [W_len, List.length_take]; omega)).symm
    rw [ite_eq_right h0, hwj, W_val _ _ _ hi, Net.run_eq, codeAt_g (Nat.lt_of_not_ge hr) hj]
    change (ofGate w g).value (X w) (N.run X) = g.op.eval (g.inputs.map fun a => (W (C.gates.take j) x).getD a false)
    rcases hh : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
    all_goals simp [ofGate, hh, Op.value, hread] at hg' ⊢

theorem ofCircuit_eval (C : Circuit) (x : List Bool) (X : ℕ → Bool)
    (hx : ∀ i < x.length, X (i+1) = x.getD i false)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (ofCircuit x.length C).run X (ofCircuit x.length C).out = C.eval x := by
  change (ofCircuit x.length C).run X _ = (W C.gates x).getD C.output false
  by_cases ho : C.output < x.length + C.gates.length
  · have hout : (ofCircuit x.length C).out = C.output + 1 := by simp [ofCircuit, ho]
    rw [hout, ofCircuit_value C x X hx hg _ (by omega)]
    simp
  · have hout : (ofCircuit x.length C).out = 0 := by simp [ofCircuit, ho]
    rw [hout, ofCircuit_value C x X hx hg _ (by omega), ite_eq_left rfl]
    exact (getD_big _ _ (by rw [W_len]; omega)).symm

theorem ofCircuit_bin (k : ℕ) (C : Circuit) (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ((ofCircuit k C).live.filter fun a => ((ofCircuit k C).code a).arity = 2).card ≤
      C.gates.countP (fun g => g.inputs.length == 2) := by
  classical
  let N := ofCircuit k C
  let B := N.live.filter fun a => (N.code a).arity = 2
  let D := (univ : Finset (Fin C.gates.length)).filter fun j => C.gates[j].inputs.length = 2
  have hb (w) (hw : w ∈ B) : k < w ∧ w - (k+1) < C.gates.length := by
    obtain ⟨hl,ho⟩ := mem_filter.mp hw
    have hp := N.reach_le (N.mem_live.mp hl)
    have hk : k < w := by
      by_contra! hc
      by_cases h0 : w = 0 <;> simp [N, ofCircuit, codeAt, h0, hc, Op.arity] at ho
    constructor
    · exact hk
    · unfold N ofCircuit at hp
      by_cases ht : C.output < k + C.gates.length <;> simp [ht] at hp <;> omega
  have hB : B.card ≤ D.card := by
    by_cases hnil : C.gates.length = 0
    · have hempty : B = ∅ := eq_empty_iff_forall_notMem.mpr fun w hw => by have := (hb w hw).2; omega
      simp [hempty]
    let f : ℕ → Fin C.gates.length := fun w => if h : w ∈ B then ⟨w-(k+1),(hb w h).2⟩ else ⟨0, Nat.pos_of_ne_zero hnil⟩
    apply card_le_card_of_injOn f
    · intro w hw
      change f w ∈ D
      have hf : f w = ⟨w-(k+1),(hb w hw).2⟩ := dite_eq_left hw
      rw [hf]
      apply mem_filter.mpr ⟨mem_univ _,?_⟩
      have ho := (mem_filter.mp hw).2
      have hn := hg _ (List.getElem_mem (hb w hw).2)
      rwa [codeAt_g (hb w hw).1 (hb w hw).2, ofGate_arity _ _ hn] at ho
    · intro w hw v hv he
      have hw' : w ∈ B := hw
      have hv' : v ∈ B := hv
      have hf (u) (hu : u ∈ B) : (f u).val = u - (k+1) := by simp only [f, dite_eq_left hu]
      have h := (hf w hw').symm.trans ((congrArg Fin.val he).trans (hf v hv'))
      have h1 := (hb w hw).1
      have h2 := (hb v hv).1
      omega
  apply hB.trans_eq
  change (univ.filter fun j : Fin C.gates.length => C.gates[j].inputs.length = 2).card = _
  rw [card_eq_sum_ones, sum_filter]
  have hlist (l : List Gate) : (∑ j : Fin l.length, if l[j].inputs.length = 2 then 1 else 0) =
      l.countP (fun g => g.inputs.length == 2) := by
    induction l with
    | nil => simp
    | cons g gs ih =>
      let f (j : Fin (gs.length + 1)) : ℕ := if (g :: gs)[j].inputs.length = 2 then 1 else 0
      change (∑ j, f j) = _
      rw [Fin.sum_univ_succ f, List.countP_cons]
      change (if g.inputs.length = 2 then 1 else 0) +
        (∑ j : Fin gs.length, if gs[j].inputs.length = 2 then 1 else 0) = _
      rw [ih]
      by_cases he : g.inputs.length = 2 <;> simp [he, Nat.add_comm]
  exact hlist C.gates

open Finset

def address {n : ℕ} (s : Bool) (i : Fin n) : ℕ := if s then n + i.val + 1 else i.val + 1

theorem address_inj {n : ℕ} (s : Bool) : Function.Injective (address (n := n) s) := by
  intro i j h
  apply Fin.ext
  cases s <;> (simp [address] at h; omega)

theorem address_pos {n : ℕ} (s : Bool) (i : Fin n) : 0 < address s i := by
  cases s <;> simp [address]

theorem address_le {n : ℕ} (s : Bool) (i : Fin n) : address s i ≤ n+n := by
  have := i.isLt
  cases s
  all_goals simp [address]
  omega

theorem address_surj {n w : ℕ} (hw : 0 < w ∧ w ≤ n+n) :
    ∃ (s : Bool) (i : Fin n), address s i = w := by
  by_cases h : w ≤ n
  · exact ⟨false, ⟨w-1, by omega⟩, by simp [address]; omega⟩
  · exact ⟨true, ⟨w-n-1, by omega⟩, by simp [address]; omega⟩

def twice (a b z : ℕ) : Bool := decide (z = a ∨ z = b)

def once (a z : ℕ) : Bool := decide (z = a)

def view {n : ℕ} (N : Net) (s : Bool) (i j : Fin n) : Bool :=
  N.run (twice (address s i) (address (!s) j)) N.out

def bank {n : ℕ} (s : Bool) (F : Frag) : Finset (Fin n) :=
  univ.filter fun i => address s i ∈ F.raw

theorem bank_le {n : ℕ} (s : Bool) (F : Frag) : (bank (n := n) s F).card ≤ F.raw.card := by
  apply card_le_card_of_injOn (address s)
  · exact fun i hi => (mem_filter.mp hi).2
  · exact (address_inj s).injOn

theorem raw_le_banks {n : ℕ} (F : Frag) (h : ∀ w ∈ F.raw, 0 < w ∧ w ≤ n+n) :
    F.raw.card ≤ (bank (n := n) false F).card + (bank (n := n) true F).card := by
  let A := (bank (n := n) false F).image (address false)
  let B := (bank (n := n) true F).image (address true)
  have hsub : F.raw ⊆ A ∪ B := by
    intro w hw
    obtain ⟨s,i,rfl⟩ := address_surj (h w hw)
    cases s
    · exact mem_union_left _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hw⟩,rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hw⟩,rfl⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans_eq (by
    simp [A, B, card_image_of_injective, address_inj]))

def key (F : Frag) (x : ℕ → Bool) : Bool × Bool := (F.f x false, F.f x true)

theorem key_apply {F : Frag} {x y : ℕ → Bool} (h : key F x = key F y) (b : Bool) :
    F.f x b = F.f y b := by
  cases b
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

def baseline (F : Frag) : Bool × Bool := key F (fun _ => false)

theorem key_diag {F : Frag} (h : F.hole = none) (x : ℕ → Bool) : (key F x).1 = (key F x).2 :=
  F.ignore h x false true

def keySpace (F : Frag) : Finset (Bool × Bool) :=
  if F.hole = none then {(false,false),(true,true)} else univ

theorem key_mem (F : Frag) (x : ℕ → Bool) : key F x ∈ keySpace F := by
  by_cases h : F.hole = none
  · have he := key_diag h x
    cases hp : key F x with
    | mk a b =>
      rw [hp] at he
      cases a <;> cases b <;> simp_all [keySpace]
  · simp [keySpace, h]

theorem keySpace_card (F : Frag) : (keySpace F).card = if F.hole = none then 2 else 4 := by
  by_cases h : F.hole = none <;> simp [keySpace, h, Fintype.card_prod]

theorem twice_eq_once {F : Frag} {a b : ℕ} (hb : b ∉ F.raw) (β : Bool) :
    F.f (twice a b) β = F.f (once a) β := by
  apply F.congrRaw
  intro z hz
  have hn : z ≠ b := fun h => hb (h ▸ hz)
  simp [twice, once, hn]

theorem once_eq_base {F : Frag} {a : ℕ} (ha : a ∉ F.raw) (β : Bool) :
    F.f (once a) β = F.f (fun _ => false) β := by
  apply F.congrRaw
  intro z hz
  simp [once, show z ≠ a from fun he => ha (he ▸ hz)]

theorem twice_comm (a b : ℕ) : twice a b = twice b a := by
  funext z
  simp [twice, or_comm]

theorem twice_same {a b c z : ℕ} (ha : z ≠ a) (hb : z ≠ b) :
    twice a c z = twice b c z := by simp [twice, ha, hb]

def Far {n : ℕ} (N : Net) (bad : Finset ℕ) : Prop :=
  ∀ s (i j : Fin n), i ≠ j → address s i ∉ bad → address s j ∉ bad →
    17 ≤ dist (view N s i) (view N s j)

def RawBank (n : ℕ) (N : Net) : Prop := ∀ a, N.code a = .raw ↔ 0 < a ∧ a ≤ n+n

def Net.Private (N : Net) (bad : Finset ℕ) (a : ℕ) : Prop :=
  a ∈ N.live ∧ N.code a = .raw ∧ ¬N.cut bad a

theorem Net.private_raw {N : Net} {bad : Finset ℕ} {w a} (hw : w ∈ N.live)
    (hs : ¬(N.code w = .raw ∧ N.cut bad w)) (ha : a ∈ (N.frag bad w).raw) : N.Private bad a := by
  obtain ⟨hl,hr,hp⟩ := N.raw_route hw ha
  refine ⟨hl,hr,?_⟩
  cases hp with
  | nil => exact fun hh => hs ⟨hr,hh⟩
  | cons h _ => exact h.uncut

theorem local_profile {n : ℕ} {N : Net} {bad : Finset ℕ} {s : Bool} {i j : Fin n} {w : ℕ}
    (hw : w ∈ N.live) (hs : ¬N.join bad w)
    (hi : address s i ∈ (N.frag bad w).raw) (hj : address s j ∈ (N.frag bad w).raw)
    (hk : key (N.frag bad w) (once (address s i)) = key (N.frag bad w) (once (address s j))) :
    dist (view N s i) (view N s j) ≤ (bank (n := n) (!s) (N.frag bad w)).card := by
  apply dist_le_of_agree
  intro z hz
  have hh : address (!s) z ∉ (N.frag bad w).raw := fun h => hz (mem_filter.mpr ⟨mem_univ _,h⟩)
  apply N.transfer_local _ _ w hw hs
  · intro a ha hr hd
    by_cases he : a = address s i
    · exact he.symm ▸ (N.raw_route hw hi).2.2
    by_cases he' : a = address s j
    · exact he'.symm ▸ (N.raw_route hw hj).2.2
    exact (hd (twice_same he he')).elim
  · intro bit
    rw [twice_eq_once hh, twice_eq_once hh, key_apply hk]

theorem bank_keys_inj {n : ℕ} {N : Net} {bad : Finset ℕ} {w : ℕ} (hF : Far (n := n) N bad)
    (hw : w ∈ N.live) (hs : ¬(N.code w = .raw ∧ N.cut bad w))
    (hJ : ¬N.join bad w) (hB : (N.frag bad w).raw.card ≤ 16) (s : Bool) :
    Set.InjOn (fun i : Fin n => key (N.frag bad w) (once (address s i))) (bank (n := n) s (N.frag bad w)) := by
  intro i hi j hj hkey
  by_contra hne
  have hi' := (mem_filter.mp hi).2
  have hj' := (mem_filter.mp hj).2
  have hd := hF s i j hne (fun h => (N.private_raw hw hs hi').2.2 (Or.inr h))
    (fun h => (N.private_raw hw hs hj').2.2 (Or.inr h))
  have hd' := (local_profile hw hJ hi' hj' hkey).trans (bank_le (!s) _)
  omega

theorem frag_small {n : ℕ} {N : Net} {bad : Finset ℕ} (hR : RawBank n N) (hF : Far (n := n) N bad)
    (w : ℕ) (hw : w ∈ N.live) :
    (N.frag bad w).raw.card ≤ if (N.frag bad w).hole = none then 4 else 8 := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have descend {a s} (h : (N.code w).pin s = some a) : (N.arg bad a).raw.card ≤ 8 := by
      have ha := N.mem_live.mpr (.child (N.mem_live.mp hw) h)
      have hI := ih a (N.back h) ha
      by_cases hc : N.cut bad a
      · simp [N.arg_cut hc, Frag.entry]
      · rw [N.arg_uncut hc]
        exact hI.trans (by split <;> omega)
    have finish (h₁ : ¬(N.code w = .raw ∧ N.cut bad w)) (hJ : ¬N.join bad w)
        (hm : (N.frag bad w).raw.card ≤ 16) :
        (N.frag bad w).raw.card ≤ if (N.frag bad w).hole = none then 4 else 8 := by
      let F := N.frag bad w
      have cardSide (s : Bool) : (bank (n := n) s F).card ≤ (keySpace F).card := by
        apply card_le_card_of_injOn (fun i => key F (once (address s i)))
        · exact fun i _ => key_mem F _
        · exact bank_keys_inj hF hw h₁ hJ hm s
      have hL := raw_le_banks F (fun a ha => (hR a).mp (N.raw_route hw ha).2.1)
      have hA := cardSide false
      have hB := cardSide true
      rw [keySpace_card] at hA hB
      change F.raw.card ≤ if F.hole = none then 4 else 8
      by_cases hh : F.hole = none
      · rw [ite_eq_left hh] at hA hB ⊢
        omega
      · rw [ite_eq_right hh] at hA hB ⊢
        omega
    cases h : N.code w with
    | raw => simp [Net.frag, N.build_raw h, Frag.bit]
    | lit b => simp [Net.frag, N.build_lit h, Frag.lit]
    | one f a =>
      apply finish (by simp [h]) (by simp [Net.join, N.build_one h])
      simpa [Net.frag, N.build_one h, Frag.unary] using
        (descend (a := a) (s := false) (by simp [h, Op.pin])).trans (show 8 ≤ 16 by omega)
    | two f a b =>
      by_cases hj : N.join bad w
      · simp [N.join_entry hj, Frag.entry]
      apply finish (by simp [h]) hj
      have hn : ¬((N.arg bad a).hole.isSome && (N.arg bad b).hole.isSome) = true := by
        simpa [N.join_two h] using hj
      simp only [Net.frag, N.build_two h, ite_eq_right hn, Frag.binary]
      have ha := descend (a := a) (s := false) (by simp [h, Op.pin])
      have hb := descend (a := b) (s := true) (by simp [h, Op.pin])
      exact (card_union_le _ _).trans (by omega)

theorem Net.agree_live {N : Net} (x y : ℕ → Bool)
    (h : ∀ a ∈ N.live, N.code a = .raw → x a = y a) : N.run x N.out = N.run y N.out := by
  have all (w) (hw : w ∈ N.live) : N.run x w = N.run y w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      have descend {a s} (he : (N.code w).pin s = some a) : N.run x a = N.run y a :=
        ih a (N.back he) (N.mem_live.mpr (.child (N.mem_live.mp hw) he))
      rw [Net.run_eq N x w, Net.run_eq N y w]
      cases he : N.code w with
      | raw => exact h w hw he
      | lit b => rfl
      | one f a => exact congrArg f (descend (a := a) (s := false) (by simp [he, Op.pin]))
      | two f a b =>
        exact congrArg₂ f (descend (a := a) (s := false) (by simp [he, Op.pin]))
          (descend (a := b) (s := true) (by simp [he, Op.pin]))
  exact all N.out (N.mem_live.mpr .top)

open Finset

noncomputable section

def owner (N : Net) (bad : Finset ℕ) (a : ℕ) : ℕ := by
  classical
  exact if h : N.Private bad a then (N.owner_exists h.1 h.2.1 h.2.2).exists.choose else 0

theorem owner_spec {N : Net} {bad : Finset ℕ} {a : ℕ} (h : N.Private bad a) :
    N.root bad (owner N bad a) ∧ a ∈ (N.frag bad (owner N bad a)).raw := by
  classical
  simpa only [owner, dite_eq_left h] using (N.owner_exists h.1 h.2.1 h.2.2).exists.choose_spec

theorem owner_eq {N : Net} {bad : Finset ℕ} {a w : ℕ} (hw : N.root bad w)
    (ha : a ∈ (N.frag bad w).raw) : owner N bad a = w := by
  have hh := owner_spec (N.root_support hw ha)
  exact (N.raw_route hh.1.1 hh.2).2.2.unique (N.raw_route hw.1 ha).2.2 hh.1.2.1 hw.2.1

def privateSide {n : ℕ} (N : Net) (bad : Finset ℕ) (s : Bool) : Finset (Fin n) := by
  classical
  exact univ.filter fun i => N.Private bad (address s i)

theorem mem_privateSide {n : ℕ} {N : Net} {bad : Finset ℕ} {s : Bool} {i : Fin n} :
    i ∈ privateSide N bad s ↔ N.Private bad (address s i) := by
  classical
  simp [privateSide]

def signature (N : Net) (bad : Finset ℕ) (a : ℕ) : ℕ × (Bool × Bool) :=
  let w := owner N bad a
  (w, key (N.frag bad w) (once a))

def ordinary {n : ℕ} (N : Net) (bad : Finset ℕ) (s : Bool) : Finset (Fin n) :=
  (privateSide N bad s).filter fun i =>
    (signature N bad (address s i)).2 ≠ baseline (N.frag bad (owner N bad (address s i)))

def unused {n : ℕ} (N : Net) (bad : Finset ℕ) (s : Bool) : Finset (Fin n) :=
  univ.filter fun i => address s i ∉ N.live ∧ address s i ∉ bad

theorem unused_le {n : ℕ} {N : Net} {bad : Finset ℕ} (hF : Far (n := n) N bad) (s : Bool) :
    (unused (n := n) N bad s).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  by_contra hn
  obtain ⟨_,hi',hi''⟩ := mem_filter.mp hi
  obtain ⟨_,hj',hj''⟩ := mem_filter.mp hj
  have hd := hF s i j hn hi'' hj''
  have he : view N s i = view N s j := by
    funext z
    apply N.agree_live _ _
    intro a ha _
    exact twice_same (fun h => hi' (h ▸ ha)) (fun h => hj' (h ▸ ha))
  simp [he, dist] at hd

theorem cover_raw {n : ℕ} {N : Net} {bad X : Finset ℕ} (hF : Far (n := n) N bad)
    (h : ∀ a ∈ N.live, N.code a = .raw → a ∉ bad → a ∈ X)
    (hR : RawBank n N) : 2*n ≤ X.card + bad.card + 2 := by
  classical
  let A := (unused (n := n) N bad false).image (address false)
  let B := (unused (n := n) N bad true).image (address true)
  have hsub : (range (n+n+1)).erase 0 ⊆ X ∪ bad ∪ A ∪ B := by
    intro w hw
    have hb : 0 < w ∧ w ≤ n+n := by
      have := mem_erase.mp hw
      have := mem_range.mp this.2
      omega
    by_cases hbad : w ∈ bad
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hbad))
    by_cases hl : w ∈ N.live
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (h w hl ((hR w).mpr hb) hbad)))
    obtain ⟨s,i,rfl⟩ := address_surj hb
    cases s
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hl,hbad⟩,rfl⟩))
    · exact mem_union_right _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hl,hbad⟩,rfl⟩)
  have hc := card_le_card hsub
  rw [card_erase_of_mem (by simp : 0 ∈ range (n+n+1)), card_range] at hc
  have hu := card_union_le (X ∪ bad ∪ A) B
  have hv := card_union_le (X ∪ bad) A
  have hx := card_union_le X bad
  have ha := (card_image_le (s := unused (n := n) N bad false) (f := address false)).trans (unused_le hF false)
  have hb := (card_image_le (s := unused (n := n) N bad true) (f := address true)).trans (unused_le hF true)
  change A.card ≤ 1 at ha
  change B.card ≤ 1 at hb
  omega

theorem private_lower {n : ℕ} {N : Net} {bad : Finset ℕ} (hF : Far (n := n) N bad) (hR : RawBank n N) :
    2*n ≤ (privateSide (n := n) N bad false).card + (privateSide (n := n) N bad true).card +
      N.excess + bad.card + 2 := by
  classical
  let A := (privateSide (n := n) N bad false).image (address false)
  let B := (privateSide (n := n) N bad true).image (address true)
  let X := A ∪ B ∪ N.live.filter N.shared
  have h := cover_raw hF (X := X) (fun w hl hr hb => by
    by_cases hc : N.shared w
    · exact mem_union_right _ (mem_filter.mpr ⟨hl,hc⟩)
    have hp : N.Private bad w := ⟨hl,hr,fun he => he.elim hc hb⟩
    obtain ⟨s,i,rfl⟩ := address_surj ((hR w).mp hr)
    cases s
    · exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨i,mem_privateSide.mpr hp,rfl⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨i,mem_privateSide.mpr hp,rfl⟩))) hR
  have hx := card_union_le (A ∪ B) (N.live.filter N.shared)
  have hu := card_union_le A B
  have ha := card_image_le (s := privateSide (n := n) N bad false) (f := address false)
  have hb := card_image_le (s := privateSide (n := n) N bad true) (f := address true)
  have hd := N.shared_le
  change 2*n ≤ X.card + bad.card + 2 at h
  change X.card ≤ _ at hx
  change A.card ≤ _ at ha
  change B.card ≤ _ at hb
  omega

theorem private_sig_inj {n : ℕ} {N : Net} {bad : Finset ℕ} (hF : Far (n := n) N bad)
    (hR : RawBank n N) (s : Bool) :
    Set.InjOn (fun i : Fin n => signature N bad (address s i)) (privateSide (n := n) N bad s) := by
  intro i hi j hj hk
  have hi' := owner_spec (mem_privateSide.mp hi)
  have hj' := owner_spec (mem_privateSide.mp hj)
  have hw : owner N bad (address s i) = owner N bad (address s j) := congrArg Prod.fst hk
  have hk' := congrArg Prod.snd hk
  change key (N.frag bad (owner N bad (address s i))) (once (address s i)) =
    key (N.frag bad (owner N bad (address s j))) (once (address s j)) at hk'
  rw [← hw] at hk' hj'
  have h8 := frag_small hR hF _ hi'.1.1
  have h16 : (N.frag bad (owner N bad (address s i))).raw.card ≤ 16 := h8.trans (by split <;> omega)
  exact bank_keys_inj hF hi'.1.1 hi'.1.2.2.2.1 hi'.1.2.2.1 h16 s
    (mem_filter.mpr ⟨mem_univ _,hi'.2⟩) (mem_filter.mpr ⟨mem_univ _,hj'.2⟩) hk'

theorem baseline_le {n : ℕ} {N : Net} {bad : Finset ℕ} (hF : Far (n := n) N bad)
    (hR : RawBank n N) (s : Bool) :
    ((privateSide (n := n) N bad s).filter fun i => (signature N bad (address s i)).2 =
      baseline (N.frag bad (owner N bad (address s i)))).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  by_contra hn
  let a := address s i
  let b := address s j
  obtain ⟨hi',hiK⟩ := mem_filter.mp hi
  obtain ⟨hj',hjK⟩ := mem_filter.mp hj
  have hpa := mem_privateSide.mp hi'
  have hpb := mem_privateSide.mp hj'
  let wa := owner N bad a
  let wb := owner N bad b
  have ha8 : (N.frag bad wa).raw.card ≤ 8 := (frag_small hR hF _ (owner_spec hpa).1.1).trans (by split <;> omega)
  have hb8 : (N.frag bad wb).raw.card ≤ 8 := (frag_small hR hF _ (owner_spec hpb).1.1).trans (by split <;> omega)
  let O := bank (n := n) (!s) (N.frag bad wa) ∪ bank (n := n) (!s) (N.frag bad wb)
  have hO : O.card ≤ 16 := (card_union_le _ _).trans (Nat.add_le_add ((bank_le _ _).trans ha8) ((bank_le _ _).trans hb8))
  have hdist := hF s i j hn (fun h => hpa.2.2 (Or.inr h)) (fun h => hpb.2.2 (Or.inr h))
  have hbd : dist (view N s i) (view N s j) ≤ O.card := by
    apply dist_le_of_agree
    intro z hz
    let c := address (!s) z
    have hcA : c ∉ (N.frag bad wa).raw := fun h => hz (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩))
    have hcB : c ∉ (N.frag bad wb).raw := fun h => hz (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩))
    apply N.transfer _ _
    · intro v _ _ hv
      exact twice_same (fun h => hpa.2.2 (h ▸ hv)) (fun h => hpb.2.2 (h ▸ hv))
    · intro w hw bit
      let F := N.frag bad w
      have hsingle (d : ℕ) (hk : key (N.frag bad (owner N bad d)) (once d) =
          baseline (N.frag bad (owner N bad d))) : F.f (once d) bit = F.f (fun _ => false) bit := by
        by_cases hd : d ∈ F.raw
        · have he := owner_eq hw hd
          rw [he] at hk
          exact key_apply hk bit
        · exact once_eq_base hd bit
      by_cases hc : c ∈ F.raw
      · have ha' : a ∉ F.raw := fun h => hcA (by
          change c ∈ (N.frag bad (owner N bad a)).raw
          rwa [owner_eq hw h])
        have hb' : b ∉ F.raw := fun h => hcB (by
          change c ∈ (N.frag bad (owner N bad b)).raw
          rwa [owner_eq hw h])
        change F.f (twice a c) bit = F.f (twice b c) bit
        rw [twice_comm a c, twice_comm b c, twice_eq_once ha', twice_eq_once hb']
      · rw [twice_eq_once hc, twice_eq_once hc, hsingle _ hiK, hsingle _ hjK]
  omega

theorem ordinary_lower {n : ℕ} {N : Net} {bad : Finset ℕ} (hF : Far (n := n) N bad) (hR : RawBank n N) :
    2*n ≤ (ordinary (n := n) N bad false).card + (ordinary (n := n) N bad true).card +
      N.excess + bad.card + 4 := by
  have hl := private_lower hF hR
  have hp (s : Bool) : (privateSide (n := n) N bad s).card ≤ (ordinary (n := n) N bad s).card + 1 := by
    have hh := card_filter_add_card_filter_not (s := privateSide (n := n) N bad s)
      (p := fun i => (signature N bad (address s i)).2 = baseline (N.frag bad (owner N bad (address s i))))
    have hb := baseline_le hF hR s
    change _ + (ordinary (n := n) N bad s).card = _ at hh
    omega
  have ha := hp false
  have hb := hp true
  omega

def allowedKeys (N : Net) (bad : Finset ℕ) (w : ℕ) : Finset (Bool × Bool) :=
  (keySpace (N.frag bad w)).erase (baseline (N.frag bad w))

theorem allowed_card (N : Net) (bad : Finset ℕ) (w : ℕ) :
    (allowedKeys N bad w).card = if (N.frag bad w).hole = none then 1 else 3 := by
  rw [allowedKeys, baseline, card_erase_of_mem (key_mem _ _), keySpace_card]
  split <;> rfl

theorem ordinary_allowed {n : ℕ} {N : Net} {bad : Finset ℕ} {s : Bool} {i : Fin n}
    (hi : i ∈ ordinary N bad s) : (signature N bad (address s i)).2 ∈
      allowedKeys N bad (owner N bad (address s i)) :=
  mem_erase.mpr ⟨(mem_filter.mp hi).2, key_mem _ _⟩

def tag (w : ℕ) : (Bool × Bool) ↪ ℕ × (Bool × Bool) :=
  ⟨fun k => (w,k), fun _ _ h => congrArg Prod.snd h⟩

theorem ordinary_union {n : ℕ} (N : Net) (bad : Finset ℕ) :
    (((ordinary (n := n) N bad false).image (fun i => signature N bad (address false i))) ∪
      ((ordinary (n := n) N bad true).image (fun i => signature N bad (address true i)))).card ≤
      (N.pure bad).card + 3 * (N.unary bad).card := by
  classical
  let A (s : Bool) := (ordinary (n := n) N bad s).image (fun i => signature N bad (address s i))
  let B := (N.roots bad).biUnion fun w => (allowedKeys N bad w).map (tag w)
  have hs (s) : A s ⊆ B := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    have hp := owner_spec (mem_privateSide.mp (mem_filter.mp hi).1)
    exact mem_biUnion.mpr ⟨_, N.mem_roots.mpr hp.1, mem_map.mpr ⟨_, ordinary_allowed hi, rfl⟩⟩
  have hb : B.card ≤ (N.pure bad).card + 3 * (N.unary bad).card := by
    apply card_biUnion_le.trans
    simp only [card_map, allowed_card]
    rw [Net.pure, Net.unary, card_eq_sum_ones, card_eq_sum_ones, sum_filter, sum_filter, mul_sum, ← sum_add_distrib]
    exact le_of_eq (sum_congr rfl fun w _ => by cases (N.frag bad w).hole <;> simp)
  exact (card_le_card (union_subset (hs false) (hs true))).trans hb

theorem matched_view {n : ℕ} {N : Net} {bad : Finset ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (h : ∀ i ∈ S, i ∈ ordinary N bad false ∧ π i ∈ ordinary N bad true ∧
      signature N bad (address false i) = signature N bad (address true (π i))) :
    ∀ i ∈ S, ∀ j ∈ S, owner N bad (address false i) ≠ owner N bad (address false j) →
      view N false i (π j) = view N false j (π i) := by
  intro i hi j hj hd
  let a := address false i
  let a' := address true (π i)
  let b := address false j
  let b' := address true (π j)
  let wa := owner N bad a
  let wb := owner N bad b
  obtain ⟨hi,hi',hA⟩ := h i hi
  obtain ⟨hj,hj',hB⟩ := h j hj
  have hwa : wa = owner N bad a' := congrArg Prod.fst hA
  have hwb : wb = owner N bad b' := congrArg Prod.fst hB
  have haK := congrArg Prod.snd hA
  have hbK := congrArg Prod.snd hB
  change key (N.frag bad wa) (once a) = key (N.frag bad (owner N bad a')) (once a') at haK
  change key (N.frag bad wb) (once b) = key (N.frag bad (owner N bad b')) (once b') at hbK
  rw [← hwa] at haK
  rw [← hwb] at hbK
  change N.run (twice a b') N.out = N.run (twice b a') N.out
  apply N.transfer _ _
  · intro z _ _ hz
    have hn (s : Bool) (i : Fin n) (hi : i ∈ ordinary N bad s) : z ≠ address s i := by
      intro hEq
      exact (mem_privateSide.mp (mem_filter.mp hi).1).2.2 (hEq ▸ hz)
    simp [twice, a, a', b, b', hn _ _ hi, hn _ _ hi', hn _ _ hj, hn _ _ hj']
  · intro w hw bit
    have apart {t : ℕ} (ht : owner N bad t ≠ w) : t ∉ (N.frag bad w).raw :=
      fun hn => ht (owner_eq hw hn)
    by_cases hwA : w = wa
    · subst w
      have h1 : b ∉ (N.frag bad wa).raw := apart (Ne.symm hd)
      have h2 : b' ∉ (N.frag bad wa).raw := apart (hwb ▸ (Ne.symm hd))
      rw [twice_eq_once h2, twice_comm b a', twice_eq_once h1, key_apply haK]
    by_cases hwB : w = wb
    · subst w
      have h1 : a ∉ (N.frag bad wb).raw := apart hd
      have h2 : a' ∉ (N.frag bad wb).raw := apart (hwa ▸ hd)
      rw [twice_comm a b', twice_eq_once h1, twice_eq_once h2, key_apply hbK]
    · have h1 : a ∉ (N.frag bad w).raw := apart (Ne.symm hwA)
      have h2 : b ∉ (N.frag bad w).raw := apart (Ne.symm hwB)
      have h3 : a' ∉ (N.frag bad w).raw := apart (hwa ▸ Ne.symm hwA)
      have h4 : b' ∉ (N.frag bad w).raw := apart (hwb ▸ Ne.symm hwB)
      rw [twice_eq_once h4, twice_eq_once h3, once_eq_base h1, once_eq_base h2]

theorem structural {n b : ℕ} (N : Net) (bad : Finset ℕ) (hF : Far (n := n) N bad)
    (hR : RawBank n N) (hbad : ∀ w ∈ bad, N.code w = .raw)
    (hb : (N.live.filter fun a => (N.code a).arity = 2).card ≤ b) :
    ∃ (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (piece : Fin n → ℕ),
      32*n ≤ 15*b+50+22*bad.card+S.card ∧
      (∀ t, (S.filter fun i => piece i = t).card ≤ 3) ∧
      (∀ i ∈ S, ∀ j ∈ S, piece i ≠ piece j → view N false i (π j) = view N false j (π i)) := by
  classical
  let A := ordinary (n := n) N bad false
  let B := ordinary (n := n) N bad true
  let a (i : Fin n) := signature N bad (address false i)
  let c (i : Fin n) := signature N bad (address true i)
  have ha := (private_sig_inj hF hR false).mono (filter_subset _ _ : A ⊆ _)
  have hc := (private_sig_inj hF hR true).mono (filter_subset _ _ : B ⊆ _)
  obtain ⟨π,S,hcount,hS,hmatch⟩ := match_keys A B a c ha hc
  refine ⟨π,S,fun i => owner N bad (address false i), ?_, ?_, ?_⟩
  · have hpart := ordinary_lower hF hR
    have hk := ordinary_union (n := n) N bad
    have hp := N.pure_bound bad hbad
    have hu := N.unary_bound bad
    have hd := N.ledger
    have hl := cover_raw hF (X := N.live.filter fun a => (N.code a).arity = 0)
      (fun w hw hr _ => mem_filter.mpr ⟨hw,by simp [hr,Op.arity]⟩) hR
    change 2*n ≤ A.card + B.card + N.excess + bad.card + 4 at hpart
    change (A.image a ∪ B.image c).card ≤ _ at hk
    omega
  · intro t
    let U := S.filter fun i => owner N bad (address false i) = t
    have hinj : Set.InjOn (fun i => (a i).2) U := by
      intro i hi j hj h
      have h₁ := mem_filter.mp hi
      have h₂ := mem_filter.mp hj
      apply ha (hS h₁.1) (hS h₂.1)
      exact Prod.ext (h₁.2.trans h₂.2.symm) h
    apply le_trans (card_le_card_of_injOn (fun i => (a i).2) (t := allowedKeys N bad t) ?_ hinj)
      (by rw [allowed_card]; split <;> omega)
    intro i hi
    change (a i).2 ∈ allowedKeys N bad t
    rw [← (mem_filter.mp hi).2]
    exact ordinary_allowed (hS (mem_filter.mp hi).1)
  · exact matched_view π S (fun i hi => ⟨hS hi,hmatch i hi⟩)

end

open Finset PEqualNP.CircuitLowerBounds

theorem view_left {n : ℕ} (C : Circuit) (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (i j : Fin n) :
    view (ofCircuit (n+n) C) false i j = C.eval (PEqualNP.Represents.oneEach i j) := by
  let x := PEqualNP.Represents.oneEach i j
  let X := twice (address false i) (address true j)
  have hlen : x.length = n + n := by simp [x, PEqualNP.Represents.oneEach]
  have hx (k : ℕ) (_ : k < x.length) : X (k+1) = x.getD k false := by
    change twice (address false i) (address true j) (k+1) = _
    rw [show x = PEqualNP.Represents.oneEach i j from rfl, oneEach_getD]
    simp [twice, address]
  change (ofCircuit (n+n) C).run X (ofCircuit (n+n) C).out = C.eval x
  simpa only [hlen] using ofCircuit_eval C x X hx hg

theorem view_right {n : ℕ} (C : Circuit) (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (i j : Fin n) :
    view (ofCircuit (n+n) C) true i j = C.eval (PEqualNP.Represents.oneEach j i) := by
  change (ofCircuit (n+n) C).run (twice (address true i) (address false j)) _ = _
  rw [twice_comm]
  exact view_left C hg j i

theorem marked_results {n : ℕ} (T : Fin n → Fin n → Bool) (C : Circuit) (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (H : Fin n → Fin n → Bool) (hH : ∀ i j, H i j = C.eval (PEqualNP.Represents.oneEach i j))
    (v : ℕ) (hv : 0 < v)
    (hr : ∀ i j, i ≠ j → 17 + 2*(v-1) ≤ dist (T i) (T j))
    (hc : ∀ i j, i ≠ j → 17 + 2*(v-1) ≤ dist (fun z => T z i) (fun z => T z j)) :
    ∃ bad : Finset ℕ, Far (n := n) (ofCircuit (n+n) C) bad ∧
      (∀ a ∈ bad, (ofCircuit (n+n) C).code a = .raw) ∧
      bad.card ≤ 2 * ((univ.filter fun z : Fin n × Fin n => H z.1 z.2 ≠ T z.1 z.2).card / v) := by
  let R := univ.filter fun i => v ≤ dist (H i) (T i)
  let L := univ.filter fun i => v ≤ dist (fun z => H z i) (fun z => T z i)
  let bad := R.image (address false) ∪ L.image (address true)
  have hR (i : Fin n) (hi : address false i ∉ bad) : dist (H i) (T i) < v := by
    apply Nat.lt_of_not_ge
    intro he
    exact hi (mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,he⟩)))
  have hL (i : Fin n) (hi : address true i ∉ bad) : dist (fun z => H z i) (fun z => T z i) < v := by
    apply Nat.lt_of_not_ge
    intro he
    exact hi (mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,he⟩)))
  refine ⟨bad, ?_, ?_, ?_⟩
  · intro s i j hij hi hj
    cases s
    · have h₁ : view (ofCircuit (n+n) C) false i = H i := funext fun z => (view_left C hg i z).trans (hH i z).symm
      have h₂ : view (ofCircuit (n+n) C) false j = H j := funext fun z => (view_left C hg j z).trans (hH j z).symm
      rw [h₁,h₂]
      exact good_dist (H i) (H j) (T i) (T j) v hv (hR i hi) (hR j hj) (hr i j hij)
    · have h₁ : view (ofCircuit (n+n) C) true i = fun z => H z i := funext fun z => (view_right C hg i z).trans (hH z i).symm
      have h₂ : view (ofCircuit (n+n) C) true j = fun z => H z j := funext fun z => (view_right C hg j z).trans (hH z j).symm
      rw [h₁,h₂]
      exact good_dist (fun z => H z i) (fun z => H z j) (fun z => T z i) (fun z => T z j) v hv
        (hL i hi) (hL j hj) (hc i j hij)
  · intro w hw
    change w ∈ R.image (address false) ∪ L.image (address true) at hw
    rcases mem_union.mp hw with hw | hw <;> obtain ⟨i,_,rfl⟩ := mem_image.mp hw
    · exact codeAt_raw.mpr ⟨address_pos false i,address_le false i⟩
    · exact codeAt_raw.mpr ⟨address_pos true i,address_le true i⟩
  · let e := (univ.filter fun z : Fin n × Fin n => H z.1 z.2 ≠ T z.1 z.2).card
    have hr' : R.card ≤ e / v := (error_rows H T v).resolve_right (Nat.ne_of_gt hv)
    have hl' : L.card ≤ e / v := by
      have ht := (error_rows (fun i j => H j i) (fun i j => T j i) v).resolve_right (Nat.ne_of_gt hv)
      rwa [error_transpose H T] at ht
    exact (card_union_le _ _).trans (by
      have h1 := card_image_le (s := R) (f := address false)
      have h2 := card_image_le (s := L) (f := address true)
      change _ ≤ 2 * (e / v)
      omega)

end PEqualNP.Outside.L_meta_25879.Struct

theorem PEqualNP.Outside.L_meta_25879.Struct.structural_main : ∀ n : ℕ, 2 ≤ n →
  let I := Fin n
  ∀ (T : I → I → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) →
    let H := fun i j : I => C.eval (PEqualNP.Represents.oneEach i j)
    let e := (Finset.univ.filter (fun z : I × I => H z.1 z.2 ≠ T z.1 z.2)).card
    let b := C.gates.countP (fun gate => gate.inputs.length == 2)
    ∀ v : ℕ, 0 < v →
      (∀ i j : I, i ≠ j → 17+2*(v-1) ≤ (Finset.univ.filter (fun z : I => T i z ≠ T j z)).card) →
      (∀ i j : I, i ≠ j → 17+2*(v-1) ≤ (Finset.univ.filter (fun z : I => T z i ≠ T z j)).card) →
      ∃ (π : Equiv.Perm I) (S : Finset I) (piece : I → ℕ),
        32*n ≤ 15*b+50+44*(e/v)+S.card ∧
        (∀ t : ℕ, (S.filter (fun i => piece i = t)).card ≤ 3) ∧
        (∀ i ∈ S, ∀ j ∈ S, piece i ≠ piece j → H i (π j) = H j (π i)) ∧
        ∀ U : Finset I, U ⊆ S →
          ((U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))).card ≤
            U.card + ((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).card := by
  classical
  intro n _ I T C hg H e b v hv hrow hcol
  obtain ⟨bad, hfar, hbad, hcount⟩ := PEqualNP.Outside.L_meta_25879.Struct.marked_results
    T C hg H (fun _ _ => rfl) v hv hrow hcol
  obtain ⟨π,S,p,hS,hcap,hsym⟩ := PEqualNP.Outside.L_meta_25879.Struct.structural
    (PEqualNP.Outside.L_meta_25879.Struct.ofCircuit (n+n) C) bad hfar
    (fun _ => PEqualNP.Outside.L_meta_25879.Struct.codeAt_raw) hbad
    (PEqualNP.Outside.L_meta_25879.Struct.ofCircuit_bin _ C hg)
  have hHsym : ∀ i ∈ S, ∀ j ∈ S, p i ≠ p j → H i (π j) = H j (π i) := by
    intro i hi j hj hp
    simpa only [PEqualNP.Outside.L_meta_25879.Struct.view_left C hg] using hsym i hi j hj hp
  refine ⟨π,S,p,?_,hcap,hHsym,?_⟩
  · change 32 * n ≤ 15 * b + 50 + 44 * (e / v) + S.card
    change bad.card ≤ 2 * (e / v) at hcount
    change 32 * n ≤ 15 * b + 50 + 22 * bad.card + S.card at hS
    omega
  · exact PEqualNP.Outside.L_meta_25879.Struct.conflict_bound T H π S p hcap hHsym

namespace PEqualNP.Outside.L_meta_25879

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem xor_pairs_card (k : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range (2 ^ k)) :
    (Finset.univ.filter (fun z : Fin (2 ^ k) × Fin (2 ^ k) => Nat.xor z.1.val z.2.val ∈ S)).card =
      2 ^ k * S.card := by
  classical
  let N := 2 ^ k
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := (Finset.univ : Finset (Fin N)))
    (fun _ _ => Finset.mem_univ _)]
  have hfiber : ∀ x : Fin N,
      ((Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ S)).filter
        (fun z => z.1 = x)).card = S.card := by
    intro x
    have heq : ((Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ S)).filter
        (fun z => z.1 = x)) =
        (Finset.univ.filter (fun y : Fin N => x.val ^^^ y.val ∈ S)).map
          ⟨fun y => (x, y), fun _ _ h => congrArg Prod.snd h⟩ := by
      ext ⟨x', y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · rintro ⟨h1, rfl⟩; exact ⟨y, h1, rfl⟩
      · rintro ⟨y', h1, h2⟩
        injection h2 with hx' hy'
        subst hx'; subst hy'; exact ⟨h1, rfl⟩
    rw [heq, Finset.card_map]
    exact card_xor_mem_gamma k S hS x
  rw [Finset.sum_congr rfl fun x _ => hfiber x, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem circuit_gamma_error_lower (k a : ℕ) (ha : 6 ≤ a) (hk : 2 * 2 ^ a ≤ k)
    (P : Polynomial (ZMod 2)) (hPm : P.Monic) (hPi : Irreducible P) (hPd : P.natDegree = k / 2)
    (f g : Fin (2 ^ k) → Bool) (C : Circuit)
    (hfits : (∀ gt ∈ C.gates, gt.inputs.length ≤ 2) ∧
      16 * (C.gates.countP (fun gt => gt.inputs.length == 2)) ≤ 33 * 2 ^ k) :
    let N := 2 ^ k
    let r := 2 ^ a
    let I := Fin N
    let Γ := gammaSet (k / 2) P
    let target := fun (D : Finset ℕ) (x y : I) =>
      xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
    let H := fun x y : I => C.eval (oneEach x y)
    let e := (Finset.univ.filter (fun z : I × I => H z.1 z.2 ≠ xor (target Γ z.1 z.2) (xor (f z.1) (g z.2)))).card
    N * 2 ^ (k / 2) < 128 * e := by
  classical
  dsimp only
  let N : ℕ := 2 ^ k
  let r : ℕ := 2 ^ a
  let m : ℕ := k / 2
  let Q : ℕ := 2 ^ m
  let Γ : Finset ℕ := gammaSet m P
  let target : Finset ℕ → Fin N → Fin N → Bool := fun D x y =>
    xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
  let T : Fin N → Fin N → Bool := fun x y => xor (target Γ x y) (xor (f x) (g y))
  let H : Fin N → Fin N → Bool := fun x y => C.eval (oneEach x y)
  let e : ℕ := (Finset.univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠ T z.1 z.2)).card
  let b : ℕ := C.gates.countP (fun gt => gt.inputs.length == 2)
  change N * Q < 128 * e
  have hr64 : 64 ≤ r := by
    calc (64 : ℕ) = 2 ^ 6 := by decide
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
  have hk128 : 128 ≤ k := by omega
  have hm64 : 64 ≤ m := by dsimp [m]; omega
  have h2mk : 2 * m ≤ k := by dsimp [m]; omega
  have hQ4096 : 4096 ≤ Q := by
    calc (4096 : ℕ) = 2 ^ 12 := by decide
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  have hNQ : 1024 * Q ≤ N := by
    have h1 : 10 + m ≤ k := by omega
    calc 1024 * Q = 2 ^ 10 * 2 ^ m := by rfl
      _ = 2 ^ (10 + m) := (Nat.pow_add 2 10 m).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) h1
  have hNbig : 131072 ≤ N := by
    calc (131072 : ℕ) = 2 ^ 17 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  have hΓsub : Γ ⊆ Finset.range N := gammaSet_subset m k P h2mk
  have hΓcard : Γ.card = Q := gammaSet_card m P
  have hauto : ∀ d, d ≠ 0 → (Γ.filter (fun z => z ^^^ d ∈ Γ)).card ≤ 2 :=
    gammaSet_autocorr m (by omega) P hPm hPi hPd
  by_contra hle
  push Not at hle
  have hdist := row_col_dist_ge k a ha hk Γ hΓsub hΓcard hauto f g
  let v : ℕ := Q - 10
  have hv_pos : 0 < v := by omega
  have hv_dist : 17 + 2 * (v - 1) ≤ 2 * Q - 4 := by dsimp [v]; omega
  have hrow : ∀ i j : Fin N, i ≠ j → 17 + 2 * (v - 1) ≤ (Finset.univ.filter (fun z : Fin N => T i z ≠ T j z)).card :=
    fun i j hij => le_trans hv_dist (hdist.1 i j hij)
  have hcol : ∀ i j : Fin N, i ≠ j → 17 + 2 * (v - 1) ≤ (Finset.univ.filter (fun z : Fin N => T z i ≠ T z j)).card :=
    fun i j hij => le_trans hv_dist (hdist.2 i j hij)
  obtain ⟨π, S, piece, hS, _, _, hconf⟩ :=
    PEqualNP.Outside.L_meta_25879.Struct.structural_main N (by omega) T C hfits.1 v hv_pos hrow hcol
  have hS' : 32 * N ≤ 15 * b + 50 + 44 * (e / v) + S.card := hS
  have hb_bound : 16 * b ≤ 33 * N := hfits.2
  have hev_bound : 127 * (e / v) ≤ N := by
    have hmul : v * (e / v) ≤ e := Nat.mul_div_le e v
    have h1 : 128 * (v * (e / v)) ≤ N * Q := le_trans (Nat.mul_le_mul_left 128 hmul) hle
    have h2 : 127 * Q ≤ 128 * v := by dsimp [v]; omega
    have h3 : 127 * Q * (e / v) ≤ 128 * v * (e / v) := Nat.mul_le_mul_right _ h2
    have h4 : Q * (127 * (e / v)) ≤ Q * N := by linarith
    exact Nat.le_of_mul_le_mul_left h4 (by omega)
  have hScard : 7 * N ≤ 10 * S.card := by
    have h1 : 16 * 127 * (32 * N) ≤ 16 * 127 * (15 * b + 50 + 44 * (e / v) + S.card) :=
      Nat.mul_le_mul_left _ hS'
    nlinarith
  let S0 : Finset (Fin N) := S.filter (fun x => xor (f x) (g (π x)) = false)
  let S1 : Finset (Fin N) := S.filter (fun x => xor (f x) (g (π x)) = true)
  have hSsplit : S0.card + S1.card = S.card := by
    have h1 : S1 = S.filter (fun x => ¬ (xor (f x) (g (π x)) = false)) := by
      ext x
      simp only [S1, Finset.mem_filter, Bool.not_eq_false]
    rw [h1]
    exact Finset.card_filter_add_card_filter_not (s := S) (p := fun x => xor (f x) (g (π x)) = false)
  have hU_exists : ∃ U : Finset (Fin N), U ⊆ S ∧ S.card ≤ 2 * U.card ∧
      ∀ x ∈ U, ∀ y ∈ U, xor (f x) (g (π x)) = xor (f y) (g (π y)) := by
    by_cases hcmp : S1.card ≤ S0.card
    · refine ⟨S0, Finset.filter_subset _ _, by omega, ?_⟩
      intro x hx y hy
      rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]
    · refine ⟨S1, Finset.filter_subset _ _, by omega, ?_⟩
      intro x hx y hy
      rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]
  obtain ⟨U, hUS, hU2, hUconst⟩ := hU_exists
  have hUcard : 7 * N ≤ 20 * U.card := by omega
  let Dbase : Finset (Fin N × Fin N) :=
    (U ×ˢ U).filter (fun z => z.1.val.testBit ((π z.2).val % r) ≠ z.2.val.testBit ((π z.1).val % r))
  let Dord : Finset (Fin N × Fin N) := Dbase.filter (fun z => z.1 < z.2)
  have hbase_int := base_asym_lower k a ha hk π U
  have hbase_nat : 4 * U.card * U.card ≤ N * U.card + 8 * Dbase.card := by
    have h1 : ((4 * U.card * U.card : ℕ) : ℤ) ≤ ((N * U.card + 8 * Dbase.card : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast h1
  have hDbase_eq : Dbase.card = 2 * Dord.card := by
    let Dgt : Finset (Fin N × Fin N) := Dbase.filter (fun z => z.2 < z.1)
    have hdisj : Disjoint Dord Dgt := by
      rw [Finset.disjoint_left]
      intro z h1 h2
      exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hunion : Dord ∪ Dgt = Dbase := by
      ext ⟨x, y⟩
      simp only [Dord, Dgt, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        have hne : x ≠ y := by
          intro hxy; subst hxy
          exact (Finset.mem_filter.mp h).2 rfl
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨h, hlt⟩
        · exact Or.inr ⟨h, hgt⟩
    have hswap : Dgt.card = Dord.card := by
      apply Finset.card_bij (fun z _ => (z.2, z.1))
      · intro ⟨x, y⟩ hz
        simp only [Dgt, Dord, Dbase, Finset.mem_filter, Finset.mem_product] at hz ⊢
        exact ⟨⟨⟨hz.1.1.2, hz.1.1.1⟩, Ne.symm hz.1.2⟩, hz.2⟩
      · intro ⟨x1, y1⟩ _ ⟨x2, y2⟩ _ heq
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext heq.2 heq.1
      · intro ⟨x, y⟩ hz
        refine ⟨(y, x), ?_, rfl⟩
        simp only [Dgt, Dord, Dbase, Finset.mem_filter, Finset.mem_product] at hz ⊢
        exact ⟨⟨⟨hz.1.1.2, hz.1.1.1⟩, Ne.symm hz.1.2⟩, hz.2⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj, hswap]
    omega
  have hDord_lower : 7 * N * N ≤ 800 * Dord.card := by
    have h1 : 4 * U.card * U.card ≤ N * U.card + 16 * Dord.card := by omega
    have h2 : 1600 * (U.card * U.card) ≤ 400 * N * U.card + 6400 * Dord.card := by linarith
    have h3 : 20 * U.card ≥ 7 * N := hUcard
    have h4 : 56 * N * N + 400 * N * U.card ≤ 1600 * (U.card * U.card) := by nlinarith
    linarith
  let DT : Finset (Fin N × Fin N) :=
    (U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))
  let G1 : Finset (Fin N × Fin N) :=
    Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val (π z.2).val ∈ Γ)
  let G2 : Finset (Fin N × Fin N) :=
    Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.2.val (π z.1).val ∈ Γ)
  have hfg_bool : ∀ a1 a2 b1 b2 : Bool, xor a1 b1 = xor a2 b2 → xor a1 b2 = xor a2 b1 := by
    intro a1 a2 b1 b2; cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> decide
  have hxor_inj : ∀ a1 a2 c : Bool, xor a1 c = xor a2 c → a1 = a2 := by
    intro a1 a2 c; cases a1 <;> cases a2 <;> cases c <;> decide
  have hsub : Dord ⊆ DT ∪ G1 ∪ G2 := by
    intro ⟨x, y⟩ hz
    simp only [Dord, Dbase, Finset.mem_filter, Finset.mem_product] at hz
    obtain ⟨⟨⟨hx, hy⟩, hne⟩, hlt⟩ := hz
    by_cases h1 : Nat.xor x.val (π y).val ∈ Γ
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩))
    · by_cases h2 : Nat.xor y.val (π x).val ∈ Γ
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
      · apply Finset.mem_union_left _
        apply Finset.mem_union_left _
        simp only [DT, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨hx, hy⟩, hlt, ?_⟩
        have hfg : xor (f x) (g (π y)) = xor (f y) (g (π x)) :=
          hfg_bool (f x) (f y) (g (π x)) (g (π y)) (hUconst x hx y hy)
        dsimp only [T, target]
        rw [decide_eq_false h1, decide_eq_false h2, Bool.xor_false, Bool.xor_false, hfg]
        intro heq
        exact hne (hxor_inj _ _ _ heq)
  have hG1_card : G1.card = N * Q := by
    have hbij : G1.card = (Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ Γ)).card := by
      apply Finset.card_bij (fun z _ => (z.1, π z.2))
      · intro z hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro z1 _ z2 _ heq
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext heq.1 (π.injective heq.2)
      · intro ⟨x, y⟩ hy
        refine ⟨(x, π.symm y), ?_, by simp⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hy).2⟩
    rw [hbij, xor_pairs_card k Γ hΓsub, hΓcard]
  have hG2_card : G2.card = N * Q := by
    have hbij : G2.card = (Finset.univ.filter (fun z : Fin N × Fin N => Nat.xor z.1.val z.2.val ∈ Γ)).card := by
      apply Finset.card_bij (fun z _ => (z.2, π z.1))
      · intro z hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro z1 _ z2 _ heq
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext (π.injective heq.2) heq.1
      · intro ⟨x, y⟩ hy
        refine ⟨(π.symm y, x), ?_, by simp⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hy).2⟩
    rw [hbij, xor_pairs_card k Γ hΓsub, hΓcard]
  have hDT_le : DT.card ≤ N + e := by
    have h1 := hconf U hUS
    have hUle : U.card ≤ N := by
      calc U.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ U
        _ = N := by simp
    have hEle : ((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).card ≤ e := by
      let emb : Fin N × Fin N ↪ Fin N × Fin N :=
        ⟨fun z => (z.1, π z.2), fun z1 z2 h => Prod.ext (Prod.mk.inj h).1 (π.injective (Prod.mk.inj h).2)⟩
      have hmap_sub : ((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).map emb ⊆
          Finset.univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠ T z.1 z.2) := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm (Finset.mem_filter.mp hw).2⟩
      calc ((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).card
          = (((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).map emb).card := (Finset.card_map _).symm
        _ ≤ e := Finset.card_le_card hmap_sub
    exact le_trans h1 (Nat.add_le_add hUle hEle)
  have hDord_upper : Dord.card ≤ 4 * N * Q := by
    have hu1 := Finset.card_le_card hsub
    have hu2 := le_trans (Finset.card_union_le (DT ∪ G1) G2)
      (Nat.add_le_add_right (Finset.card_union_le DT G1) G2.card)
    have h1 : Dord.card ≤ DT.card + G1.card + G2.card := le_trans hu1 hu2
    rw [hG1_card, hG2_card] at h1
    have hNleNQ : N ≤ N * Q := Nat.le_mul_of_pos_right N (by omega)
    linarith
  have h7N : 7 * N * N ≤ 3200 * N * Q := by
    calc 7 * N * N ≤ 800 * Dord.card := hDord_lower
      _ ≤ 800 * (4 * N * Q) := Nat.mul_le_mul_left 800 hDord_upper
      _ = 3200 * N * Q := by ring
  have h7N' : N * (7 * N) ≤ N * (3200 * Q) := by linarith
  have hfinal : 7 * N ≤ 3200 * Q := Nat.le_of_mul_le_mul_left h7N' (by omega)
  linarith

end PEqualNP.Outside.L_meta_25879

theorem PEqualNP.Outside.L_meta_25879 :
  ∀ k a : ℕ, (6 ≤ a ∧ 2*2^a ≤ k) →
    let N := 2^k
    let r := 2^a
    let I := Fin N
    let target := fun (D : Finset ℕ) (x y : I) =>
      xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
    let Q := 2^(k/2)
    let fits := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ 16*(C.gates.countP (fun g => g.inputs.length == 2)) ≤ 33*N
    let table := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : I) =>
      C.eval (PEqualNP.Represents.oneEach x y)
    ∃ Γ : Finset ℕ, Γ ⊆ Finset.range N ∧ Γ.card = Q ∧
      PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) (target Γ))
        (150*(k+1)^2) ∧
      ∀ f g : I → Bool,
        let loss := fun (H : I → I → Bool) (D : Finset ℕ) =>
          (Finset.univ.filter (fun z : I × I => H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2)))).card
        ∃ C₀, fits C₀ ∧ (∀ D : Finset ℕ, D ⊆ Γ → loss (table C₀) D = N*D.card) ∧
          ∀ t : ℕ, t ≤ Q →
            let sets := Γ.powersetCard t
            let opt := N * min t (Q-t)
            (∀ H : I → I → Bool, opt ≤ sets.sup (loss H)) ∧
            (∃ H : I → I → Bool, sets.sup (loss H) = opt) ∧
            ∀ (l : ℕ) (w : Fin l → ℝ) (C : Fin l → PEqualNP.CircuitLowerBounds.Circuit),
              (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → (∀ i, fits (C i)) →
              ∃ D ∈ sets,
                let err := ∑ i : Fin l, w i * (loss (table (C i)) D : ℝ)
                (opt : ℝ) ≤ err ∧ (Q < 2*t →
                  ((128*(N*(Q-t))+N*(2*t-Q) : ℕ) : ℝ) < 128*err) := by
  classical
  intro k a ⟨ha, hk⟩ N r I target Q fits table
  have hr64 : 64 ≤ 2 ^ a := by
    calc (64 : ℕ) = 2 ^ 6 := by decide
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
  have hm_pos : 0 < k / 2 := by omega
  have h2mk : 2 * (k / 2) ≤ k := by omega
  obtain ⟨P, hPm, hPi, hPd⟩ := PEqualNP.Outside.L_meta_25879.exists_irred_poly (k / 2) hm_pos
  let Γ : Finset ℕ := PEqualNP.Outside.L_meta_25879.gammaSet (k / 2) P
  have hΓsub : Γ ⊆ Finset.range N := PEqualNP.Outside.L_meta_25879.gammaSet_subset (k / 2) k P h2mk
  have hΓcard : Γ.card = Q := PEqualNP.Outside.L_meta_25879.gammaSet_card (k / 2) P
  refine ⟨Γ, hΓsub, hΓcard, PEqualNP.Outside.L_meta_25879.Lit.hasLitSize_target_gamma k a ha hk P, ?_⟩
  intro f g loss
  obtain ⟨C₀, hC₀_fits, hC₀_loss⟩ := PEqualNP.Outside.L_meta_25879.exists_base_circuit k a ha hk Γ hΓsub f g
  refine ⟨C₀, hC₀_fits, hC₀_loss, ?_⟩
  intro t ht sets opt
  have hsets_card : 0 < sets.card := by
    rw [Finset.card_powersetCard, hΓcard]
    exact Nat.choose_pos ht
  have hsets_ne : sets.Nonempty := Finset.card_pos.mp hsets_card
  have hQ_pos : 0 < Q := Nat.pow_pos (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro H
    have havg := (PEqualNP.Outside.L_meta_25879.loss_powersetCard_avg k a Γ hΓsub f g t (by rw [hΓcard]; exact ht) H).1
    rw [hΓcard] at havg
    have hsup : ∑ D ∈ sets, loss H D ≤ sets.card * sets.sup (loss H) := by
      calc ∑ D ∈ sets, loss H D
          ≤ ∑ _D ∈ sets, sets.sup (loss H) := Finset.sum_le_sum fun D hD => Finset.le_sup (f := loss H) hD
        _ = sets.card * sets.sup (loss H) := by rw [Finset.sum_const, smul_eq_mul]
    exact Nat.le_of_mul_le_mul_left (le_trans havg hsup) hsets_card
  · by_cases hcmp : t ≤ Q - t
    · refine ⟨table C₀, ?_⟩
      have hconst : ∀ D ∈ sets, loss (table C₀) D = opt := by
        intro D hD
        obtain ⟨hDsub, hDcard⟩ := Finset.mem_powersetCard.mp hD
        have hlossD : loss (table C₀) D = N * D.card := hC₀_loss D hDsub
        rw [hlossD, hDcard]
        dsimp only [opt]
        rw [Nat.min_eq_left hcmp]
      apply le_antisymm
      · exact Finset.sup_le fun D hD => le_of_eq (hconst D hD)
      · obtain ⟨D, hD⟩ := hsets_ne
        rw [← hconst D hD]
        exact Finset.le_sup (f := loss (table C₀)) hD
    · let H1 : I → I → Bool := fun x y => xor (target Γ x y) (xor (f x) (g y))
      refine ⟨H1, ?_⟩
      have hconst : ∀ D ∈ sets, loss H1 D = opt := by
        intro D hD
        obtain ⟨hDsub, hDcard⟩ := Finset.mem_powersetCard.mp hD
        have hfilt : (Finset.univ.filter (fun z : I × I =>
            H1 z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2)))) =
            Finset.univ.filter (fun z : I × I => Nat.xor z.1.val z.2.val ∈ Γ \ D) := by
          ext ⟨x, y⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, H1, target]
          by_cases h1 : Nat.xor x.val y.val ∈ Γ <;> by_cases h2 : Nat.xor x.val y.val ∈ D
          · simp only [h1, h2, decide_true, not_true_eq_false, and_false, ne_eq, not_true_eq_false]
          · simp only [h1, h2, decide_true, decide_false, not_false_eq_true, and_self, iff_true]
            cases x.val.testBit (y.val % r) <;> cases f x <;> cases g y <;> decide
          · exact absurd (hDsub h2) h1
          · simp only [h1, h2, decide_false, not_false_eq_true, false_and, ne_eq, not_true_eq_false]
        change (Finset.univ.filter (fun z : I × I =>
          H1 z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2)))).card = opt
        rw [hfilt, PEqualNP.Outside.L_meta_25879.xor_pairs_card k (Γ \ D) (Finset.Subset.trans Finset.sdiff_subset hΓsub),
          Finset.card_sdiff_of_subset hDsub, hΓcard, hDcard]
        dsimp only [opt]
        rw [Nat.min_eq_right (by omega)]
      apply le_antisymm
      · exact Finset.sup_le fun D hD => le_of_eq (hconst D hD)
      · obtain ⟨D, hD⟩ := hsets_ne
        rw [← hconst D hD]
        exact Finset.le_sup (f := loss H1) hD
  · intro l w C hw0 hw1 hCfits
    let err : Finset ℕ → ℝ := fun D => ∑ i : Fin l, w i * (loss (table (C i)) D : ℝ)
    have hsum_err : ∑ D ∈ sets, err D = ∑ i : Fin l, w i * ∑ D ∈ sets, (loss (table (C i)) D : ℝ) := by
      dsimp only [err]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_sum]
    by_cases hQt : Q < 2 * t
    · have hstrict_i : ∀ i : Fin l,
          ((sets.card : ℝ) * ((128 * (N * (Q - t)) + N * (2 * t - Q) : ℕ) : ℝ)) <
            128 * ∑ D ∈ sets, (loss (table (C i)) D : ℝ) := by
        intro i
        have havg := (PEqualNP.Outside.L_meta_25879.loss_powersetCard_avg k a Γ hΓsub f g t
          (by rw [hΓcard]; exact ht) (table (C i))).2 (by rw [hΓcard]; exact hQt)
        rw [hΓcard] at havg
        have havg' : sets.card * (Q * (N * (Q - t)) + (2 * t - Q) * loss (table (C i)) Γ) ≤
            Q * ∑ D ∈ sets, loss (table (C i)) D := havg
        have hlow : N * Q < 128 * loss (table (C i)) Γ :=
          PEqualNP.Outside.L_meta_25879.circuit_gamma_error_lower k a ha hk P hPm hPi hPd f g (C i) (hCfits i)
        have hmul128 : sets.card * (128 * Q * (N * (Q - t)) + (2 * t - Q) * (128 * loss (table (C i)) Γ)) ≤
            Q * (128 * ∑ D ∈ sets, loss (table (C i)) D) := by
          have := Nat.mul_le_mul_left 128 havg'
          linarith
        have hlt_inner : 128 * Q * (N * (Q - t)) + (2 * t - Q) * (N * Q) <
            128 * Q * (N * (Q - t)) + (2 * t - Q) * (128 * loss (table (C i)) Γ) :=
          Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hlow (by omega)) _
        have hlt_mul : sets.card * (128 * Q * (N * (Q - t)) + (2 * t - Q) * (N * Q)) <
            Q * (128 * ∑ D ∈ sets, loss (table (C i)) D) :=
          lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hlt_inner hsets_card) hmul128
        have hfac : sets.card * (128 * Q * (N * (Q - t)) + (2 * t - Q) * (N * Q)) =
            Q * (sets.card * (128 * (N * (Q - t)) + N * (2 * t - Q))) := by ring
        rw [hfac] at hlt_mul
        have hnat_lt : sets.card * (128 * (N * (Q - t)) + N * (2 * t - Q)) <
            128 * ∑ D ∈ sets, loss (table (C i)) D :=
          Nat.lt_of_mul_lt_mul_left hlt_mul
        have hreal_lt : ((sets.card * (128 * (N * (Q - t)) + N * (2 * t - Q)) : ℕ) : ℝ) <
            ((128 * ∑ D ∈ sets, loss (table (C i)) D : ℕ) : ℝ) := by
          exact_mod_cast hnat_lt
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] at hreal_lt
        exact hreal_lt
      have hex_pos : ∃ i₀ : Fin l, 0 < w i₀ := by
        by_contra hall
        push Not at hall
        have hzero : ∀ i : Fin l, w i = 0 := fun i => le_antisymm (hall i) (hw0 i)
        have hsum0 : ∑ i : Fin l, w i = 0 := Finset.sum_eq_zero fun i _ => hzero i
        linarith
      obtain ⟨i₀, hi₀⟩ := hex_pos
      have hsum_lt : (sets.card : ℝ) * ((128 * (N * (Q - t)) + N * (2 * t - Q) : ℕ) : ℝ) <
          ∑ D ∈ sets, (128 * err D) := by
        have h1 : (sets.card : ℝ) * ((128 * (N * (Q - t)) + N * (2 * t - Q) : ℕ) : ℝ) =
            ∑ i : Fin l, w i * ((sets.card : ℝ) * ((128 * (N * (Q - t)) + N * (2 * t - Q) : ℕ) : ℝ)) := by
          rw [← Finset.sum_mul, hw1, one_mul]
        have h2 : ∑ D ∈ sets, (128 * err D) =
            ∑ i : Fin l, w i * (128 * ∑ D ∈ sets, (loss (table (C i)) D : ℝ)) := by
          rw [← Finset.mul_sum, hsum_err, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [h1, h2]
        exact Finset.sum_lt_sum
          (fun i _ => mul_le_mul_of_nonneg_left (le_of_lt (hstrict_i i)) (hw0 i))
          ⟨i₀, Finset.mem_univ i₀, mul_lt_mul_of_pos_left (hstrict_i i₀) hi₀⟩
      have hexD : ∃ D ∈ sets, ((128 * (N * (Q - t)) + N * (2 * t - Q) : ℕ) : ℝ) < 128 * err D := by
        by_contra hall
        push Not at hall
        have hle : ∑ D ∈ sets, (128 * err D) ≤
            (sets.card : ℝ) * ((128 * (N * (Q - t)) + N * (2 * t - Q) : ℕ) : ℝ) := by
          calc ∑ D ∈ sets, (128 * err D)
              ≤ ∑ _D ∈ sets, ((128 * (N * (Q - t)) + N * (2 * t - Q) : ℕ) : ℝ) :=
                Finset.sum_le_sum fun D hD => hall D hD
            _ = (sets.card : ℝ) * ((128 * (N * (Q - t)) + N * (2 * t - Q) : ℕ) : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        linarith
      obtain ⟨D, hD, hDlt⟩ := hexD
      refine ⟨D, hD, ?_, fun _ => hDlt⟩
      have hopt_eq : opt = N * (Q - t) := by dsimp only [opt]; rw [Nat.min_eq_right (by omega)]
      have hle_nat : 128 * opt ≤ 128 * (N * (Q - t)) + N * (2 * t - Q) := by rw [hopt_eq]; omega
      have hle_real : (128 : ℝ) * (opt : ℝ) ≤ ((128 * (N * (Q - t)) + N * (2 * t - Q) : ℕ) : ℝ) := by
        exact_mod_cast hle_nat
      linarith
    · have hge_i : ∀ i : Fin l, (sets.card : ℝ) * (opt : ℝ) ≤ ∑ D ∈ sets, (loss (table (C i)) D : ℝ) := by
        intro i
        have havg := (PEqualNP.Outside.L_meta_25879.loss_powersetCard_avg k a Γ hΓsub f g t
          (by rw [hΓcard]; exact ht) (table (C i))).1
        rw [hΓcard] at havg
        have hreal : ((sets.card * opt : ℕ) : ℝ) ≤ ((∑ D ∈ sets, loss (table (C i)) D : ℕ) : ℝ) := by
          exact_mod_cast havg
        push_cast at hreal
        exact hreal
      have hsum_ge : (sets.card : ℝ) * (opt : ℝ) ≤ ∑ D ∈ sets, err D := by
        calc (sets.card : ℝ) * (opt : ℝ)
            = ∑ i : Fin l, w i * ((sets.card : ℝ) * (opt : ℝ)) := by rw [← Finset.sum_mul, hw1, one_mul]
          _ ≤ ∑ i : Fin l, w i * ∑ D ∈ sets, (loss (table (C i)) D : ℝ) :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hge_i i) (hw0 i)
          _ = ∑ D ∈ sets, err D := hsum_err.symm
      have hexD : ∃ D ∈ sets, (opt : ℝ) ≤ err D := by
        by_contra hall
        push Not at hall
        have hlt : ∑ D ∈ sets, err D < (sets.card : ℝ) * (opt : ℝ) := by
          calc ∑ D ∈ sets, err D
              < ∑ _D ∈ sets, (opt : ℝ) := Finset.sum_lt_sum_of_nonempty hsets_ne fun D hD => hall D hD
            _ = (sets.card : ℝ) * (opt : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        linarith
      obtain ⟨D, hD, hDge⟩ := hexD
      exact ⟨D, hD, hDge, fun h => absurd h hQt⟩

