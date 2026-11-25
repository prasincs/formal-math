/-
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
import Statement
import OrbitStatement
import Bridge

/-!
# Border determinantal complexity

`MS.bridge_border`: the border determinantal complexity of the permanent over `ℂ` (limits of determinants of affine matrices) is superpolynomial.
-/

namespace MS

open MvPolynomial Filter PEqualNP.Gct

/-- A polynomial of degree at most one is affine. -/
theorem affine_eq {σ : Type} [Fintype σ] [DecidableEq σ] (p : MvPolynomial σ ℂ) (h : p.totalDegree ≤ 1) :
    p = ∑ t, C (p.coeff (Finsupp.single t 1)) * X t + C (p.coeff 0) := by
  refine MvPolynomial.ext _ _ fun s => ?_
  rw [coeff_add, coeff_sum, coeff_C]
  have hterm : ∀ t, (C (p.coeff (Finsupp.single t 1)) * X t : MvPolynomial σ ℂ).coeff s = if Finsupp.single t 1 = s then p.coeff (Finsupp.single t 1) else 0 := by
    intro t
    rw [coeff_C_mul, coeff_X']
    split_ifs <;> simp
  simp only [hterm]
  by_cases h0 : s = 0
  · subst h0
    rw [Finset.sum_eq_zero, zero_add, if_pos rfl]
    intro t _
    rw [if_neg]
    intro h1
    have := DFunLike.congr_fun h1 t
    simp at this
  · rw [if_neg (Ne.symm h0), add_zero]
    by_cases h1 : ∃ t, Finsupp.single t 1 = s
    · obtain ⟨t, rfl⟩ := h1
      rw [Finset.sum_eq_single t]
      · rw [if_pos rfl]
      · intro u _ hu
        rw [if_neg]
        intro h2
        exact hu (Finsupp.single_left_injective one_ne_zero h2)
      · intro hno; exact absurd (Finset.mem_univ t) hno
    · rw [Finset.sum_eq_zero (fun t _ => if_neg fun h2 => h1 ⟨t, h2⟩)]
      by_contra hne
      have hs : s ∈ p.support := mem_support_iff.2 hne
      have hdeg : (s.sum fun _ e => e) ≤ 1 := (le_totalDegree hs).trans h
      obtain ⟨t, ht⟩ := Finsupp.ne_iff.1 h0
      have ht' : s t ≠ 0 := by simpa using ht
      apply h1
      refine ⟨t, ?_⟩
      have hle : ∀ u, s u ≤ 1 := by
        intro u
        by_cases hu : u ∈ s.support
        · exact (Finset.single_le_sum (f := fun u => s u) (fun _ _ => Nat.zero_le _) hu).trans hdeg
        · rw [Finsupp.notMem_support_iff.1 hu]; exact Nat.zero_le 1
      ext u
      by_cases hut : t = u
      · subst hut
        rw [Finsupp.single_eq_same]
        have := hle t
        omega
      · rw [Finsupp.single_eq_of_ne' hut]
        by_contra hu0
        have hu : u ∈ s.support := Finsupp.mem_support_iff.2 (Ne.symm hu0)
        have htm : t ∈ s.support := Finsupp.mem_support_iff.2 ht'
        have h2 : s t + s u ≤ s.sum fun _ e => e := by
          rw [Finsupp.sum, ← Finset.sum_pair (f := fun v => s v) hut]
          exact Finset.sum_le_sum_of_subset (by
            intro v hv
            rcases Finset.mem_insert.1 hv with rfl | hv
            · exact htm
            · rw [Finset.mem_singleton.1 hv]; exact hu)
        have h3 : s u ≠ 0 := Ne.symm hu0
        omega

/-- Coefficients that are limits of values of polynomials are reached by power series. -/
theorem arc_general {σ κ : Type} [Finite κ] (U : MvPolynomial σ (MvPolynomial κ ℂ)) (PZ : MvPolynomial σ ℤ) (a : ℕ → κ → ℂ)
    (lim : ∀ s, Tendsto (fun t => eval (a t) (U.coeff s)) atTop (nhds ((PZ.coeff s : ℤ) : ℂ))) :
    ∃ (k : Type) (_ : Field k) (_ : CharZero k) (ψ : MvPolynomial κ ℂ →+* LaurentSeries k) (Q' : MvPolynomial σ (PowerSeries k)),
      map (HahnSeries.ofPowerSeries ℤ k) Q' = map ψ U ∧ map (PowerSeries.constantCoeff (R := k)) Q' = map (Int.castRingHom k) PZ := by
  classical
  obtain ⟨e, he⟩ := limit_hom (fun s : U.support => U.coeff s.1) a (fun s => ((PZ.coeff s.1 : ℤ) : ℂ)) fun s => lim s.1
  obtain ⟨k, ik, ck, ψ, hψ⟩ := arc (fun s : U.support => U.coeff s.1) (fun s => PZ.coeff s.1) e he
  have out : ∀ s, s ∉ U.support → PZ.coeff s = 0 := by
    intro s hs
    have hl := lim s
    simp only [notMem_support_iff.1 hs, map_zero] at hl
    have h1 : ((PZ.coeff s : ℤ) : ℂ) = 0 := tendsto_nhds_unique hl tendsto_const_nhds
    exact_mod_cast h1
  have hF : ∀ s, ∃ f : PowerSeries k, ψ (U.coeff s) = HahnSeries.ofPowerSeries ℤ k f ∧ PowerSeries.constantCoeff f = ((PZ.coeff s : ℤ) : k) := by
    intro s
    by_cases hs : s ∈ U.support
    · exact hψ ⟨s, hs⟩
    · exact ⟨0, by rw [notMem_support_iff.1 hs, map_zero, map_zero], by rw [out s hs]; simp⟩
  choose F hF1 hF2 using hF
  have hQ' : ∀ s, (∑ s ∈ U.support, monomial s (F s)).coeff s = if s ∈ U.support then F s else 0 := by
    intro s
    simp only [coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
  refine ⟨k, ik, ck, ψ, ∑ s ∈ U.support, monomial s (F s), ?_, ?_⟩
  · refine MvPolynomial.ext _ _ fun s => ?_
    rw [coeff_map, coeff_map, hQ']
    split_ifs with h
    · exact (hF1 s).symm
    · rw [map_zero, notMem_support_iff.1 h, map_zero]
  · refine MvPolynomial.ext _ _ fun s => ?_
    rw [coeff_map, hQ', coeff_map]
    split_ifs with h
    · exact hF2 s
    · rw [map_zero, out s h, map_zero]

/-- A cost bound and power series coefficients give an approximating circuit. -/
theorem approximates_of_cost {k : Type} [Field k] {V : Type} (f : MvPolynomial V k) (q' : MvPolynomial V (PowerSeries k)) (c : ℕ)
    (hcost : Cost (∅ : Set (MvPolynomial V (LaurentSeries k))) c {map (HahnSeries.ofPowerSeries ℤ k) q'})
    (hq2 : map (PowerSeries.constantCoeff (R := k)) q' = f) : Statement.Approximates f c := by
  refine ⟨map (HahnSeries.ofPowerSeries ℤ k) q', ?_, ?_⟩
  · obtain ⟨l, hl, _, hT, hlen⟩ := hcost [] Slp.nil (fun x hx => absurd hx (Set.notMem_empty x))
    obtain ⟨G', h1, h2⟩ := hl.seq
    obtain ⟨j, hj, hjq⟩ := h2 _ (hT _ rfl)
    have hlen' : l.length ≤ c := by simpa using hlen
    refine ⟨fun i => if i < l.length then G' i else C 0, fun i hi => ?_, j, by omega, by simp only [if_pos hj]; exact hjq⟩
    by_cases h : i < l.length
    · simp only [if_pos h]
      rcases h1 i h with h' | h' | ⟨x, hx, y, hy, h'⟩ | ⟨x, hx, y, hy, h'⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl ⟨x, hx, y, hy, by rw [if_pos (by omega), if_pos (by omega)]; exact h'⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨x, hx, y, hy, by rw [if_pos (by omega), if_pos (by omega)]; exact h'⟩))
    · simp only [if_neg h]
      exact Or.inr (Or.inl ⟨0, rfl⟩)
  · intro d i hi
    rw [coeff_map]
    have hcoe : ∀ f : PowerSeries k, HahnSeries.ofPowerSeries ℤ k f = (f : LaurentSeries k) := fun _ => rfl
    rw [hcoe, PowerSeries.coeff_coe]
    rcases lt_or_eq_of_le hi with h | rfl
    · rw [if_pos h, if_neg h.ne]
    · rw [if_neg (lt_irrefl _), if_pos rfl, ← hq2, coeff_map]
      simp

/-- The generic affine matrix. -/
noncomputable def affMat (σ : Type) [Fintype σ] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial σ (MvPolynomial ((Fin n × Fin n) × Option σ) ℂ)) :=
  Matrix.of fun i j => ∑ t, C (X ((i, j), some t)) * X t + C (X ((i, j), none))

theorem affMat_map {σ R : Type} [Fintype σ] [CommRing R] (n : ℕ) (E : MvPolynomial ((Fin n × Fin n) × Option σ) ℂ →+* R) :
    map E (affMat σ n).det = (Matrix.of fun i j => ∑ t, C (E (X ((i, j), some t))) * X t + C (E (X ((i, j), none))) : Matrix (Fin n) (Fin n) (MvPolynomial σ R)).det := by
  rw [RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, affMat, Matrix.of_apply, map_add, map_sum, map_mul, map_C, map_X]

theorem approximates_of_border {m n : ℕ} (h : HasBorderDetExpression (permPoly ℂ m) n) :
    ∃ (k : Type) (_ : Field k) (_ : CharZero k), Statement.Approximates (Statement.perm k m) (n * n * (4 * (m * m) + 4) + (4 + 40 * n ^ 4)) := by
  classical
  obtain ⟨q, hq, hlim⟩ := h
  choose A hA hdet using hq
  let a : ℕ → (Fin n × Fin n) × Option (Fin m × Fin m) → ℂ := fun l p =>
    match p.2 with
    | some t => (A l p.1.1 p.1.2).coeff (Finsupp.single t 1)
    | none => (A l p.1.1 p.1.2).coeff 0
  have hU : ∀ l, map (eval (a l)) (affMat (Fin m × Fin m) n).det = q l := by
    intro l
    rw [affMat_map, ← hdet l]
    congr 1
    refine Matrix.ext fun i j => ?_
    rw [Matrix.of_apply]
    conv_rhs => rw [affine_eq (A l i j) (hA l i j)]
    simp only [eval_X, a]
  have hPZ : map (Int.castRingHom ℂ) (permPoly ℤ m) = permPoly ℂ m := perm_map _ m
  obtain ⟨k, ik, ck, ψ, Q', h1, h2⟩ := arc_general (affMat (Fin m × Fin m) n).det (permPoly ℤ m) a (by
    intro s
    have h3 := hlim s
    rw [← hPZ, coeff_map] at h3
    have h4 : (fun l => eval (a l) ((affMat (Fin m × Fin m) n).det.coeff s)) = fun l => (q l).coeff s := by
      funext l
      rw [← coeff_map, hU]
    rw [h4]
    exact h3)
  refine ⟨k, ik, ck, approximates_of_cost _ Q' _ ?_ ?_⟩
  · rw [h1, affMat_map]
    have hc := cost_det_forms (V := Fin m × Fin m) (R := LaurentSeries k) (m := m * m) (n := n) (fun t => finProdFinEquiv.symm t)
      (Matrix.of fun i j => ∑ t, C (ψ (X ((i, j), some t))) * X t + C (ψ (X ((i, j), none))))
      (fun i j t => ψ (X ((i, j), some (finProdFinEquiv.symm t)))) (fun i j => ψ (X ((i, j), none))) (by
        intro i j
        rw [Matrix.of_apply]
        congr 1
        exact (Equiv.sum_comp finProdFinEquiv.symm fun t : Fin m × Fin m => C (ψ (X ((i, j), some t))) * (X t : MvPolynomial (Fin m × Fin m) (LaurentSeries k))).symm)
    exact hc
  · rw [h2, perm_map, permPoly_eq]

theorem approximates_mono {k : Type} [Field k] {V : Type} {f : MvPolynomial V k} {s t : ℕ} (hst : s ≤ t) (h : Statement.Approximates f s) : Statement.Approximates f t := by
  obtain ⟨q, ⟨l, hl, j, hj, hjq⟩, hc⟩ := h
  refine ⟨q, ⟨fun i => if i < s then l i else C 0, fun i hi => ?_, j, by omega, by simp only [if_pos hj]; exact hjq⟩, hc⟩
  by_cases h : i < s
  · simp only [if_pos h]
    rcases hl i h with h' | h' | ⟨x, hx, y, hy, h'⟩ | ⟨x, hx, y, hy, h'⟩
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl ⟨x, hx, y, hy, by rw [if_pos (by omega), if_pos (by omega)]; exact h'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x, hx, y, hy, by rw [if_pos (by omega), if_pos (by omega)]; exact h'⟩))
  · simp only [if_neg h]
    exact Or.inr (Or.inl ⟨0, rfl⟩)

/-- For every `d`, all large `m`: border determinantal expressions of the permanent have size more than `m ^ d`. -/
theorem bridge_border (h : Statement.MainTheoremApprox.{0}) (d : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ n, HasBorderDetExpression (permPoly ℂ m) n → m ^ d < n := by
  obtain ⟨m₀, h0⟩ := numerics h (d + 1) (by omega)
  refine ⟨max m₀ 1, fun m hm n hb => ?_⟩
  have hm0 : m₀ ≤ m := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  by_contra hn
  push Not at hn
  obtain ⟨k, ik, ck, hA⟩ := approximates_of_border hb
  refine (h0 m hm0).2 ⟨k, ik, ck, approximates_mono ?_ hA⟩
  have e1 : n ^ 4 ≤ (m ^ (d + 1)) ^ 4 := Nat.pow_le_pow_left (hn.trans (Nat.pow_le_pow_right hm1 (by omega))) 4
  have e2 : n * n * (m * m) ≤ (m ^ (d + 1)) ^ 4 := by
    have h1 : n * m ≤ m ^ (d + 1) := by rw [pow_succ]; exact Nat.mul_le_mul_right _ hn
    have h2 : 1 ≤ m ^ (d + 1) := Nat.one_le_pow _ _ hm1
    calc n * n * (m * m) = (n * m) ^ 2 := by ring
      _ ≤ (m ^ (d + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ (m ^ (d + 1)) ^ 4 := Nat.pow_le_pow_right h2 (by norm_num)
  have e3 : n * n ≤ (m ^ (d + 1)) ^ 4 := (Nat.le_mul_of_pos_right _ (Nat.mul_pos hm1 hm1)).trans e2
  have e4 : 49 * (m ^ (d + 1)) ^ 4 + 49 ≤ 49 * (m ^ (d + 1) + 1) ^ 4 := by
    have : (m ^ (d + 1)) ^ 4 + 1 ≤ (m ^ (d + 1) + 1) ^ 4 := by
      generalize m ^ (d + 1) = y
      have : (y + 1) ^ 4 = y ^ 4 + 1 + (4 * y ^ 3 + 6 * y ^ 2 + 4 * y) := by ring
      omega
    omega
  have e5 : n * n * (4 * (m * m) + 4) = 4 * (n * n * (m * m)) + 4 * (n * n) := by ring
  rw [e5]
  omega

end MS
