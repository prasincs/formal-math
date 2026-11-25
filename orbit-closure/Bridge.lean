/-
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
import Statement
import OrbitStatement

/-!
# From approximating circuits to orbit closures

`MS.bridge`: the bound for circuits that approximate the permanent (`Statement.MainTheoremApprox` of anthropics/formal-math,
`vp-vnp`) gives `PaddedPermanentNotMem`.

* `limit_hom`: a limit of points of a polynomial map gives an algebra map from its image algebra;
* `taylor`, `descend`, `extend`, `conj`, `arc`: the limit is reached by a Laurent series arc, over some field of characteristic zero;
* `cost_det`: a determinant of size `n` costs at most `40 n ^ 4 + 4` gates beyond its entries (Berkowitz);
* `approximates_of_mem`, `bridge`: undo the padding, count gates, compare.
-/

namespace MS

section P1


open MvPolynomial Filter

theorem limit_hom {ι D : Type} (Φ : D → MvPolynomial ι ℂ) (a : ℕ → ι → ℂ) (p : D → ℂ)
    (h : ∀ d, Tendsto (fun k => eval (a k) (Φ d)) atTop (nhds (p d))) :
    ∃ e : (aeval (R := ℂ) Φ).range →ₐ[ℂ] ℂ, ∀ d, e ⟨Φ d, X d, by simp⟩ = p d := by
  let q : MvPolynomial D ℂ →ₐ[ℂ] MvPolynomial ι ℂ := aeval Φ
  have hk : ∀ P ∈ RingHom.ker q, aeval p P = 0 := by
    intro P hP
    have h0 : ∀ k, eval (fun d => eval (a k) (Φ d)) P = 0 := by
      intro k
      have e1 : eval (fun d => eval (a k) (Φ d)) P = eval (a k) (q P) := by
        show _ = eval (a k) (aeval Φ P)
        rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
        change (aeval _) P = ((aeval (a k)).comp (aeval Φ)) P
        rw [comp_aeval]
        rfl
      rw [e1, (RingHom.mem_ker).1 hP, map_zero]
    have hc : Tendsto (fun k => eval (fun d => eval (a k) (Φ d)) P) atTop (nhds (eval p P)) :=
      ((MvPolynomial.continuous_eval P).tendsto p).comp (tendsto_pi_nhds.2 h)
    simp only [h0] at hc
    have := tendsto_nhds_unique hc tendsto_const_nhds
    rw [MvPolynomial.aeval_eq_eval]
    exact this
  let E := Ideal.quotientKerEquivRange q
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker q) (aeval p) hk).comp E.symm.toAlgHom, fun d => ?_⟩
  have : E (Ideal.Quotient.mk _ (X d)) = (⟨Φ d, X d, aeval_X Φ d⟩ : q.range) := by
    apply Subtype.ext
    exact aeval_X Φ d
  rw [← this]
  show (Ideal.Quotient.liftₐ (RingHom.ker q) (aeval p) hk) (E.symm (E _)) = _
  rw [AlgEquiv.symm_apply_apply]
  simp


end P1

section P3


section T

open PowerSeries

variable {k D : Type} [Field k] [CommRing D] [IsDomain D] [Algebra k D]

/-- `p` is the expansion of `x` in powers of `s`. -/
def Exp (s : D) (x : D) (p : PowerSeries k) : Prop :=
  ∀ n : ℕ, s ^ n ∣ x - Polynomial.aeval s (trunc n p)

theorem Exp.add {s x y : D} {p q : PowerSeries k} (h : Exp s x p) (h' : Exp s y q) : Exp s (x + y) (p + q) := by
  intro n
  have := dvd_add (h n) (h' n)
  rw [map_add, map_add]
  convert this using 1; ring

theorem Exp.mul {s x y : D} {p q : PowerSeries k} (h : Exp s x p) (h' : Exp s y q) : Exp s (x * y) (p * q) := by
  intro n
  have h1 : s ^ n ∣ x * y - Polynomial.aeval s (trunc n p * trunc n q) := by
    rw [map_mul]
    have : x * y - Polynomial.aeval s (trunc n p) * Polynomial.aeval s (trunc n q)
        = (x - Polynomial.aeval s (trunc n p)) * y + Polynomial.aeval s (trunc n p) * (y - Polynomial.aeval s (trunc n q)) := by ring
    rw [this]
    exact dvd_add ((h n).mul_right _) ((h' n).mul_left _)
  have h2 : s ^ n ∣ Polynomial.aeval s (trunc n p * trunc n q) - Polynomial.aeval s (trunc n (p * q)) := by
    rw [← map_sub]
    have hX : (Polynomial.X : Polynomial k) ^ n ∣ trunc n p * trunc n q - trunc n (p * q) := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      rw [Polynomial.coeff_sub, coeff_trunc, if_pos hd, Polynomial.coeff_mul, coeff_mul, sub_eq_zero]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha := Finset.HasAntidiagonal.mem_antidiagonal.1 ha
      rw [coeff_trunc, coeff_trunc, if_pos (by omega), if_pos (by omega)]
    obtain ⟨r, hr⟩ := hX
    rw [hr, map_mul, map_pow, Polynomial.aeval_X]
    exact dvd_mul_right _ _
  have := dvd_add h1 h2
  convert this using 1; ring

theorem Exp.const {s : D} (c : k) : Exp s (algebraMap k D c) (C c) := by
  intro n
  cases n with
  | zero => simp
  | succ n => rw [trunc_C]; simp

/-- Expansions are unique when `s` is not zero and constants are not divisible by `s`. -/
theorem Exp.unique {s x : D} (hs : s ≠ 0) (hk : ∀ c : k, s ∣ algebraMap k D c → c = 0) {p q : PowerSeries k}
    (h : Exp s x p) (h' : Exp s x q) : p = q := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h1 := dvd_sub (h' (n + 1)) (h (n + 1))
    have e : x - Polynomial.aeval s (trunc (n + 1) q) - (x - Polynomial.aeval s (trunc (n + 1) p))
        = Polynomial.aeval s (trunc (n + 1) p - trunc (n + 1) q) := by rw [map_sub]; ring
    have e2 : trunc (n + 1) p - trunc (n + 1) q = Polynomial.monomial n (coeff n p - coeff n q) := by
      ext d
      rw [Polynomial.coeff_sub, coeff_trunc, coeff_trunc, Polynomial.coeff_monomial]
      rcases lt_trichotomy d n with hd | rfl | hd
      · rw [if_pos (by omega), if_pos (by omega), ih d hd, sub_self]
        first | rw [Finsupp.single_apply, if_neg (by omega)] | rw [if_neg (by omega)]
      · simp
      · rw [if_neg (by omega), if_neg (by omega), sub_self]
        first | rw [Finsupp.single_apply, if_neg (by omega)] | rw [if_neg (by omega)]
    rw [e, e2, Polynomial.aeval_monomial, pow_succ, mul_comm (algebraMap k D _)] at h1
    exact sub_eq_zero.1 (hk _ ((mul_dvd_mul_iff_left (pow_ne_zero n hs)).1 h1))

/-- Every element has an expansion when every element is a constant modulo `s`. -/
theorem exists_exp {s : D} (hres : ∀ x : D, ∃ c : k, s ∣ x - algebraMap k D c) (x : D) : ∃ p : PowerSeries k, Exp s x p := by
  choose c hc using hres
  choose nx hnx using hc
  let it : ℕ → D := fun n => nx^[n] x
  refine ⟨PowerSeries.mk fun n => c (it n), fun n => ⟨it n, ?_⟩⟩
  induction n with
  | zero => simp [it]
  | succ n ih =>
    have h1 : it n = algebraMap k D (c (it n)) + s * it (n + 1) := by
      have := hnx (it n)
      simp only [it, Function.iterate_succ_apply'] at this ⊢
      rw [← this]; ring
    rw [trunc_succ, map_add, Polynomial.aeval_monomial, coeff_mk, ← sub_sub, ih]
    nth_rewrite 1 [h1]
    ring

/-- The Taylor map. -/
theorem taylor {s : D} (hs : s ≠ 0) (hk : ∀ c : k, s ∣ algebraMap k D c → c = 0)
    (hres : ∀ x : D, ∃ c : k, s ∣ x - algebraMap k D c) :
    ∃ φ : D →ₐ[k] PowerSeries k, ∀ x, Exp s x (φ x) := by
  choose f hf using exists_exp (k := k) hres
  have u : ∀ {x : D} {p : PowerSeries k}, Exp s x p → f x = p := fun h => Exp.unique hs hk (hf _) h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_, commutes' := ?_ }, hf⟩
  · simpa using u (Exp.const (s := s) (1 : k))
  · exact fun x y => u ((hf x).mul (hf y))
  · simpa using u (Exp.const (s := s) (0 : k))
  · exact fun x y => u ((hf x).add (hf y))
  · exact fun c => u (Exp.const c)

theorem taylor_const {s x : D} {p : PowerSeries k} (hk : ∀ c : k, s ∣ algebraMap k D c → c = 0) (h : Exp s x p) (hx : s ∣ x) :
    constantCoeff p = 0 := by
  have h1 := h 1
  rw [pow_one] at h1
  have e : trunc 1 p = Polynomial.C (constantCoeff p) := by
    ext d
    rw [coeff_trunc, Polynomial.coeff_C]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [if_neg (by omega), if_neg (by omega)]
  rw [e, Polynomial.aeval_C] at h1
  exact hk _ (by simpa using dvd_sub hx h1)

theorem taylor_inj {s x : D} (hD : ∀ x : D, (∀ n, s ^ n ∣ x) → x = 0) (h : Exp s x (0 : PowerSeries k)) : x = 0 :=
  hD x fun n => by simpa using h n

end T

open Polynomial

theorem series_of_dedekind {k O₀ : Type} [Field k] [CommRing O₀] [IsDomain O₀] [IsDedekindDomain O₀] (Q₀ : Ideal O₀) [hm : Q₀.IsMaximal]
    (hne : Q₀ ≠ ⊥) (c₀ : k →+* O₀) (res : ∀ y : O₀, ∃ c : k, y - c₀ c ∈ Q₀) :
    ∃ g : O₀ →+* PowerSeries k, Function.Injective g ∧ ∀ y ∈ Q₀, PowerSeries.constantCoeff (g y) = 0 := by
  classical
  have hp : Q₀.IsPrime := hm.isPrime
  let D := Localization.AtPrime Q₀
  have : IsDiscreteValuationRing D := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O₀ hne D
  let ia : Algebra k D := ((algebraMap O₀ D).comp c₀).toAlgebra
  have hcD : ∀ c : k, algebraMap k D c = algebraMap O₀ D (c₀ c) := fun _ => rfl
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible D
  have dvd_iff : ∀ x : D, s ∣ x ↔ x ∈ IsLocalRing.maximalIdeal D := by
    intro x
    rw [hs.maximalIdeal_eq, Ideal.mem_span_singleton]
  have hk : ∀ c : k, s ∣ algebraMap k D c → c = 0 := by
    intro c hc
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).1 ((dvd_iff _).1 hc) ((IsUnit.mk0 c h).map (algebraMap k D))
  have mem_iff : ∀ y : O₀, algebraMap O₀ D y ∈ IsLocalRing.maximalIdeal D ↔ y ∈ Q₀ := fun y =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff D Q₀ y
  have hres : ∀ x : D, ∃ c : k, s ∣ x - algebraMap k D c := by
    intro x
    obtain ⟨y, u, rfl⟩ := IsLocalization.exists_mk'_eq Q₀.primeCompl x
    obtain ⟨cy, hy⟩ := res y
    obtain ⟨cu, hu⟩ := res u
    have hcu : cu ≠ 0 := by
      rintro rfl
      rw [map_zero, sub_zero] at hu
      exact u.2 hu
    refine ⟨cy / cu, ?_⟩
    rw [dvd_iff]
    have hunit : IsUnit (algebraMap O₀ D u) := IsLocalization.map_units D u
    have e : (IsLocalization.mk' D y u - algebraMap k D (cy / cu)) * algebraMap O₀ D u
        = algebraMap O₀ D ((y - c₀ cy) - c₀ (cy / cu) * (u - c₀ cu)) := by
      have e1 : IsLocalization.mk' D y u * algebraMap O₀ D u = algebraMap O₀ D y := IsLocalization.mk'_spec D y u
      have e2 : c₀ (cy / cu) * c₀ cu = c₀ cy := by rw [← map_mul, div_mul_cancel₀ _ hcu]
      have e3 : (y - c₀ cy) - c₀ (cy / cu) * ((u : O₀) - c₀ cu) = y - c₀ (cy / cu) * u := by linear_combination e2
      rw [e3, map_sub, map_mul, ← hcD, ← e1, sub_mul]
    have h2 : (IsLocalization.mk' D y u - algebraMap k D (cy / cu)) * algebraMap O₀ D u ∈ IsLocalRing.maximalIdeal D := by
      rw [e, mem_iff]
      exact Q₀.sub_mem hy (Q₀.mul_mem_left _ hu)
    exact (Ideal.mul_unit_mem_iff_mem _ hunit).1 h2
  obtain ⟨φ, hφ⟩ := taylor hs.ne_zero hk hres
  have φinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun x hx => ?_
    have h := hφ x
    rw [hx] at h
    refine taylor_inj (k := k) (s := s) (fun z hz => ?_) h
    have : z ∈ (⨅ n : ℕ, IsLocalRing.maximalIdeal D ^ n) := by
      rw [Ideal.mem_iInf]
      intro n
      rw [hs.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hz n
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top', Ideal.mem_bot] at this
  have locinj : Function.Injective (algebraMap O₀ D) := IsLocalization.injective D Q₀.primeCompl_le_nonZeroDivisors
  exact ⟨(φ : D →+* PowerSeries k).comp (algebraMap O₀ D), φinj.comp locinj,
    fun y hy => taylor_const hk (hφ _) ((dvd_iff _).2 ((mem_iff y).2 hy))⟩

theorem descend {k K L : Type} [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [IsFractionRing k[X] K]
    [Field L] [Algebra K L] [Algebra k[X] L] [IsScalarTower k[X] K L] [Algebra.IsAlgebraic K L]
    (Q : Ideal (integralClosure k[X] L)) [Q.IsPrime] (hQ : algebraMap k[X] (integralClosure k[X] L) X ∈ Q)
    (a : Set L) (ha : a.Finite) :
    ∃ (L₀ : IntermediateField K L) (ψ : L₀ →+* LaurentSeries k), (∀ x ∈ a, x ∈ L₀) ∧
      ∀ x : L₀, ∀ y : integralClosure k[X] L, (y : L) = x → y ∈ Q →
        ∃ f : PowerSeries k, ψ x = HahnSeries.ofPowerSeries ℤ k f ∧ PowerSeries.constantCoeff f = 0 := by
  classical
  let L₀ := IntermediateField.adjoin K a
  have : Finite a := ha
  have fd : FiniteDimensional K L₀ := IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective k[X] K)
  have st : IsScalarTower k[X] L₀ L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply k[X] K L₀, IsScalarTower.algebraMap_apply k[X] K L, IsScalarTower.algebraMap_apply K L₀ L]
  let O₀ := integralClosure k[X] L₀
  have : IsDedekindDomain O₀ := integralClosure.isDedekindDomain k[X] K L₀
  have : IsFractionRing O₀ L₀ := integralClosure.isFractionRing_of_finite_extension K L₀
  let j : O₀ →ₐ[k[X]] integralClosure k[X] L := (IsScalarTower.toAlgHom k[X] L₀ L).mapIntegralClosure
  let Q₀ : Ideal O₀ := Q.comap j
  have hXQ : algebraMap k[X] O₀ X ∈ Q₀ := by
    show j (algebraMap k[X] O₀ X) ∈ Q
    rw [AlgHom.commutes]; exact hQ
  have injO : Function.Injective (algebraMap k[X] O₀) := by
    have h1 : Function.Injective (algebraMap k[X] L₀) := by
      rw [IsScalarTower.algebraMap_eq k[X] K L₀]
      exact (algebraMap K L₀).injective.comp (IsFractionRing.injective k[X] K)
    intro x y hxy
    exact h1 (by rw [IsScalarTower.algebraMap_apply k[X] O₀ L₀, hxy, ← IsScalarTower.algebraMap_apply])
  have hne : Q₀ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hXQ
    exact X_ne_zero (injO (hXQ.trans (map_zero _).symm))
  have hp : Q₀.IsPrime := Ideal.comap_isPrime j Q
  have hm : Q₀.IsMaximal := hp.isMaximal hne
  let c₀ : k →+* O₀ := (algebraMap k[X] O₀).comp C
  -- constants modulo Q₀
  have res : ∀ y : O₀, ∃ c : k, y - c₀ c ∈ Q₀ := by
    let _i : Field (O₀ ⧸ Q₀) := Ideal.Quotient.field Q₀
    let _j : Algebra k (O₀ ⧸ Q₀) := ((Ideal.Quotient.mk Q₀).comp c₀).toAlgebra
    have hint : Algebra.IsIntegral k (O₀ ⧸ Q₀) := ⟨fun z => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨p, hpm, hp0⟩ := (integralClosure.isIntegral (R := k[X]) (A := L₀) y)
      refine ⟨p.map (evalRingHom 0), hpm.map _, ?_⟩
      rw [eval₂_map]
      have : (algebraMap k (O₀ ⧸ Q₀)).comp (evalRingHom 0) = (Ideal.Quotient.mk Q₀).comp (algebraMap k[X] O₀) := by
        refine Polynomial.ringHom_ext ?_ ?_
        · intro r
          simp only [RingHom.comp_apply, coe_evalRingHom, eval_C]
          rfl
        · simp only [RingHom.comp_apply, coe_evalRingHom, eval_X, map_zero]
          exact (Ideal.Quotient.eq_zero_iff_mem.2 hXQ).symm
      rw [this]
      have h := congrArg (Ideal.Quotient.mk Q₀) hp0
      rw [map_zero, hom_eval₂] at h
      exact h⟩
    intro y
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := O₀ ⧸ Q₀)).2 (Ideal.Quotient.mk Q₀ y)
    exact ⟨c, Ideal.Quotient.eq.1 hc.symm⟩
  obtain ⟨g₁, g₁inj, g₁c⟩ := series_of_dedekind Q₀ hne c₀ res
  let g : O₀ →+* LaurentSeries k := (HahnSeries.ofPowerSeries ℤ k).comp g₁
  have ginj : Function.Injective g := HahnSeries.ofPowerSeries_injective.comp g₁inj
  refine ⟨L₀, IsFractionRing.lift ginj, fun x hx => IntermediateField.subset_adjoin K a hx, ?_⟩
  intro x y hxy hy
  have hxi : IsIntegral k[X] x := by
    have h1 : IsIntegral k[X] (algebraMap L₀ L x) := by
      have : algebraMap L₀ L x = (y : L) := hxy.symm
      rw [this]; exact y.2
    first | exact isIntegral_algebraMap_iff.1 h1 | exact (isIntegral_algebraMap_iff (algebraMap L₀ L).injective).1 h1
  let x₀ : O₀ := ⟨x, hxi⟩
  have hx₀ : x₀ ∈ Q₀ := by
    show j x₀ ∈ Q
    have : j x₀ = y := Subtype.ext hxy.symm
    rw [this]; exact hy
  refine ⟨g₁ x₀, ?_, ?_⟩
  · have : x = algebraMap O₀ L₀ x₀ := rfl
    rw [this, IsFractionRing.lift_algebraMap]
    rfl
  · exact g₁c x₀ hx₀

section E

open TensorProduct

theorem point_of_maximal {F S κ L : Type} [Field F] [CommRing S] [Algebra F S] [Algebra.FiniteType F S] [Field κ] [Algebra F κ]
    [Field L] [Algebra F L] [IsAlgClosed L] (q : S →ₐ[F] κ) (hq : Function.Surjective q) : Nonempty (S →ₐ[F] L) := by
  have ft : Algebra.FiniteType F κ := Algebra.FiniteType.of_surjective q hq
  have fin : Module.Finite F κ := finite_of_finite_type_of_isJacobsonRing F κ
  exact ⟨(IsAlgClosed.lift : κ →ₐ[F] L).comp q⟩

theorem exists_point {F S L : Type} [Field F] [CommRing S] [Nontrivial S] [Algebra F S] [Algebra.FiniteType F S]
    [Field L] [Algebra F L] [IsAlgClosed L] : Nonempty (S →ₐ[F] L) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  let iκ : Field (S ⧸ m) := Ideal.Quotient.field m
  exact point_of_maximal (κ := S ⧸ m) (Ideal.Quotient.mkₐ F m) (Ideal.Quotient.mkₐ_surjective F m)

/-- A map to an algebraically closed field extends to a finitely generated domain. -/
theorem extend {B A L : Type} [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A]
    [Field L] [IsAlgClosed L] (hBA : Function.Injective (algebraMap B A)) (l : B →+* L) (hl : Function.Injective l) :
    ∃ ψ : A →+* L, ∀ b, ψ (algebraMap B A b) = l b := by
  classical
  let F := FractionRing B
  let iL : Algebra F L := (IsFractionRing.lift hl : F →+* L).toAlgebra
  have hF : ∀ b : B, algebraMap F L (algebraMap B F b) = l b := fun b => IsFractionRing.lift_algebraMap hl b
  let S := F ⊗[B] A
  have nt : Nontrivial S := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := F) (Algebra.linearMap B A) hBA
    have h2 : Function.Injective fun x : F => x ⊗ₜ[B] (1 : A) := by
      intro x y hxy
      have e : ∀ z : F, (Algebra.linearMap B A).lTensor F (z ⊗ₜ[B] (1 : B)) = z ⊗ₜ[B] (1 : A) := by
        intro z; simp
      have h3 := h ((e x).trans (hxy.trans (e y).symm))
      simpa using congrArg (TensorProduct.rid B F) h3
    exact h2.nontrivial
  obtain ⟨f⟩ := exists_point (F := F) (S := S) (L := L)
  refine ⟨(f : S →+* L).comp (Algebra.TensorProduct.includeRight : A →ₐ[B] S).toRingHom, fun b => ?_⟩
  have e : (Algebra.TensorProduct.includeRight : A →ₐ[B] S) (algebraMap B A b) = algebraMap F S (algebraMap B F b) := by
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  show f ((Algebra.TensorProduct.includeRight : A →ₐ[B] S) (algebraMap B A b)) = l b
  rw [e, ← hF b]
  exact f.commutes (algebraMap B F b)

/-- Among the extensions of `l` to a finite extension `B`, one sends a given prime above into `Q`. -/
theorem conj {R B L V : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] [CommRing B] [IsDomain B] [Algebra R B]
    [Module.Finite R B] (hRB : Function.Injective (algebraMap R B)) [Field L] [IsAlgClosed L] (l : R →+* L)
    (hl : Function.Injective l) [CommRing V] (v : V →+* L) (hv : Function.Injective v)
    (hV : ∀ x : L, l.IsIntegralElem x → ∃ y, v y = x) (Q : Ideal V) [Q.IsPrime] (p : Ideal B) [p.IsPrime]
    (hp : ∀ r : R, algebraMap R B r ∈ p ↔ ∃ y ∈ Q, v y = l r) :
    ∃ f : B →+* L, (∀ r, f (algebraMap R B r) = l r) ∧ ∀ b ∈ p, ∃ y ∈ Q, v y = f b := by
  classical
  let E := FractionRing R
  let Ω := AlgebraicClosure E
  have hRΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R E Ω]
    exact (algebraMap E Ω).injective.comp (IsFractionRing.injective R E)
  obtain ⟨i, hi⟩ := extend (B := R) (A := B) (L := Ω) hRB (algebraMap R Ω) hRΩ
  -- a finite Galois extension containing the image of B
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule R B).FG)
  let K₁ : IntermediateField E Ω := IntermediateField.adjoin E (i '' (S : Set B))
  have fS : Finite (i '' (S : Set B)) := (S.finite_toSet.image i)
  have fd1 : FiniteDimensional E K₁ := IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let N : IntermediateField E Ω := IntermediateField.normalClosure E K₁ Ω
  have hKN : K₁ ≤ N := IntermediateField.le_normalClosure K₁
  have himg : ∀ b : B, i b ∈ N := by
    intro b
    have hb : b ∈ Submodule.span R (S : Set B) := by rw [hS]; trivial
    induction hb using Submodule.span_induction with
    | mem x hx => exact hKN (IntermediateField.subset_adjoin E _ ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact N.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact N.add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul, hi, IsScalarTower.algebraMap_apply R E Ω]
      exact N.mul_mem (N.algebraMap_mem _) hx
  have : CharZero E := charZero_of_injective_algebraMap (IsFractionRing.injective R E)
  have gal : IsGalois E N := IsGalois.mk
  have st : IsScalarTower R E N := inferInstance
  have st2 : IsScalarTower R N Ω := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R E N, IsScalarTower.algebraMap_apply R E Ω, IsScalarTower.algebraMap_apply E N Ω]
  let C := integralClosure R N
  have int : ∀ b : B, IsIntegral R (⟨i b, himg b⟩ : N) := by
    intro b
    obtain ⟨q, hq, hq0⟩ := Algebra.IsIntegral.isIntegral (R := R) b
    refine ⟨q, hq, ?_⟩
    apply Subtype.ext
    have e : (algebraMap N Ω) (Polynomial.eval₂ (algebraMap R N) ⟨i b, himg b⟩ q) = Polynomial.eval₂ (i.comp (algebraMap R B)) (i b) q := by
      rw [Polynomial.hom_eval₂]
      have : (algebraMap N Ω).comp (algebraMap R N) = i.comp (algebraMap R B) := by
        ext r
        simp only [RingHom.comp_apply, hi]
        exact (IsScalarTower.algebraMap_apply R N Ω r).symm
      rw [this]; rfl
    refine e.trans ?_
    rw [← Polynomial.hom_eval₂, hq0, map_zero]; rfl
  let iC : B →+* C :=
    { toFun := fun b => ⟨⟨i b, himg b⟩, int b⟩
      map_one' := by ext; simp
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp
      map_mul' := fun x y => by ext; simp }
  have iCr : ∀ r, iC (algebraMap R B r) = algebraMap R C r := by
    intro r; apply Subtype.ext; apply Subtype.ext
    show i (algebraMap R B r) = _
    rw [hi]; rfl
  have injC : Function.Injective iC := by
    have hk : RingHom.ker i = ⊥ := by
      refine Ideal.eq_bot_of_comap_eq_bot (R := R) ?_
      rw [eq_bot_iff]
      intro r hr
      have h0 : i (algebraMap R B r) = 0 := hr
      rw [hi] at h0
      exact hRΩ (h0.trans (map_zero _).symm)
    intro x y hxy
    have h1 : i x = i y := congrArg (fun c : C => ((c : N) : Ω)) hxy
    exact (RingHom.injective_iff_ker_eq_bot i).2 hk h1
  have fr : IsFractionRing C N := integralClosure.isFractionRing_of_finite_extension E N
  let G := C ≃ₐ[R] C
  have finG : Finite G := Finite.of_equiv _ (galRestrict R E N C).toEquiv
  have inv : Algebra.IsInvariant R C G := Algebra.isInvariant_of_isGalois' R E N C
  -- the map to L
  let iL : Algebra E L := (IsFractionRing.lift hl : E →+* L).toAlgebra
  have hE : ∀ r : R, algebraMap E L (algebraMap R E r) = l r := fun r => IsFractionRing.lift_algebraMap hl r
  let μ : N →ₐ[E] L := IsAlgClosed.lift
  let μC : C →+* L := (μ : N →+* L).comp (algebraMap C N)
  have μr : ∀ r : R, μC (algebraMap R C r) = l r := by
    intro r
    show μ (algebraMap C N (algebraMap R C r)) = l r
    rw [← IsScalarTower.algebraMap_apply R C N, IsScalarTower.algebraMap_apply R E N, AlgHom.commutes, hE]
  have μint : ∀ c : C, ∃ y, v y = μC c := by
    intro c
    refine hV _ ?_
    obtain ⟨q, hq, hq0⟩ := integralClosure.isIntegral (R := R) (A := N) c
    refine ⟨q, hq, ?_⟩
    have : l = μC.comp (algebraMap R C) := by ext r; exact (μr r).symm
    rw [this, ← Polynomial.hom_eval₂, hq0, map_zero]
  let vE : V ≃+* v.range := RingEquiv.ofBijective v.rangeRestrict ⟨fun a b h => hv (congrArg Subtype.val h), v.rangeRestrict_surjective⟩
  let ρ : C →+* V := (vE.symm : v.range →+* V).comp (μC.codRestrict v.range fun c => μint c)
  have hρ : ∀ c, v (ρ c) = μC c := by
    intro c
    have : vE (ρ c) = ⟨μC c, μint c⟩ := vE.apply_symm_apply _
    exact congrArg Subtype.val this
  let P' : Ideal C := Q.comap ρ
  have hP' : P'.IsPrime := Ideal.comap_isPrime ρ Q
  let aBC : Algebra B C := iC.toAlgebra
  have stBC : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r => (iCr r).symm
  have intBC : Algebra.IsIntegral B C := ⟨fun c => (integralClosure.isIntegral (R := R) (A := N) c).tower_top⟩
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (R := B) (S := C) p
    (by
      have hk : RingHom.ker (algebraMap B C) = ⊥ := (RingHom.injective_iff_ker_eq_bot (algebraMap B C)).1 injC
      rw [hk]; exact bot_le)
  have under : P.under R = P'.under R := by
    ext r
    have h1 : r ∈ P.under R ↔ algebraMap R B r ∈ p := by
      rw [← hPp]
      show algebraMap R C r ∈ P ↔ algebraMap B C (algebraMap R B r) ∈ P
      rw [← IsScalarTower.algebraMap_apply R B C]
    rw [h1, hp]
    show _ ↔ ρ (algebraMap R C r) ∈ Q
    have h2 : v (ρ (algebraMap R C r)) = l r := by rw [hρ, μr]
    constructor
    · rintro ⟨y, hy, hyr⟩
      have : y = ρ (algebraMap R C r) := hv (hyr.trans h2.symm)
      rwa [← this]
    · exact fun h => ⟨_, h, h2⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R C G P P' under
  refine ⟨μC.comp ((g : C →+* C).comp iC), fun r => ?_, fun b hb => ?_⟩
  · show μC (g (iC (algebraMap R B r))) = l r
    rw [iCr, AlgEquiv.commutes, μr]
  · have hbP : iC b ∈ P := by
      have : b ∈ P.under B := by
        first
          | (rw [hPp]; exact hb)
          | (show b ∈ P.comap (algebraMap B C); rw [hPp]; exact hb)
      exact this
    have h3 : g (iC b) ∈ P' := by
      have h4 := Ideal.smul_mem_pointwise_smul g (iC b) P hbP
      rw [← hg] at h4
      exact h4
    exact ⟨ρ (g (iC b)), h3, hρ _⟩

end E

section Arc

open Polynomial

/-- A generic line through `π`. -/
theorem line {s : ℕ} {k : Type} [Field k] [Algebra ℂ k] (j : MvPolynomial (Fin s) ℂ →ₐ[ℂ] k) (hj : Function.Injective j) (π : Fin s → ℂ) :
    ∃ ℓ : MvPolynomial (Fin s) ℂ →ₐ[ℂ] k[X], Function.Injective ℓ ∧ ∀ x, eval 0 (ℓ x) = algebraMap ℂ k (MvPolynomial.aeval π x) := by
  let sh : MvPolynomial (Fin s) ℂ →ₐ[ℂ] MvPolynomial (Fin s) ℂ := MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (π i)
  let sh' : MvPolynomial (Fin s) ℂ →ₐ[ℂ] MvPolynomial (Fin s) ℂ := MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (π i)
  have shX : ∀ i, sh (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C (π i) := fun i => MvPolynomial.aeval_X _ i
  have shX' : ∀ i, sh' (MvPolynomial.X i) = MvPolynomial.X i - MvPolynomial.C (π i) := fun i => MvPolynomial.aeval_X _ i
  have shC' : ∀ c, sh' (MvPolynomial.C c) = MvPolynomial.C c := fun c => sh'.commutes c
  have hsh : sh'.comp sh = AlgHom.id ℂ _ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, shX, map_add, shX', shC', sub_add_cancel, AlgHom.id_apply]
  have shinj : Function.Injective sh := by
    intro x y hxy
    have h1 := DFunLike.congr_fun hsh x
    have h2 := DFunLike.congr_fun hsh y
    rw [AlgHom.comp_apply, AlgHom.id_apply] at h1 h2
    rw [← h1, ← h2, hxy]
  let ℓ : MvPolynomial (Fin s) ℂ →ₐ[ℂ] k[X] := MvPolynomial.aeval fun i => C (algebraMap ℂ k (π i)) + X * C (j (MvPolynomial.X i))
  have ℓX : ∀ i, ℓ (MvPolynomial.X i) = C (algebraMap ℂ k (π i)) + X * C (j (MvPolynomial.X i)) := fun i => MvPolynomial.aeval_X _ i
  let E : k → (k[X] →ₐ[ℂ] k) := fun c => (Polynomial.aeval (R := k) c).restrictScalars ℂ
  have hE : ∀ c x, E c x = eval c x := fun c x => Polynomial.coe_aeval_eq_eval c ▸ rfl
  refine ⟨ℓ, ?_, ?_⟩
  · have h : (E 1).comp ℓ = j.comp sh := by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, ℓX, shX, hE, map_add, eval_add, eval_mul, eval_C, eval_X, eval_C, one_mul, add_comm]
      congr 1
      exact (j.commutes (π i)).symm
    intro x y hxy
    refine shinj (hj ?_)
    have h1 := DFunLike.congr_fun h x
    have h2 := DFunLike.congr_fun h y
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at h1 h2
    rw [← h1, ← h2, hxy]
  · intro x
    have h : (E 0).comp ℓ = (Algebra.ofId ℂ k).comp (MvPolynomial.aeval π) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, ℓX, hE, MvPolynomial.aeval_X, eval_add, eval_mul, eval_C, eval_X, zero_mul, add_zero, Algebra.ofId_apply]
    have h1 := DFunLike.congr_fun h x
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hE, Algebra.ofId_apply] at h1
    exact h1

set_option maxHeartbeats 1000000 in
/-- Arc lemma: a point of the closure with integer coordinates is reached by a Laurent arc over some field of characteristic zero. -/
theorem arc {ι D : Type} [Finite ι] [Finite D] (Φ : D → MvPolynomial ι ℂ) (z : D → ℤ)
    (e : (MvPolynomial.aeval (R := ℂ) Φ).range →ₐ[ℂ] ℂ) (he : ∀ d, e ⟨Φ d, MvPolynomial.X d, by simp⟩ = z d) :
    ∃ (k : Type) (_ : Field k) (_ : CharZero k) (ψ : MvPolynomial ι ℂ →+* LaurentSeries k),
      ∀ d, ∃ f : PowerSeries k, ψ (Φ d) = HahnSeries.ofPowerSeries ℤ k f ∧ PowerSeries.constantCoeff f = z d := by
  classical
  let A := MvPolynomial ι ℂ
  let B := (MvPolynomial.aeval (R := ℂ) Φ).range
  have ftB : Algebra.FiniteType ℂ B :=
    Algebra.FiniteType.of_surjective (MvPolynomial.aeval (R := ℂ) Φ).rangeRestrict (MvPolynomial.aeval (R := ℂ) Φ).rangeRestrict_surjective
  obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg ℂ B
  let R := MvPolynomial (Fin s) ℂ
  let aRB : Algebra R B := g.toRingHom.toAlgebra
  have mf : Module.Finite R B := gfin
  let k := AlgebraicClosure (FractionRing R)
  let π : Fin s → ℂ := fun i => e (g (MvPolynomial.X i))
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap ℂ k).injective
  have injRk : Function.Injective (algebraMap R k) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) k]
    exact (algebraMap (FractionRing R) k).injective.comp (IsFractionRing.injective R (FractionRing R))
  obtain ⟨ℓ, ℓinj, hev⟩ := line (IsScalarTower.toAlgHom ℂ R k) injRk π
  have hev0 : ∀ x : R, eval 0 (ℓ x) = algebraMap ℂ k (e (g x)) := by
    intro x
    have h : MvPolynomial.aeval π = e.comp g := MvPolynomial.algHom_ext fun i => by
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rw [hev, h, AlgHom.comp_apply]
  let K := RatFunc k
  let L := AlgebraicClosure K
  have injXL : Function.Injective (algebraMap k[X] L) := by
    rw [IsScalarTower.algebraMap_eq k[X] K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective k[X] K)
  let l : R →+* L := (algebraMap k[X] L).comp (ℓ : R →+* k[X])
  have linj : Function.Injective l := injXL.comp ℓinj
  let V := integralClosure k[X] L
  let v : V →+* L := V.val.toRingHom
  have hv : Function.Injective v := Subtype.val_injective
  have hV : ∀ x : L, l.IsIntegralElem x → ∃ y, v y = x := by
    rintro x ⟨q, hq, hq0⟩
    refine ⟨⟨x, q.map (ℓ : R →+* k[X]), hq.map _, ?_⟩, rfl⟩
    rw [eval₂_map]; exact hq0
  have injXV : Function.Injective (algebraMap k[X] V) := by
    intro x y hxy
    exact injXL (congrArg (fun c : V => (c : L)) hxy)
  have pX : (Ideal.span {(X : k[X])}).IsPrime := (Ideal.span_singleton_prime X_ne_zero).2 prime_X
  obtain ⟨Q, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (R := k[X]) (S := V) (Ideal.span {X})
    (by
      have hk : RingHom.ker (algebraMap k[X] V) = ⊥ := (RingHom.injective_iff_ker_eq_bot (algebraMap k[X] V)).1 injXV
      rw [hk]; exact bot_le)
  have memQ : ∀ x : k[X], algebraMap k[X] V x ∈ Q ↔ eval 0 x = 0 := by
    intro x
    have h1 : algebraMap k[X] V x ∈ Q ↔ x ∈ Ideal.span {(X : k[X])} := by rw [← hQ]; rfl
    rw [h1, Ideal.mem_span_singleton, X_dvd_iff, coeff_zero_eq_eval_zero]
  let p : Ideal B := RingHom.ker e
  have hpp : p.IsPrime := RingHom.ker_isPrime e
  have hp : ∀ r : R, algebraMap R B r ∈ p ↔ ∃ y ∈ Q, v y = l r := by
    intro r
    have h1 : algebraMap R B r ∈ p ↔ algebraMap k[X] V (ℓ r) ∈ Q := by
      rw [memQ, hev0]
      show e (g r) = 0 ↔ _
      rw [map_eq_zero_iff _ (algebraMap ℂ k).injective]
    rw [h1]
    constructor
    · exact fun h => ⟨_, h, rfl⟩
    · rintro ⟨y, hy, hyr⟩
      have : y = algebraMap k[X] V (ℓ r) := hv hyr
      rwa [← this]
  obtain ⟨f, hf, hfQ⟩ := conj (R := R) (B := B) (L := L) (V := V) ginj l linj v hv hV Q p hp
  have finj : Function.Injective f := by
    refine (RingHom.injective_iff_ker_eq_bot f).2 (Ideal.eq_bot_of_comap_eq_bot (R := R) ?_)
    rw [eq_bot_iff]
    intro r hr
    have h0 : f (algebraMap R B r) = 0 := hr
    rw [hf] at h0
    exact linj (h0.trans (map_zero _).symm)
  have ftA : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A
  obtain ⟨ψ₁, hψ₁⟩ := extend (B := B) (A := A) (L := L) Subtype.val_injective f finj
  obtain ⟨L₀, ψ₂, hL₀, hψ₂⟩ := descend (k := k) (K := K) (L := L) Q ((memQ X).2 (by simp)) (Set.range fun i => ψ₁ (MvPolynomial.X i)) (Set.finite_range _)
  have hC : ∀ c : ℂ, ψ₁ (MvPolynomial.C c) = algebraMap K L (algebraMap k[X] K (C (algebraMap ℂ k c))) := by
    intro c
    have h1 : (MvPolynomial.C c : A) = algebraMap B A (algebraMap R B (MvPolynomial.C c)) := by
      have : algebraMap R B (MvPolynomial.C c) = algebraMap ℂ B c := g.commutes c
      rw [this]; rfl
    rw [h1, hψ₁, hf]
    show algebraMap k[X] L (ℓ (MvPolynomial.C c)) = _
    rw [← IsScalarTower.algebraMap_apply k[X] K L]
    congr 1
    exact ℓ.commutes c
  have mem : ∀ x : A, ψ₁ x ∈ L₀ := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C c => rw [hC]; exact L₀.algebraMap_mem _
    | add x y hx hy => rw [map_add]; exact L₀.add_mem hx hy
    | mul_X x i hx => rw [map_mul]; exact L₀.mul_mem hx (hL₀ _ ⟨i, rfl⟩)
  let ψ₃ : A →+* L₀ := ψ₁.codRestrict L₀ mem
  refine ⟨k, inferInstance, inferInstance, ψ₂.comp ψ₃, fun d => ?_⟩
  let b : B := ⟨Φ d, MvPolynomial.X d, by simp⟩
  have hb : b - (z d : B) ∈ p := by
    show e (b - (z d : B)) = 0
    rw [map_sub, map_intCast, he, sub_self]
  obtain ⟨y, hyQ, hy⟩ := hfQ _ hb
  have hΦ : ψ₁ (Φ d) = f b := hψ₁ b
  obtain ⟨q, hq, hq0⟩ := hψ₂ (ψ₃ (Φ d) - (z d : L₀)) y (by
    show v y = ψ₁ (Φ d) - _
    rw [hy, map_sub, map_intCast, hΦ]
    simp) hyQ
  refine ⟨q + (z d : PowerSeries k), ?_, ?_⟩
  · have e1 : ψ₂ (ψ₃ (Φ d) - (z d : L₀)) = ψ₂ (ψ₃ (Φ d)) - (z d : LaurentSeries k) :=
      (RingHom.map_sub ψ₂ _ _).trans (congrArg (fun c => ψ₂ (ψ₃ (Φ d)) - c) (map_intCast ψ₂ (z d)))
    have e2 : HahnSeries.ofPowerSeries ℤ k (q + (z d : PowerSeries k)) = HahnSeries.ofPowerSeries ℤ k q + (z d : LaurentSeries k) :=
      (RingHom.map_add _ _ _).trans (congrArg (fun c => HahnSeries.ofPowerSeries ℤ k q + c) (map_intCast (HahnSeries.ofPowerSeries ℤ k) (z d)))
    have e3 : ψ₂ (ψ₃ (Φ d)) = HahnSeries.ofPowerSeries ℤ k q + (z d : LaurentSeries k) := sub_eq_iff_eq_add.1 (e1.symm.trans hq)
    exact e3.trans e2.symm
  · have e4 : PowerSeries.constantCoeff ((z d : PowerSeries k)) = (z d : k) := map_intCast (PowerSeries.constantCoeff (R := k)) (z d)
    exact (RingHom.map_add _ _ _).trans (by rw [hq0, e4, zero_add])

end Arc


end P3

section P4


open Matrix Polynomial

section Border

variable {S : Type} [CommRing S] [Nontrivial S] {n : ℕ}

/-- `w k = Σ_{j>k} c_j N^(j-k-1)`, by Horner from above: `hw d` is `w (n - d)`. -/
def hw (N : Matrix (Fin n) (Fin n) S) (c : ℕ → S) : ℕ → Matrix (Fin n) (Fin n) S
  | 0 => 0
  | d + 1 => N * hw N c d + (c (n - d)) • (1 : Matrix (Fin n) (Fin n) S)

theorem hw_eq (N : Matrix (Fin n) (Fin n) S) (c : ℕ → S) :
    ∀ d, d ≤ n + 1 → hw N c d = ∑ j ∈ Finset.range d, c (n + 1 - d + j) • N ^ j := by
  intro d
  induction d with
  | zero => intro _; simp [hw]
  | succ d ih =>
    intro hd
    rw [hw, ih (by omega), Finset.sum_range_succ', pow_zero, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mul_smul, ← pow_succ']
      congr 2
      omega
    · congr 2
      omega

/-- Cayley-Hamilton in Horner form. -/
theorem hw_top (N : Matrix (Fin n) (Fin n) S) : hw N (fun j => N.charpoly.coeff j) (n + 1) = 0 := by
  rw [hw_eq N _ (n + 1) le_rfl]
  have h := Matrix.aeval_self_charpoly N
  rw [Polynomial.aeval_eq_sum_range' (n := n + 1) (by rw [Matrix.charpoly_natDegree_eq_dim]; simp)] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  omega

/-- The candidate for the adjugate of the characteristic matrix. -/
noncomputable def W (N : Matrix (Fin n) (Fin n) S) : Matrix (Fin n) (Fin n) S[X] :=
  ∑ k ∈ Finset.range n, (X : S[X]) ^ k • (hw N (fun j => N.charpoly.coeff j) (n - k)).map C

theorem charmatrix_mul_W (N : Matrix (Fin n) (Fin n) S) : N.charmatrix * W N = N.charpoly • (1 : Matrix (Fin n) (Fin n) S[X]) := by
  set c : ℕ → S := fun j => N.charpoly.coeff j with hc
  have hmap : ∀ M : Matrix (Fin n) (Fin n) S, N.charmatrix * M.map C = (X : S[X]) • M.map C - (N * M).map C := by
    intro M
    rw [Matrix.charmatrix, sub_mul]
    congr 1
    · ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_mul]
    · rw [RingHom.mapMatrix_apply]
      exact (Matrix.map_mul (f := (C : S →+* S[X]))).symm
  have step : ∀ k ∈ Finset.range n, N.charmatrix * ((X : S[X]) ^ k • (hw N c (n - k)).map C)
      = ((X : S[X]) ^ (k + 1) • (hw N c (n - (k + 1) + 1)).map C - (X : S[X]) ^ k • (hw N c (n - k + 1)).map C)
        + (X : S[X]) ^ k • (c k • (1 : Matrix (Fin n) (Fin n) S)).map C := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have e1 : n - (k + 1) + 1 = n - k := by omega
    have e2 : hw N c (n - k + 1) = N * hw N c (n - k) + c k • 1 := by
      rw [hw]; congr 2; congr 1; omega
    have e3 : (hw N c (n - k + 1)).map C = (N * hw N c (n - k)).map C + (c k • (1 : Matrix (Fin n) (Fin n) S)).map C := by
      rw [e2]; exact Matrix.map_add _ (fun a b => map_add C a b) _ _
    rw [Matrix.mul_smul, hmap, e1, e3, smul_sub, smul_smul, ← pow_succ, smul_add]
    abel
  rw [W, Finset.mul_sum, Finset.sum_congr rfl step, Finset.sum_add_distrib, Finset.sum_range_sub (fun k => (X : S[X]) ^ k • (hw N c (n - k + 1)).map C)]
  have h0 : hw N c (n - 0 + 1) = 0 := hw_top N
  have hn : hw N c (n - n + 1) = c n • 1 := by simp [hw]
  rw [h0, hn]
  have hz : (0 : Matrix (Fin n) (Fin n) S).map C = (0 : Matrix (Fin n) (Fin n) S[X]) := by ext i j; simp
  rw [hz, smul_zero, sub_zero, add_comm, ← Finset.sum_range_succ (fun k => (X : S[X]) ^ k • (c k • (1 : Matrix (Fin n) (Fin n) S)).map C)]
  have hsum := Polynomial.as_sum_range' N.charpoly (n + 1) (by rw [Matrix.charpoly_natDegree_eq_dim]; simp)
  conv_rhs => rw [hsum]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← C_mul_X_pow_eq_monomial, mul_comm]
  · simp [hij]

theorem adjugate_charmatrix (N : Matrix (Fin n) (Fin n) S) : N.charmatrix.adjugate = W N := by
  have h1 : N.charpoly • N.charmatrix.adjugate = N.charpoly • W N := by
    calc N.charpoly • N.charmatrix.adjugate = N.charmatrix.adjugate * (N.charpoly • (1 : Matrix (Fin n) (Fin n) S[X])) := by
          rw [Matrix.mul_smul, mul_one]
      _ = N.charmatrix.adjugate * (N.charmatrix * W N) := by rw [charmatrix_mul_W]
      _ = N.charpoly • W N := by
          rw [← mul_assoc, Matrix.adjugate_mul, smul_mul_assoc, one_mul]; rfl
  refine Matrix.ext fun i j => ?_
  have h2 := congrFun (congrFun h1 i) j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at h2
  exact (Matrix.charpoly_monic N).isRegular.left h2

end Border

/-- Expansion along a border, when the corner determinant can be cancelled. -/
theorem det_border {T : Type} [CommRing T] {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) T)
    (hreg : IsRegular (M.submatrix Fin.succ Fin.succ).det) :
    M.det = M 0 0 * (M.submatrix Fin.succ Fin.succ).det
      - ∑ i, M 0 (Fin.succ i) * ∑ j, (M.submatrix Fin.succ Fin.succ).adjugate i j * M (Fin.succ j) 0 := by
  set D := M.submatrix Fin.succ Fin.succ with hD
  let y : Fin n → T := fun i => ∑ j, D.adjugate i j * M (Fin.succ j) 0
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) T :=
    Matrix.of fun i j => Fin.cases (Fin.cases D.det (fun i' => -y i') i) (fun j' => if i = Fin.succ j' then 1 else 0) j
  have U0 : U 0 0 = D.det := rfl
  have Us0 : ∀ i, U (Fin.succ i) 0 = -y i := fun i => rfl
  have Us : ∀ i j, U i (Fin.succ j) = if i = Fin.succ j then 1 else 0 := fun i j => rfl
  have detU : U.det = D.det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have h1 : U.submatrix Fin.succ (Fin.succAbove 0) = 1 := by
      ext i j
      rw [Matrix.submatrix_apply, Fin.succAbove_zero, Us, Matrix.one_apply]
      simp [Fin.succ_inj]
    rw [h1, U0, Matrix.det_one]
    have h2 : ∀ j : Fin n, U 0 (Fin.succ j) = 0 := by
      intro j; rw [Us, if_neg (Fin.succ_ne_zero j).symm]
    simp [h2]
  have mulS : ∀ i j, (M * U) i (Fin.succ j) = M i (Fin.succ j) := by
    intro i j
    rw [Matrix.mul_apply]
    simp [Us]
  have mul0 : ∀ i, (M * U) i 0 = M i 0 * D.det - ∑ k, M i (Fin.succ k) * y k := by
    intro i
    rw [Matrix.mul_apply, Fin.sum_univ_succ, U0]
    simp [Us0, sub_eq_add_neg]
  have zero : ∀ i, (M * U) (Fin.succ i) 0 = 0 := by
    intro i
    rw [mul0]
    have h := congrFun (congrFun (Matrix.mul_adjugate D) i)
    have e : ∑ k, M (Fin.succ i) (Fin.succ k) * y k = M (Fin.succ i) 0 * D.det := by
      calc ∑ k, M (Fin.succ i) (Fin.succ k) * y k = ∑ k, ∑ j, D i k * (D.adjugate k j * M (Fin.succ j) 0) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]; rfl
        _ = ∑ j, (∑ k, D i k * D.adjugate k j) * M (Fin.succ j) 0 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ = ∑ j, (if i = j then D.det else 0) * M (Fin.succ j) 0 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have hj := h j
            rw [Matrix.mul_apply] at hj
            rw [hj, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
            split_ifs <;> simp
        _ = _ := by simp [mul_comm]
    rw [e, sub_self]
  have detMU : (M * U).det = (M 0 0 * D.det - ∑ k, M 0 (Fin.succ k) * y k) * D.det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have h1 : (M * U).submatrix (Fin.succAbove 0) Fin.succ = D := by
      ext i j
      rw [Matrix.submatrix_apply, Fin.succAbove_zero, mulS]; rfl
    rw [h1, mul0]
    simp [zero]
  rw [Matrix.det_mul, detU] at detMU
  exact hreg.right detMU


section Rec

variable {S : Type} [CommRing S] [Nontrivial S]

/-- Horner on vectors: `hv d = hw d * C`. -/
def hv {n : ℕ} (N : Matrix (Fin n) (Fin n) S) (c : ℕ → S) (b : Fin n → S) : ℕ → Fin n → S
  | 0 => fun _ => 0
  | d + 1 => fun i => ∑ j, N i j * hv N c b d j + c (n - d) * b i

omit [Nontrivial S] in
theorem hv_eq {n : ℕ} (N : Matrix (Fin n) (Fin n) S) (c : ℕ → S) (b : Fin n → S) (d : ℕ) (i : Fin n) :
    hv N c b d i = ∑ j, hw N c d i j * b j := by
  induction d generalizing i with
  | zero => simp [hv, hw]
  | succ d ih =>
    simp only [hv, hw, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
    refine congrArg₂ (· + ·) ?_ (by simp)
    · simp only [ih, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The coefficients of the characteristic polynomial, by the border recursion. -/
def cp : (n : ℕ) → Matrix (Fin n) (Fin n) S → ℕ → S
  | 0, _, k => if k = 0 then 1 else 0
  | n + 1, A, k =>
    let N := A.submatrix Fin.succ Fin.succ
    (if k = 0 then 0 else cp n N (k - 1)) - A 0 0 * cp n N k
      - (if k < n then ∑ i, A 0 (Fin.succ i) * hv N (cp n N) (fun j => A (Fin.succ j) 0) (n - k) i else 0)

omit [Nontrivial S] in
theorem fsc {ι : Type} (s : Finset ι) (f : ι → S[X]) (k : ℕ) : (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  simpa using map_sum (lcoeff S k) f s

set_option maxHeartbeats 1000000 in
theorem cp_eq : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) S) (k : ℕ), cp n A k = A.charpoly.coeff k := by
  intro n
  induction n with
  | zero =>
    intro A k
    rw [Matrix.charpoly, Matrix.det_fin_zero, coeff_one, cp]
    try simp [eq_comm]
  | succ n ih =>
    intro A k
    set N := A.submatrix Fin.succ Fin.succ with hN
    have hc : cp n N = fun j => N.charpoly.coeff j := funext fun j => ih N j
    have sub : A.charmatrix.submatrix Fin.succ Fin.succ = N.charmatrix := by
      ext i j : 2
      by_cases hij : i = j
      · subst hij; simp [hN, Matrix.charmatrix_apply_eq]
      · rw [Matrix.submatrix_apply, Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.charmatrix_apply_ne _ _ _ (fun h => hij (Fin.succ_injective _ h))]
        rfl
    have hreg : IsRegular (A.charmatrix.submatrix Fin.succ Fin.succ).det := by
      rw [sub]; exact (Matrix.charpoly_monic N).isRegular
    have hb := det_border A.charmatrix hreg
    rw [sub, adjugate_charmatrix] at hb
    have e0 : A.charmatrix 0 0 = X - C (A 0 0) := Matrix.charmatrix_apply_eq A 0
    have e1 : ∀ i, A.charmatrix 0 (Fin.succ i) = -C (A 0 (Fin.succ i)) := fun i => Matrix.charmatrix_apply_ne A _ _ (Fin.succ_ne_zero i).symm
    have e2 : ∀ i, A.charmatrix (Fin.succ i) 0 = -C (A (Fin.succ i) 0) := fun i => Matrix.charmatrix_apply_ne A _ _ (Fin.succ_ne_zero i)
    have hcoef : ∀ i j, (W N i j).coeff k = if k < n then hw N (cp n N) (n - k) i j else 0 := by
      intro i j
      rw [W, hc, Matrix.sum_apply, fsc]
      have : ∀ x ∈ Finset.range n, (((X : S[X]) ^ x • (hw N (fun j => N.charpoly.coeff j) (n - x)).map C) i j).coeff k
          = if k = x then hw N (fun j => N.charpoly.coeff j) (n - k) i j else 0 := by
        intro x _
        rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, coeff_X_pow_mul']
        split_ifs with h1 h2 h2
        · subst h2; simp
        · rw [coeff_C, if_neg (by omega)]
        · omega
        · rfl
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
      simp
    have hd : A.charpoly = (X - C (A 0 0)) * N.charpoly - ∑ i, C (A 0 (Fin.succ i)) * ∑ j, W N i j * C (A (Fin.succ j) 0) := by
      rw [Matrix.charpoly, Matrix.charpoly, hb, e0]
      refine congrArg (fun q : S[X] => (X - C (A 0 0)) * N.charmatrix.det - q) ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      have h3 : ∑ j, W N i j * A.charmatrix (Fin.succ j) 0 = -∑ j, W N i j * C (A (Fin.succ j) 0) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [e2, mul_neg]
      rw [h3, e1, neg_mul_neg]
    rw [hd, coeff_sub, sub_mul, coeff_sub, fsc, coeff_C_mul]
    have hX : (X * N.charpoly).coeff k = if k = 0 then 0 else cp n N (k - 1) := by
      rcases k with _ | k
      · simp
      · rw [coeff_X_mul, ih]; simp
    rw [hX, ← ih]
    show _ - _ - _ = _
    congr 1
    have hi : ∀ i, (C (A 0 (Fin.succ i)) * ∑ j, W N i j * C (A (Fin.succ j) 0)).coeff k
        = if k < n then A 0 (Fin.succ i) * hv N (cp n N) (fun j => A (Fin.succ j) 0) (n - k) i else 0 := by
      intro i
      rw [coeff_C_mul, fsc, hv_eq]
      have h4 : ∀ j, (W N i j * C (A (Fin.succ j) 0)).coeff k = (if k < n then hw N (cp n N) (n - k) i j else 0) * A (Fin.succ j) 0 := by
        intro j; rw [coeff_mul_C, hcoef]
      rw [Finset.sum_congr rfl fun j _ => h4 j]
      by_cases hk : k < n
      · simp only [if_pos hk]
      · simp only [if_neg hk, zero_mul, Finset.sum_const_zero, mul_zero]
    rw [Finset.sum_congr rfl fun i _ => hi i]
    by_cases hk : k < n
    · rw [if_pos hk]
      exact (Finset.sum_congr rfl fun i _ => if_pos hk).symm
    · rw [if_neg hk]
      exact (Finset.sum_eq_zero fun i _ => if_neg hk).symm

theorem det_eq_cp (n : ℕ) (A : Matrix (Fin n) (Fin n) S) : A.det = (-1) ^ n * cp n A 0 := by
  rw [cp_eq, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]

end Rec


section Slp

variable {V R : Type} [CommRing R]

/-- Straight-line programs, newest value first. -/
inductive Slp : List (MvPolynomial V R) → Prop
  | nil : Slp []
  | var (l) (v : V) : Slp l → Slp (MvPolynomial.X v :: l)
  | const (l) (a : R) : Slp l → Slp (MvPolynomial.C a :: l)
  | add (l) (p q) : p ∈ l → q ∈ l → Slp l → Slp ((p + q) :: l)
  | mul (l) (p q) : p ∈ l → q ∈ l → Slp l → Slp ((p * q) :: l)

/-- From any program that holds `I`, at most `c` more gates give all of `T`. -/
def Cost (I : Set (MvPolynomial V R)) (c : ℕ) (T : Set (MvPolynomial V R)) : Prop :=
  ∀ l, Slp l → (∀ x ∈ I, x ∈ l) → ∃ l', Slp l' ∧ (∀ x ∈ l, x ∈ l') ∧ (∀ x ∈ T, x ∈ l') ∧ l'.length ≤ l.length + c

theorem Cost.self (I : Set (MvPolynomial V R)) : Cost I 0 I := fun l hl hI => ⟨l, hl, fun _ h => h, hI, le_rfl⟩

theorem Cost.mono {I J T U : Set (MvPolynomial V R)} {c d : ℕ} (h : Cost I c T) (hI : I ⊆ J) (hT : U ⊆ T) (hc : c ≤ d) : Cost J d U := by
  intro l hl hJ
  obtain ⟨l', h1, h2, h3, h4⟩ := h l hl fun x hx => hJ x (hI hx)
  exact ⟨l', h1, h2, fun x hx => h3 x (hT hx), by omega⟩

theorem Cost.comp {I T U : Set (MvPolynomial V R)} {c d : ℕ} (h : Cost I c T) (h' : Cost (I ∪ T) d U) : Cost I (c + d) (T ∪ U) := by
  intro l hl hI
  obtain ⟨l', h1, h2, h3, h4⟩ := h l hl hI
  obtain ⟨l2, k1, k2, k3, k4⟩ := h' l' h1 (by rintro x (hx | hx); exacts [h2 x (hI x hx), h3 x hx])
  refine ⟨l2, k1, fun x hx => k2 x (h2 x hx), ?_, by omega⟩
  rintro x (hx | hx)
  exacts [k2 x (h3 x hx), k3 x hx]

theorem Cost.union {I T U : Set (MvPolynomial V R)} {c d : ℕ} (h : Cost I c T) (h' : Cost I d U) : Cost I (c + d) (T ∪ U) :=
  h.comp (h'.mono Set.subset_union_left le_rfl le_rfl)

theorem Cost.const (I : Set (MvPolynomial V R)) (a : R) : Cost I 1 {MvPolynomial.C a} := fun l hl _ =>
  ⟨_, Slp.const l a hl, fun x hx => List.mem_cons_of_mem _ hx, by rintro x rfl; exact List.mem_cons_self, by simp⟩

theorem Cost.var (I : Set (MvPolynomial V R)) (v : V) : Cost I 1 {MvPolynomial.X v} := fun l hl _ =>
  ⟨_, Slp.var l v hl, fun x hx => List.mem_cons_of_mem _ hx, by rintro x rfl; exact List.mem_cons_self, by simp⟩

theorem Cost.add {I : Set (MvPolynomial V R)} {p q} {c d : ℕ} (hp : Cost I c {p}) (hq : Cost I d {q}) : Cost I (c + d + 1) {p + q} := by
  intro l hl hI
  obtain ⟨l', h1, h2, h3, h4⟩ := hp.union hq l hl hI
  exact ⟨_, Slp.add l' p q (h3 p (Or.inl rfl)) (h3 q (Or.inr rfl)) h1, fun x hx => List.mem_cons_of_mem _ (h2 x hx),
    by rintro x rfl; exact List.mem_cons_self, by simp; omega⟩

theorem Cost.mul {I : Set (MvPolynomial V R)} {p q} {c d : ℕ} (hp : Cost I c {p}) (hq : Cost I d {q}) : Cost I (c + d + 1) {p * q} := by
  intro l hl hI
  obtain ⟨l', h1, h2, h3, h4⟩ := hp.union hq l hl hI
  exact ⟨_, Slp.mul l' p q (h3 p (Or.inl rfl)) (h3 q (Or.inr rfl)) h1, fun x hx => List.mem_cons_of_mem _ (h2 x hx),
    by rintro x rfl; exact List.mem_cons_self, by simp; omega⟩

theorem Cost.mem {I : Set (MvPolynomial V R)} {p} (hp : p ∈ I) : Cost I 0 {p} :=
  (Cost.self I).mono le_rfl (by rintro x rfl; exact hp) le_rfl

/-- Finitely many targets. -/
theorem Cost.all {I : Set (MvPolynomial V R)} {c m : ℕ} (F : Fin m → MvPolynomial V R) (h : ∀ i, Cost I c {F i}) :
    Cost I (m * c) (Set.range F) := by
  induction m with
  | zero => exact (Cost.self I).mono le_rfl (by rintro x ⟨i, _⟩; exact i.elim0) (by omega)
  | succ m ih =>
    have h1 := (ih (fun i => F i.succ) fun i => h i.succ).union (h 0)
    refine h1.mono le_rfl ?_ (by rw [Nat.add_mul]; omega)
    rintro x ⟨i, rfl⟩
    refine Fin.cases (Or.inr rfl) (fun j => Or.inl ⟨j, rfl⟩) i

theorem Cost.sum {I : Set (MvPolynomial V R)} {c m : ℕ} (F : Fin m → MvPolynomial V R) (h : ∀ i, Cost I c {F i}) :
    Cost I (m * (c + 1) + 1) {∑ i, F i} := by
  induction m with
  | zero => exact (Cost.const I 0).mono le_rfl (by simp) (by omega)
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    exact ((h 0).add (ih (fun i => F i.succ) fun i => h i.succ)).mono le_rfl le_rfl (by rw [Nat.add_mul]; omega)

theorem Cost.dot {I : Set (MvPolynomial V R)} {m : ℕ} (f g : Fin m → MvPolynomial V R) (hf : ∀ i, f i ∈ I) (hg : ∀ i, g i ∈ I) :
    Cost I (2 * m + 1) {∑ i, f i * g i} :=
  (Cost.sum _ fun i => (Cost.mem (hf i)).mul (Cost.mem (hg i))).mono le_rfl le_rfl (by omega)

variable [Nontrivial R]

/-- The entries of a matrix. -/
def Ent {n : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial V R)) : Set (MvPolynomial V R) := Set.range fun p : Fin n × Fin n => A p.1 p.2

omit [Nontrivial R] in
theorem cost_hv {n : ℕ} (N : Matrix (Fin n) (Fin n) (MvPolynomial V R)) (c : ℕ → MvPolynomial V R) (b : Fin n → MvPolynomial V R)
    (I : Set (MvPolynomial V R)) (hN : ∀ i j, N i j ∈ I) (hc : ∀ k, c k ∈ I) (hb : ∀ i, b i ∈ I) :
    ∀ d, Cost I (1 + d * (n * (2 * n + 3))) {x | ∃ e ≤ d, ∃ i, hv N c b e i = x} := by
  intro d
  induction d with
  | zero =>
    refine (Cost.const I 0).mono le_rfl ?_ (by omega)
    rintro x ⟨e, he, i, rfl⟩
    obtain rfl : e = 0 := by omega
    simp [hv]
  | succ d ih =>
    have st : Cost (I ∪ {x | ∃ e ≤ d, ∃ i, hv N c b e i = x}) (n * (2 * n + 3)) (Set.range fun i => hv N c b (d + 1) i) := by
      refine Cost.all _ fun i => ?_
      have h1 := Cost.dot (I := I ∪ {x | ∃ e ≤ d, ∃ i, hv N c b e i = x}) (fun j => N i j) (fun j => hv N c b d j)
        (fun j => Or.inl (hN i j)) (fun j => Or.inr ⟨d, le_rfl, j, rfl⟩)
      exact (h1.add ((Cost.mem (Or.inl (hc (n - d)))).mul (Cost.mem (Or.inl (hb i))))).mono le_rfl le_rfl (by omega)
    refine (ih.comp st).mono le_rfl ?_ (by rw [Nat.add_mul]; omega)
    rintro x ⟨e, he, i, rfl⟩
    rcases Nat.lt_or_ge e (d + 1) with h | h
    · exact Or.inl ⟨e, by omega, i, rfl⟩
    · obtain rfl : e = d + 1 := by omega
      exact Or.inr ⟨i, rfl⟩

theorem cp_zero_of_gt {n : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial V R)) {k : ℕ} (hk : n < k) : cp n A k = 0 := by
  rw [cp_eq]
  exact coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim]; simpa using hk)

theorem cost_cp : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial V R)), Cost (Ent A) (2 + 40 * n ^ 4) (Set.range (cp n A)) := by
  intro n
  induction n with
  | zero =>
    intro A
    refine ((Cost.const _ 1).union (Cost.const _ 0)).mono le_rfl ?_ (by omega)
    rintro x ⟨k, rfl⟩
    rw [cp]
    split_ifs
    · left; simp
    · right; simp
  | succ n ih =>
    intro A
    let N := A.submatrix Fin.succ Fin.succ
    let b : Fin n → MvPolynomial V R := fun j => A (Fin.succ j) 0
    have hNA : Ent N ⊆ Ent A := by rintro x ⟨p, rfl⟩; exact ⟨(Fin.succ p.1, Fin.succ p.2), rfl⟩
    have h1 : Cost (Ent A) (2 + 40 * n ^ 4) (Set.range (cp n N)) := (ih N).mono hNA le_rfl le_rfl
    let I := Ent A ∪ Set.range (cp n N)
    have ent : ∀ i j, A i j ∈ I := fun i j => Or.inl ⟨(i, j), rfl⟩
    have cpm : ∀ k, cp n N k ∈ I := fun k => Or.inr ⟨k, rfl⟩
    have h2 := cost_hv N (cp n N) b I (fun i j => ent _ _) cpm (fun i => ent _ _) n
    let J := I ∪ {x | ∃ e ≤ n, ∃ i, hv N (cp n N) b e i = x}
    have h3 : Cost J ((n + 3) * (2 * n + 10)) (Set.range fun k : Fin (n + 3) => cp (n + 1) A k.val) := by
      refine Cost.all _ fun k => ?_
      have c1 : Cost J 1 {(if k.val = 0 then 0 else cp n N (k.val - 1))} := by
        split_ifs
        · exact (Cost.const J 0).mono le_rfl (by simp) le_rfl
        · exact (Cost.mem (Or.inl (cpm _))).mono le_rfl le_rfl (by omega)
      have c2 : Cost J 1 {A 0 0 * cp n N k.val} := (Cost.mem (Or.inl (ent 0 0))).mul (Cost.mem (Or.inl (cpm _)))
      have c3 : Cost J (2 * n + 1) {(if k.val < n then ∑ i, A 0 (Fin.succ i) * hv N (cp n N) b (n - k.val) i else 0)} := by
        split_ifs
        · exact Cost.dot _ _ (fun i => Or.inl (ent _ _)) (fun i => Or.inr ⟨n - k.val, by omega, i, rfl⟩)
        · exact (Cost.const J 0).mono le_rfl (by simp) (by omega)
      have neg : ∀ {p : MvPolynomial V R} {c}, Cost J c {p} → Cost J (c + 2) {MvPolynomial.C (-1) * p} := fun h =>
        ((Cost.const J (-1)).mul h).mono le_rfl le_rfl (by omega)
      have c4 := (c1.add (neg c2)).add (neg c3)
      refine c4.mono le_rfl ?_ (by omega)
      rintro x rfl
      show cp (n + 1) A k.val = _
      rw [cp]
      simp only [map_neg, map_one, neg_mul, one_mul, sub_eq_add_neg]
      rfl
    refine ((h1.comp (h2.comp h3)).mono le_rfl ?_ ?_)
    · rintro x ⟨k, rfl⟩
      rcases Nat.lt_or_ge k (n + 3) with hk | hk
      · exact Or.inr (Or.inr ⟨⟨k, hk⟩, rfl⟩)
      · refine Or.inr (Or.inr ⟨⟨n + 2, by omega⟩, ?_⟩)
        show cp (n + 1) A (n + 2) = cp (n + 1) A k
        rw [cp_zero_of_gt A (by omega), cp_zero_of_gt A (by omega)]
    · have e1 : n * (n * (2 * n + 3)) + (n + 3) * (2 * n + 10) + 1 ≤ 40 * (n + 1) ^ 3 := by
        ring_nf; nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2), Nat.zero_le n]
      have e2 : 40 * n ^ 4 + 40 * (n + 1) ^ 3 ≤ 40 * (n + 1) ^ 4 := by
        ring_nf; nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2), Nat.zero_le n]
      omega

theorem cost_det (n : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial V R)) : Cost (Ent A) (4 + 40 * n ^ 4) {A.det} := by
  have h := (Cost.const (Ent A) ((-1 : R) ^ n)).mul ((cost_cp n A).mono le_rfl (U := {cp n A 0}) (by rintro x rfl; exact ⟨0, rfl⟩) le_rfl)
  refine h.mono le_rfl ?_ (by omega)
  rintro x rfl
  rw [Set.mem_singleton_iff, det_eq_cp]
  simp

omit [Nontrivial R] in
/-- A program as a sequence. -/
theorem Slp.seq {l : List (MvPolynomial V R)} (h : Slp l) : ∃ g : ℕ → MvPolynomial V R,
    (∀ k < l.length, (∃ v : V, g k = MvPolynomial.X v) ∨ (∃ a : R, g k = MvPolynomial.C a) ∨
      (∃ i < k, ∃ j < k, g k = g i + g j) ∨ (∃ i < k, ∃ j < k, g k = g i * g j)) ∧
    ∀ p ∈ l, ∃ k < l.length, g k = p := by
  have key : ∀ (l : List (MvPolynomial V R)) (q : MvPolynomial V R),
      (∃ g : ℕ → MvPolynomial V R,
        (∀ k < l.length, (∃ v : V, g k = MvPolynomial.X v) ∨ (∃ a : R, g k = MvPolynomial.C a) ∨
          (∃ i < k, ∃ j < k, g k = g i + g j) ∨ (∃ i < k, ∃ j < k, g k = g i * g j)) ∧
        (∀ p ∈ l, ∃ k < l.length, g k = p) ∧
        ((∃ v : V, q = MvPolynomial.X v) ∨ (∃ a : R, q = MvPolynomial.C a) ∨
          (∃ i < l.length, ∃ j < l.length, q = g i + g j) ∨ (∃ i < l.length, ∃ j < l.length, q = g i * g j))) →
      ∃ g : ℕ → MvPolynomial V R,
        (∀ k < (q :: l).length, (∃ v : V, g k = MvPolynomial.X v) ∨ (∃ a : R, g k = MvPolynomial.C a) ∨
          (∃ i < k, ∃ j < k, g k = g i + g j) ∨ (∃ i < k, ∃ j < k, g k = g i * g j)) ∧
        ∀ p ∈ q :: l, ∃ k < (q :: l).length, g k = p := by
    rintro l q ⟨g, h1, h2, h3⟩
    let g' : ℕ → MvPolynomial V R := fun k => if k = l.length then q else g k
    have e : ∀ k, k < l.length → g' k = g k := fun k hk => if_neg (by omega)
    have eq : g' l.length = q := if_pos rfl
    refine ⟨g', fun k hk => ?_, fun p hp => ?_⟩
    · rw [List.length_cons] at hk
      rcases Nat.lt_or_ge k l.length with h | h
      · rw [e k h]
        rcases h1 k h with h | h | ⟨i, hi, j, hj, h⟩ | ⟨i, hi, j, hj, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [e i (by omega), e j (by omega)]; exact h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [e i (by omega), e j (by omega)]; exact h⟩))
      · obtain rfl : k = l.length := by omega
        rw [eq]
        rcases h3 with h | h | ⟨i, hi, j, hj, h⟩ | ⟨i, hi, j, hj, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [e i hi, e j hj]; exact h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [e i hi, e j hj]; exact h⟩))
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨l.length, by simp, eq⟩
      · obtain ⟨k, hk, hkp⟩ := h2 p hp
        exact ⟨k, by simp; omega, by rw [e k hk]; exact hkp⟩
  induction h with
  | nil => exact ⟨fun _ => 0, fun k hk => absurd hk (by simp), fun p hp => absurd hp (by simp)⟩
  | var l v _ ih =>
    obtain ⟨g, h1, h2⟩ := ih
    exact key l _ ⟨g, h1, h2, Or.inl ⟨v, rfl⟩⟩
  | const l a _ ih =>
    obtain ⟨g, h1, h2⟩ := ih
    exact key l _ ⟨g, h1, h2, Or.inr (Or.inl ⟨a, rfl⟩)⟩
  | add l p q hp hq _ ih =>
    obtain ⟨g, h1, h2⟩ := ih
    obtain ⟨i, hi, rfl⟩ := h2 p hp
    obtain ⟨j, hj, rfl⟩ := h2 q hq
    exact key l _ ⟨g, h1, h2, Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, rfl⟩))⟩
  | mul l p q hp hq _ ih =>
    obtain ⟨g, h1, h2⟩ := ih
    obtain ⟨i, hi, rfl⟩ := h2 p hp
    obtain ⟨j, hj, rfl⟩ := h2 q hq
    exact key l _ ⟨g, h1, h2, Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, rfl⟩))⟩

/-- The determinant of a matrix of linear forms in finitely many variables. -/
theorem cost_det_forms {m n : ℕ} (e : Fin m → V) (A : Matrix (Fin n) (Fin n) (MvPolynomial V R))
    (a : Fin n → Fin n → Fin m → R) (a₀ : Fin n → Fin n → R)
    (hA : ∀ i j, A i j = ∑ t, MvPolynomial.C (a i j t) * MvPolynomial.X (e t) + MvPolynomial.C (a₀ i j)) :
    Cost (∅ : Set (MvPolynomial V R)) (n * n * (4 * m + 4) + (4 + 40 * n ^ 4)) {A.det} := by
  have h1 : Cost (∅ : Set (MvPolynomial V R)) (n * n * (4 * m + 4)) (Ent A) := by
    have h := Cost.all (I := (∅ : Set (MvPolynomial V R))) (c := 4 * m + 4) (fun p : Fin (n * n) => A (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) fun p => by
      rw [hA]
      exact ((Cost.sum _ fun t => (Cost.const _ (a _ _ t)).mul (Cost.var _ (e t))).add (Cost.const _ (a₀ _ _))).mono le_rfl le_rfl (by omega)
    refine h.mono le_rfl ?_ le_rfl
    rintro x ⟨p, rfl⟩
    exact ⟨finProdFinEquiv p, by simp⟩
  have h2 := h1.comp ((cost_det n A).mono Set.subset_union_right le_rfl le_rfl)
  exact h2.mono le_rfl Set.subset_union_right le_rfl

end Slp


end P4

section Final

open MvPolynomial Filter PEqualNP.Gct

/-- The substitution that undoes the padding. -/
noncomputable def unpad (R : Type) [CommRing R] (m n : ℕ) (x : Fin (n + 1) × Fin (n + 1)) : MvPolynomial (Fin m × Fin m) R := by
  classical
  exact if x = (0, 0) then 1 else if h : ∃ p, padIndex m n p = x then X h.choose else 0

theorem padIndex_inj {m n : ℕ} (hmn : m ≤ n) : Function.Injective (padIndex m n) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 := congrArg (fun x : Fin (n + 1) × Fin (n + 1) => x.1.val) h
  have h2 := congrArg (fun x : Fin (n + 1) × Fin (n + 1) => x.2.val) h
  simp only [padIndex, Fin.val_ofNat] at h1 h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1 h2
  exact Prod.ext (Fin.ext (by simpa using h1)) (Fin.ext (by simpa using h2))

theorem padIndex_ne {m n : ℕ} (hmn : m ≤ n) (p : Fin m × Fin m) : padIndex m n p ≠ (0, 0) := by
  intro h
  have h1 := congrArg (fun x : Fin (n + 1) × Fin (n + 1) => x.1.val) h
  simp only [padIndex, Fin.val_ofNat] at h1
  rw [Nat.mod_eq_of_lt (by omega)] at h1
  simp at h1

theorem unpad_zero (R : Type) [CommRing R] (m n : ℕ) : unpad R m n (0, 0) = 1 := by
  unfold unpad; rw [if_pos rfl]

theorem unpad_pad (R : Type) [CommRing R] {m n : ℕ} (hmn : m ≤ n) (p : Fin m × Fin m) : unpad R m n (padIndex m n p) = X p := by
  have h : ∃ p', padIndex m n p' = padIndex m n p := ⟨p, rfl⟩
  unfold unpad
  rw [if_neg (padIndex_ne hmn p), dif_pos h, padIndex_inj hmn h.choose_spec]

theorem unpad_cases (R : Type) [CommRing R] (m n : ℕ) (x) : unpad R m n x = C 1 ∨ (∃ p, unpad R m n x = X p) ∨ unpad R m n x = C 0 := by
  unfold unpad
  split_ifs with h1 h2
  · left; simp
  · right; left; exact ⟨_, rfl⟩
  · right; right; simp

theorem unpad_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m n : ℕ) (x) : map f (unpad R m n x) = unpad S m n x := by
  unfold unpad
  split_ifs <;> simp

theorem perm_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) : map f (permPoly R m) = permPoly S m := by
  simp only [permPoly, Matrix.permanent, map_sum, map_prod, Matrix.mvPolynomialX_apply, map_X]

theorem padded_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m n : ℕ) : map f (paddedPerm R m n) = paddedPerm S m n := by
  rw [paddedPerm, map_mul, map_pow, map_X, map_rename, perm_map]; rfl

theorem unpad_padded (R : Type) [CommRing R] {m n : ℕ} (hmn : m ≤ n) : aeval (unpad R m n) (paddedPerm R m n) = permPoly R m := by
  rw [paddedPerm, map_mul, map_pow, aeval_X, unpad_zero, one_pow, one_mul, aeval_rename]
  have : unpad R m n ∘ padIndex m n = X := funext fun p => unpad_pad R hmn p
  rw [this]
  exact aeval_X_left_apply _

theorem permPoly_eq (F : Type) [Field F] (m : ℕ) : permPoly F m = Statement.perm F m := by
  simp only [permPoly, Matrix.permanent, Statement.perm, Matrix.mvPolynomialX_apply]

theorem coeff_universal {ι A : Type} [Fintype ι] [CommRing A] (E : A →+* ℂ) (j : ℂ →+* A) (hid : E.comp j = RingHom.id ℂ)
    (f : MvPolynomial ι ℂ) (γ : Matrix ι ι A) (s : ι →₀ ℕ) :
    E ((linSubst γ (map j f)).coeff s) = (linSubst (γ.map E) f).coeff s := by
  rw [← coeff_map]
  unfold linSubst
  rw [map_bind₁, MvPolynomial.map_map, hid, MvPolynomial.map_id]
  have : (fun i => map E (∑ j, C (γ i j) * X j)) = fun i => ∑ j, C ((γ.map E) i j) * (X j : MvPolynomial ι ℂ) := by
    funext i
    simp only [map_sum, map_mul, map_C, map_X, Matrix.map_apply]
  rw [this]

theorem linSubst_map {ι A B : Type} [Fintype ι] [CommRing A] [CommRing B] (ψ : A →+* B) (j : ℂ →+* A) (f : MvPolynomial ι ℂ) (γ : Matrix ι ι A) :
    map ψ (linSubst γ (map j f)) = linSubst (γ.map ψ) (map (ψ.comp j) f) := by
  unfold linSubst
  rw [map_bind₁, MvPolynomial.map_map]
  have : (fun i => map ψ (∑ j, C (γ i j) * X j)) = fun i => ∑ j, C ((γ.map ψ) i j) * (X j : MvPolynomial ι B) := by
    funext i
    simp only [map_sum, map_mul, map_C, map_X, Matrix.map_apply]
  rw [this]

theorem limits {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial ι ℂ) (PZ : MvPolynomial ι ℤ)
    (hmem : map (Int.castRingHom ℂ) PZ ∈ orbitClosure f) (A : Type) [CommRing A] (j : ℂ →+* A) (γ : Matrix ι ι A)
    (E : Matrix ι ι ℂ → (A →+* ℂ)) (hid : ∀ g, (E g).comp j = RingHom.id ℂ) (hγ : ∀ g, γ.map (E g) = g) :
    ∃ g : ℕ → Matrix ι ι ℂ, ∀ s, Tendsto (fun t => E (g t) ((linSubst γ (map j f)).coeff s)) atTop (nhds ((PZ.coeff s : ℤ) : ℂ)) := by
  obtain ⟨g, hg⟩ := hmem
  refine ⟨fun t => (g t : Matrix ι ι ℂ), fun s => ?_⟩
  have h2 := hg s
  rw [coeff_map] at h2
  have h1 : (fun t => E (g t : Matrix ι ι ℂ) ((linSubst γ (map j f)).coeff s)) = fun t => (linSubst (g t : Matrix ι ι ℂ) f).coeff s := by
    funext t
    rw [coeff_universal (E _) j (hid _), hγ]
  rw [h1]
  exact h2

/-- A limit of the orbit is reached by power series. -/
theorem arc_of_orbit {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial ι ℂ) (PZ : MvPolynomial ι ℤ)
    (hmem : map (Int.castRingHom ℂ) PZ ∈ orbitClosure f) :
    ∃ (k : Type) (_ : Field k) (_ : CharZero k) (γ : Matrix ι ι (LaurentSeries k)) (j : ℂ →+* LaurentSeries k) (Q' : MvPolynomial ι (PowerSeries k)),
      map (HahnSeries.ofPowerSeries ℤ k) Q' = linSubst γ (map j f) ∧ map (PowerSeries.constantCoeff (R := k)) Q' = map (Int.castRingHom k) PZ := by
  classical
  let G : Matrix ι ι (MvPolynomial (ι × ι) ℂ) := fun i j => X (i, j)
  obtain ⟨g, lim⟩ := limits f PZ hmem (MvPolynomial (ι × ι) ℂ) C G (fun g => eval fun p => g p.1 p.2)
    (fun g => by ext; simp) (fun g => by refine Matrix.ext fun x y => ?_; rw [Matrix.map_apply]; exact eval_X _)
  obtain ⟨U, hU⟩ : ∃ U, U = linSubst G (map C f) := ⟨_, rfl⟩
  rw [← hU] at lim
  obtain ⟨e, he⟩ := limit_hom (fun s : U.support => U.coeff s.1) (fun t p => g t p.1 p.2) (fun s => ((PZ.coeff s.1 : ℤ) : ℂ)) fun s => lim s.1
  obtain ⟨k, ik, ck, ψ, hψ⟩ := arc (fun s : U.support => U.coeff s.1) (fun s => PZ.coeff s.1) e he
  have hF : ∀ s, ∃ f : PowerSeries k, ψ (U.coeff s) = HahnSeries.ofPowerSeries ℤ k f ∧ PowerSeries.constantCoeff f = ((PZ.coeff s : ℤ) : k) := by
    intro s
    by_cases hs : s ∈ U.support
    · exact hψ ⟨s, hs⟩
    · have h0 : U.coeff s = 0 := notMem_support_iff.1 hs
      have hl := lim s
      simp only [h0, map_zero] at hl
      have h1 : ((PZ.coeff s : ℤ) : ℂ) = 0 := tendsto_nhds_unique hl tendsto_const_nhds
      have h2 : PZ.coeff s = 0 := by exact_mod_cast h1
      exact ⟨0, by rw [h0, map_zero, map_zero], by rw [h2]; simp⟩
  choose F hF1 hF2 using hF
  have hQ' : ∀ s, (∑ s ∈ U.support, monomial s (F s)).coeff s = if s ∈ U.support then F s else 0 := by
    intro s
    simp only [coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
  refine ⟨k, ik, ck, G.map ψ, ψ.comp C, ∑ s ∈ U.support, monomial s (F s), ?_, ?_⟩
  · have hmap : linSubst (G.map ψ) (map (ψ.comp C) f) = map ψ U := by
      rw [hU, linSubst_map]
    rw [hmap]
    refine MvPolynomial.ext _ _ fun s => ?_
    rw [coeff_map, coeff_map, hQ']
    split_ifs with h
    · exact (hF1 s).symm
    · rw [map_zero, notMem_support_iff.1 h, map_zero]
  · refine MvPolynomial.ext _ _ fun s => ?_
    rw [coeff_map, hQ', coeff_map]
    split_ifs with h
    · exact hF2 s
    · rw [map_zero]
      have h3 := hF2 s
      have h4 := hF1 s
      rw [notMem_support_iff.1 h, map_zero] at h4
      have h5 : F s = 0 := HahnSeries.ofPowerSeries_injective (h4.symm.trans (map_zero _).symm)
      rw [h5, map_zero] at h3
      exact h3

set_option maxHeartbeats 1000000 in
/-- Membership in the orbit closure gives an approximating circuit of polynomial size over some field of characteristic zero. -/
theorem approximates_of_mem {m n : ℕ} (hmn : m ≤ n) (hmem : paddedPerm ℂ m n ∈ orbitClosure (detPoly ℂ (n + 1))) :
    ∃ (k : Type) (_ : Field k) (_ : CharZero k), Statement.Approximates (Statement.perm k m) (49 * (n + 1) ^ 4) := by
  classical
  obtain ⟨k, ik, ck, γ, j, Q', hQ1, hQ2⟩ := arc_of_orbit (detPoly ℂ (n + 1)) (paddedPerm ℤ m n) (by rw [padded_map]; exact hmem)
  rw [padded_map] at hQ2
  refine ⟨k, ik, ck, ?_⟩
  let q' : MvPolynomial (Fin m × Fin m) (PowerSeries k) := aeval (unpad _ m n) Q'
  let q : MvPolynomial (Fin m × Fin m) (LaurentSeries k) := aeval (unpad _ m n) (linSubst γ (map j (detPoly ℂ (n + 1))))
  have aeval_map' : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : MvPolynomial (Fin (n + 1) × Fin (n + 1)) R),
      map f (aeval (unpad R m n) x) = aeval (unpad S m n) (map f x) := by
    intro R S _ _ f x
    induction x using MvPolynomial.induction_on with
    | C r => simp [algebraMap_eq]
    | add x y hx hy => simp only [map_add, hx, hy]
    | mul_X x i hx => simp only [map_mul, hx, map_X, aeval_X, unpad_map]
  have hq : map (HahnSeries.ofPowerSeries ℤ k) q' = q := by
    show map _ (aeval _ Q') = _
    rw [aeval_map', hQ1]
  have hq2 : map (PowerSeries.constantCoeff (R := k)) q' = Statement.perm k m := by
    show map _ (aeval _ Q') = _
    rw [aeval_map', hQ2, unpad_padded k hmn, permPoly_eq]
  -- the circuit
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin m × Fin m) (LaurentSeries k)) :=
    fun i j => ∑ x : Fin (n + 1) × Fin (n + 1), C (γ (i, j) x) * unpad _ m n x
  have hdet : q = B.det := by
    have h0 : ∀ x : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ, aeval (unpad (LaurentSeries k) m n) (linSubst γ (map j x))
        = eval₂Hom ((C : LaurentSeries k →+* MvPolynomial (Fin m × Fin m) (LaurentSeries k)).comp j) (fun y => ∑ x, C (γ y x) * unpad (LaurentSeries k) m n x) x := by
      intro x
      unfold linSubst
      induction x using MvPolynomial.induction_on with
      | C r => simp [algebraMap_eq]
      | add x y hx hy => simp only [map_add, hx, hy]
      | mul_X x i hx =>
        simp only [map_mul, hx, map_X, bind₁_X_right, map_sum, aeval_X, aeval_C, algebraMap_eq, eval₂Hom_X']
    show aeval (unpad (LaurentSeries k) m n) (linSubst γ (map j (detPoly ℂ (n + 1)))) = _
    rw [h0, detPoly, RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j' => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply, eval₂Hom_X']
  have hcost : Cost (∅ : Set (MvPolynomial (Fin m × Fin m) (LaurentSeries k))) (49 * (n + 1) ^ 4) {q} := by
    have hent : Cost (∅ : Set (MvPolynomial (Fin m × Fin m) (LaurentSeries k))) ((n + 1) * (n + 1) * ((n + 1) * (n + 1) * 4 + 1)) (Ent B) := by
      have h := Cost.all (I := (∅ : Set (MvPolynomial (Fin m × Fin m) (LaurentSeries k)))) (c := (n + 1) * (n + 1) * 4 + 1)
        (fun p : Fin ((n + 1) * (n + 1)) => B (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) fun p => by
          have hs := Cost.sum (I := (∅ : Set (MvPolynomial (Fin m × Fin m) (LaurentSeries k)))) (c := 3)
            (fun t : Fin ((n + 1) * (n + 1)) => C (γ ((finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2) (finProdFinEquiv.symm t)) * unpad _ m n (finProdFinEquiv.symm t))
            fun t => by
              have hu : Cost (∅ : Set (MvPolynomial (Fin m × Fin m) (LaurentSeries k))) 1 {unpad (LaurentSeries k) m n (finProdFinEquiv.symm t)} := by
                rcases unpad_cases (LaurentSeries k) m n (finProdFinEquiv.symm t) with h | ⟨p, h⟩ | h
                · rw [h]; exact Cost.const _ _
                · rw [h]; exact Cost.var _ _
                · rw [h]; exact Cost.const _ _
              exact (Cost.const _ _).mul hu
          refine hs.mono le_rfl ?_ le_rfl
          rintro x rfl
          rw [Set.mem_singleton_iff]
          exact (Equiv.sum_comp finProdFinEquiv.symm fun x : Fin (n + 1) × Fin (n + 1) =>
            C (γ ((finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2) x) * unpad (LaurentSeries k) m n x).symm
      refine h.mono le_rfl ?_ le_rfl
      rintro x ⟨p, rfl⟩
      exact ⟨finProdFinEquiv p, by simp⟩
    have h2 := hent.comp ((cost_det (n + 1) B).mono Set.subset_union_right le_rfl le_rfl)
    refine h2.mono le_rfl ?_ ?_
    · rintro x rfl
      rw [hdet]; exact Or.inr rfl
    · have hν1 : 1 ≤ n + 1 := by omega
      have e1 : (n + 1) * (n + 1) ≤ (n + 1) ^ 4 := by
        calc (n + 1) * (n + 1) = (n + 1) ^ 2 := by ring
          _ ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right hν1 (by norm_num)
      have e2 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ hν1
      have e3 : (n + 1) * (n + 1) * ((n + 1) * (n + 1) * 4 + 1) = 4 * (n + 1) ^ 4 + (n + 1) * (n + 1) := by ring
      omega
  refine ⟨q, ?_, ?_⟩
  · obtain ⟨l, hl, _, hT, hlen⟩ := hcost [] Slp.nil (fun x hx => absurd hx (Set.notMem_empty x))
    obtain ⟨G', h1, h2⟩ := hl.seq
    obtain ⟨j, hj, hjq⟩ := h2 q (hT q rfl)
    have hlen' : l.length ≤ 49 * (n + 1) ^ 4 := by simpa using hlen
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
    rw [← hq, coeff_map]
    have hcoe : ∀ f : PowerSeries k, HahnSeries.ofPowerSeries ℤ k f = (f : LaurentSeries k) := fun _ => rfl
    rw [hcoe, PowerSeries.coeff_coe]
    rcases lt_or_eq_of_le hi with h | rfl
    · rw [if_pos h, if_neg h.ne]
    · rw [if_neg (lt_irrefl _), if_pos rfl, ← hq2, coeff_map]
      simp

/-- For each exponent, large padded permanents are outside the orbit closure, given the bound for approximating circuits. -/
theorem bridge (h : Statement.MainTheoremApprox.{0}) (c : ℕ) (hc : 1 ≤ c) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, paddedPerm ℂ m (m ^ c) ∉ orbitClosure (detPoly ℂ (m ^ c + 1)) := by
  obtain ⟨c', hc', h⟩ := h
  obtain ⟨m₁, h⟩ := h 0
  obtain ⟨t, ht⟩ := exists_nat_gt (((4 * c + 10 : ℕ) / c' : ℝ) ^ (3 : ℕ))
  refine ⟨max m₁ (2 ^ (t + 1)), fun m hm hmem => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : 2 ^ (t + 1) ≤ m := le_trans (le_max_right _ _) hm
  have h2m : 2 ≤ m := le_trans (by rw [pow_succ]; have := Nat.one_le_two_pow (n := t); omega) hm2
  obtain ⟨k, _, _, happ⟩ := approximates_of_mem (Nat.le_self_pow (by omega) m) hmem
  have hb : Statement.Beyond c' m (49 * (m ^ c + 1) ^ 4) := (h k m hm1 _).2 (by norm_num) happ
  unfold Statement.Beyond at hb
  have hs : 49 * (m ^ c + 1) ^ 4 ≤ m ^ (4 * c + 10) := by
    have e1 : m ^ c + 1 ≤ 2 * m ^ c := by have := Nat.one_le_pow c m (by omega); omega
    calc 49 * (m ^ c + 1) ^ 4 ≤ 49 * (2 * m ^ c) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e1 4)
      _ = 784 * m ^ (4 * c) := by rw [mul_pow, ← pow_mul, mul_comm c 4]; ring
      _ ≤ 2 ^ 10 * m ^ (4 * c) := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ m ^ 10 * m ^ (4 * c) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2m 10)
      _ = m ^ (4 * c + 10) := by rw [← pow_add, add_comm]
  have hlog : (t : ℝ) ≤ Real.logb 2 m := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
    have : (2 : ℕ) ^ t ≤ m := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hm2
    exact_mod_cast this
  have hexp : ((4 * c + 10 : ℕ) : ℝ) ≤ c' * Real.logb 2 m ^ (1 / 3 : ℝ) := by
    have h0 : (0 : ℝ) ≤ ((4 * c + 10 : ℕ) : ℝ) / c' := by positivity
    have h1 : (((4 * c + 10 : ℕ) : ℝ) / c') ^ (3 : ℕ) ≤ Real.logb 2 m := ht.le.trans hlog
    have h2 : ((4 * c + 10 : ℕ) : ℝ) / c' ≤ Real.logb 2 m ^ (1 / 3 : ℝ) := by
      calc ((4 * c + 10 : ℕ) : ℝ) / c' = ((((4 * c + 10 : ℕ) : ℝ) / c') ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
        _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rw [div_le_iff₀ hc'] at h2
    linarith
  have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hle : ((49 * (m ^ c + 1) ^ 4 : ℕ) : ℝ) ≤ (m : ℝ) ^ (c' * Real.logb 2 m ^ (1 / 3 : ℝ)) := by
    calc ((49 * (m ^ c + 1) ^ 4 : ℕ) : ℝ) ≤ ((m ^ (4 * c + 10) : ℕ) : ℝ) := by exact_mod_cast hs
      _ = (m : ℝ) ^ ((4 * c + 10 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hm0 hexp
  exact absurd hb (not_lt.2 hle)

end Final

end MS
