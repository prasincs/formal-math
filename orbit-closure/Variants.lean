/-
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
import Statement
import OrbitStatement
import Bridge

/-!
# The Zariski closure, and the projective form

Mulmuley and Sohoni use the Zariski closure of the `SL`-orbit in projective space. `MS.bridge_zariski` and `MS.bridge_projective` give those forms.
-/

namespace MS

open MvPolynomial Filter PEqualNP.Gct

/-- The orbit closure by sequences lies in the Zariski closure. -/
theorem orbitClosure_subset_zariski {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial ι ℂ) :
    orbitClosure f ⊆ zariskiOrbitClosure f := by
  rintro h ⟨g, hg⟩ Q hQ
  have h1 : Tendsto (fun k => eval (fun s => (linSubst (g k : Matrix ι ι ℂ) f).coeff s) Q) atTop (nhds (eval (fun s => h.coeff s) Q)) :=
    ((MvPolynomial.continuous_eval Q).tendsto _).comp (tendsto_pi_nhds.2 hg)
  simp only [hQ] at h1
  exact (tendsto_nhds_unique h1 tendsto_const_nhds)

/-- Vanishing of the relations gives an algebra map from the image algebra. -/
theorem zariski_hom {κ D : Type} (Φ : D → MvPolynomial κ ℂ) (p : D → ℂ) (h : ∀ P : MvPolynomial D ℂ, aeval Φ P = 0 → aeval p P = 0) :
    ∃ e : (aeval (R := ℂ) Φ).range →ₐ[ℂ] ℂ, ∀ d, e ⟨Φ d, X d, by simp⟩ = p d := by
  let q : MvPolynomial D ℂ →ₐ[ℂ] MvPolynomial κ ℂ := aeval Φ
  have hk : ∀ P ∈ RingHom.ker q, aeval p P = 0 := fun P hP => h P ((RingHom.mem_ker).1 hP)
  let E := Ideal.quotientKerEquivRange q
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker q) (aeval p) hk).comp E.symm.toAlgHom, fun d => ?_⟩
  have : E (Ideal.Quotient.mk _ (X d)) = (⟨Φ d, X d, aeval_X Φ d⟩ : q.range) := by
    apply Subtype.ext
    exact aeval_X Φ d
  rw [← this]
  show (Ideal.Quotient.liftₐ (RingHom.ker q) (aeval p) hk) (E.symm (E _)) = _
  rw [AlgEquiv.symm_apply_apply]
  simp

theorem eval_aeval {κ D : Type} (a : κ → ℂ) (Φ : D → MvPolynomial κ ℂ) (P : MvPolynomial D ℂ) :
    eval a (aeval Φ P) = eval (fun d => eval a (Φ d)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [algebraMap_eq]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul_X x i hx => simp only [map_mul, hx, aeval_X, eval_X]

theorem eval_universal {ι A : Type} [Fintype ι] [CommRing A] (j : ℂ →+* A) (f : MvPolynomial ι ℂ) (U : MvPolynomial ι A) (G : Matrix ι ι A)
    (hU : U = linSubst G (map j f)) (E : A →+* ℂ) (hid : E.comp j = RingHom.id ℂ) (g : Matrix ι ι ℂ) (hg : G.map E = g) (s : ι →₀ ℕ) :
    E (U.coeff s) = (linSubst g f).coeff s := by
  rw [hU, coeff_universal E j hid, hg]

/-- A point of the Zariski closure is reached by power series. -/
theorem arc_of_zariski {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial ι ℂ) (PZ : MvPolynomial ι ℤ)
    (hmem : map (Int.castRingHom ℂ) PZ ∈ zariskiOrbitClosure f) :
    ∃ (k : Type) (_ : Field k) (_ : CharZero k) (γ : Matrix ι ι (LaurentSeries k)) (j : ℂ →+* LaurentSeries k) (Q' : MvPolynomial ι (PowerSeries k)),
      map (HahnSeries.ofPowerSeries ℤ k) Q' = linSubst γ (map j f) ∧ map (PowerSeries.constantCoeff (R := k)) Q' = map (Int.castRingHom k) PZ := by
  classical
  let G : Matrix ι ι (MvPolynomial (ι × ι) ℂ) := fun i j => X (i, j)
  obtain ⟨U, hU⟩ : ∃ U, U = linSubst G (map C f) := ⟨_, rfl⟩
  have hUg : ∀ (g : Matrix ι ι ℂ) s, eval (fun p : ι × ι => g p.1 p.2) (U.coeff s) = (linSubst g f).coeff s := by
    intro g s
    exact eval_universal C f U G hU (eval fun p : ι × ι => g p.1 p.2) (by ext; simp) g
      (by refine Matrix.ext fun x y => ?_; rw [Matrix.map_apply]; exact eval_X _) s
  have hpc : ∀ s, (map (Int.castRingHom ℂ) PZ).coeff s = ((PZ.coeff s : ℤ) : ℂ) := fun s => by rw [coeff_map]; rfl
  have rel : ∀ P : MvPolynomial U.support ℂ, aeval (fun s : U.support => U.coeff s.1) P = 0 → aeval (fun s : U.support => ((PZ.coeff s.1 : ℤ) : ℂ)) P = 0 := by
    intro P hP
    have h1 := hmem (rename (fun s : U.support => s.1) P) (by
      intro g
      rw [eval_rename]
      have h3 := eval_aeval (fun p : ι × ι => (g : Matrix ι ι ℂ) p.1 p.2) (fun s : U.support => U.coeff s.1) P
      rw [hP, map_zero] at h3
      have h4 : (fun s : U.support => eval (fun p : ι × ι => (g : Matrix ι ι ℂ) p.1 p.2) (U.coeff s.1))
          = (fun s => (linSubst (g : Matrix ι ι ℂ) f).coeff s) ∘ fun s : U.support => s.1 := by
        funext s
        exact hUg _ _
      rw [h4] at h3
      exact h3.symm)
    rw [eval_rename] at h1
    rw [MvPolynomial.aeval_eq_eval]
    have : ((fun s => (map (Int.castRingHom ℂ) PZ).coeff s) ∘ fun s : U.support => s.1) = fun s : U.support => ((PZ.coeff s.1 : ℤ) : ℂ) :=
      funext fun s => hpc s.1
    rw [this] at h1
    exact h1
  have out : ∀ s, s ∉ U.support → PZ.coeff s = 0 := by
    intro s hs
    have h1 := hmem (X s) (by
      intro g
      rw [eval_X, ← hUg, notMem_support_iff.1 hs, map_zero])
    rw [eval_X, hpc] at h1
    exact_mod_cast h1
  obtain ⟨e, he⟩ := zariski_hom (fun s : U.support => U.coeff s.1) (fun s => ((PZ.coeff s.1 : ℤ) : ℂ)) rel
  obtain ⟨k, ik, ck, ψ, hψ⟩ := arc (fun s : U.support => U.coeff s.1) (fun s => PZ.coeff s.1) e he
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
    · rw [map_zero, out s h, map_zero]

theorem bridge_zariski (h : Statement.MainTheoremApprox.{0}) : PaddedPermanentNotMemZariski := by
  intro c hc
  obtain ⟨m₀, h0⟩ := numerics h c hc
  exact ⟨m₀, fun m hm hmem => (h0 m hm).2 (approximates_of_arc (h0 m hm).1 (arc_of_zariski _ _ (by rw [padded_map]; exact hmem)))⟩

/-- Scaling the substitution scales the determinant by a power. -/
theorem linSubst_smul_det {ν : ℕ} (c : ℂ) (g : Matrix (Fin ν × Fin ν) (Fin ν × Fin ν) ℂ) :
    linSubst (c • g) (detPoly ℂ ν) = C (c ^ ν) * linSubst g (detPoly ℂ ν) := by
  unfold linSubst detPoly
  have key : ∀ g : Matrix (Fin ν × Fin ν) (Fin ν × Fin ν) ℂ, bind₁ (fun i => ∑ j, C (g i j) * X j) (Matrix.mvPolynomialX (Fin ν) (Fin ν) ℂ).det
      = (Matrix.of fun i j => ∑ x, C (g (i, j) x) * (X x : MvPolynomial (Fin ν × Fin ν) ℂ)).det := by
    intro g
    rw [AlgHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply, bind₁_X_right]
    rfl
  rw [key, key]
  have : (Matrix.of fun i j => ∑ x, C ((c • g) (i, j) x) * (X x : MvPolynomial (Fin ν × Fin ν) ℂ))
      = (C c : MvPolynomial (Fin ν × Fin ν) ℂ) • Matrix.of fun i j => ∑ x, C (g (i, j) x) * (X x : MvPolynomial (Fin ν × Fin ν) ℂ) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul, mul_assoc]
  rw [this, Matrix.det_smul, Fintype.card_fin, map_pow]

/-- A nonzero limit in projective space is a limit of the orbit of the general linear group. -/
theorem projective_subset {ν : ℕ} (hν : ν ≠ 0) {h : MvPolynomial (Fin ν × Fin ν) ℂ} (hne : h ≠ 0)
    (hmem : h ∈ projectiveSLClosure (detPoly ℂ ν)) : h ∈ orbitClosure (detPoly ℂ ν) := by
  classical
  obtain ⟨g, a, hg⟩ := hmem
  obtain ⟨s₀, hs₀⟩ := MvPolynomial.ne_zero_iff.1 hne
  have ev : ∀ᶠ k in atTop, a k ≠ 0 := by
    have h1 : ∀ᶠ k in atTop, a k * (linSubst (g k : Matrix (Fin ν × Fin ν) (Fin ν × Fin ν) ℂ) (detPoly ℂ ν)).coeff s₀ ≠ 0 :=
      (hg s₀).eventually_ne hs₀
    exact h1.mono fun k hk h0 => hk (by rw [h0, zero_mul])
  have root : ∀ z : ℂ, ∃ y : ℂ, y ^ ν = z := fun z => IsAlgClosed.exists_pow_nat_eq z (Nat.pos_of_ne_zero hν)
  choose rt hrt using root
  let u : ℕ → Matrix.GeneralLinearGroup (Fin ν × Fin ν) ℂ := fun k =>
    if hk : a k = 0 then 1 else
      Matrix.GeneralLinearGroup.mkOfDetNeZero (rt (a k) • (g k : Matrix (Fin ν × Fin ν) (Fin ν × Fin ν) ℂ)) (by
        rw [Matrix.det_smul, (g k).2, mul_one]
        refine pow_ne_zero _ fun h0 => hk ?_
        rw [← hrt (a k), h0, zero_pow hν])
  refine ⟨u, fun s => (hg s).congr' ?_⟩
  filter_upwards [ev] with k hk
  have hu : (u k : Matrix (Fin ν × Fin ν) (Fin ν × Fin ν) ℂ) = rt (a k) • (g k : Matrix (Fin ν × Fin ν) (Fin ν × Fin ν) ℂ) := by
    simp only [u, dif_neg hk]; rfl
  rw [hu, linSubst_smul_det, hrt, coeff_C_mul]

theorem padded_ne_zero {m n : ℕ} (hmn : m ≤ n) : paddedPerm ℂ m n ≠ 0 := by
  intro h
  have h1 := unpad_padded ℂ hmn
  rw [h, map_zero] at h1
  have h2 : eval (fun p : Fin m × Fin m => if p.1 = p.2 then (1 : ℂ) else 0) (permPoly ℂ m) = 1 := by
    rw [permPoly, Matrix.permanent]
    simp only [map_sum, map_prod, Matrix.mvPolynomialX_apply, eval_X]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin m))]
    · simp
    · intro σ _ hσ
      obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
        by_contra hno
        push Not at hno
        exact hσ (Equiv.ext hno)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    · intro hno; exact absurd (Finset.mem_univ _) hno
  rw [← h1, map_zero] at h2
  exact zero_ne_one h2

theorem bridge_projective (h : Statement.MainTheoremApprox.{0}) : PaddedPermanentNotMemProjective := by
  intro c hc
  obtain ⟨m₀, h0⟩ := numerics h c hc
  refine ⟨m₀, fun m hm hmem => (h0 m hm).2 (approximates_of_mem (h0 m hm).1 ?_)⟩
  exact projective_subset (Nat.succ_ne_zero _) (padded_ne_zero (h0 m hm).1) hmem

end MS
