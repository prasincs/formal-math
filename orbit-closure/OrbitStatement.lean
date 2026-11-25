/-
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# The statement

The definitions of the project `open-goat/pequalnp-proofs` (`lean/PEqualNP/Defs/Gct.lean`, copied unchanged) and the statement
that the padded permanent is not in the orbit closure of a determinant of polynomial size. Mathlib is the only import.
-/

namespace PEqualNP.Gct

open MvPolynomial

/-- The determinant of the `n × n` matrix of variables `X (i, j)`. -/
noncomputable def detPoly (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).det

/-- The permanent of the `n × n` matrix of variables `X (i, j)`. -/
noncomputable def permPoly (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).permanent

/-- `p` is the determinant of an `n × n` matrix whose entries are affine linear polynomials
(total degree at most one) in the variables of `p`. -/
def HasDetExpression {σ R : Type} [CommRing R] (p : MvPolynomial σ R) (n : ℕ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) (MvPolynomial σ R),
    (∀ i j, (A i j).totalDegree ≤ 1) ∧ A.det = p

/-- `p` is a coefficientwise limit of complex polynomials that have a determinantal expression
of size `n`. For finitely many variables the polynomials involved have degree at most `n`, so
this is the limit in the usual topology of a finite-dimensional complex vector space. -/
def HasBorderDetExpression {σ : Type} (p : MvPolynomial σ ℂ) (n : ℕ) : Prop :=
  ∃ q : ℕ → MvPolynomial σ ℂ, (∀ k, HasDetExpression (q k) n) ∧
    ∀ s, Filter.Tendsto (fun k => (q k).coeff s) Filter.atTop (nhds (p.coeff s))

/-- Linear change of variables: the polynomial `x ↦ f (g x)`, which replaces each variable
`X i` by `∑ j, g i j * X j`. -/
noncomputable def linSubst {ι R : Type} [Fintype ι] [CommRing R] (g : Matrix ι ι R)
    (f : MvPolynomial ι R) : MvPolynomial ι R :=
  MvPolynomial.bind₁ (fun i => ∑ j, MvPolynomial.C (g i j) * MvPolynomial.X j) f

/-- The orbit closure of a complex polynomial under invertible linear changes of variables: the
coefficientwise limits of sequences `linSubst (g k) f` with every `g k` invertible. The orbit
lies in the finite-dimensional space of forms of the degree of `f` (when `f` is homogeneous),
where this is the closure in the usual topology, which for orbits of `GL` equals the Zariski
closure used in GCT. -/
def orbitClosure {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial ι ℂ) :
    Set (MvPolynomial ι ℂ) :=
  {h | ∃ g : ℕ → Matrix.GeneralLinearGroup ι ℂ,
    ∀ s, Filter.Tendsto (fun k => (linSubst (g k : Matrix ι ι ℂ) f).coeff s) Filter.atTop
      (nhds (h.coeff s))}

/-- Where variable `(i, j)` of `perm_m` sits in the `(n + 1) × (n + 1)` grid: at
`(i + 1, j + 1)`. This is injective and avoids `(0, 0)` exactly when `m ≤ n`. -/
def padIndex (m n : ℕ) (p : Fin m × Fin m) : Fin (n + 1) × Fin (n + 1) :=
  (Fin.ofNat (n + 1) (p.1.val + 1), Fin.ofNat (n + 1) (p.2.val + 1))

/-- The padded permanent `x₀₀^(n+1-m) · perm_m`, homogeneous of degree `n + 1` in the
`(n + 1)²` variables of `det_{n+1}`. Meaningful when `m ≤ n`; statements assume it. -/
noncomputable def paddedPerm (R : Type) [CommRing R] (m n : ℕ) :
    MvPolynomial (Fin (n + 1) × Fin (n + 1)) R :=
  MvPolynomial.X (0, 0) ^ (n + 1 - m) * MvPolynomial.rename (padIndex m n) (permPoly R m)

end PEqualNP.Gct

/-- For every exponent `c ≥ 1` and all large `m`, the padded `m × m` permanent is not in the orbit closure of the determinant of
size `m ^ c + 1` (the polynomial-size form of the Mulmuley–Sohoni conjecture over `ℂ`; `L-gct-011` on pequalnp.com). -/
def PaddedPermanentNotMem : Prop :=
  ∀ c : ℕ, 1 ≤ c → ∃ m₀ : ℕ, ∀ m ≥ m₀,
    PEqualNP.Gct.paddedPerm ℂ m (m ^ c) ∉ PEqualNP.Gct.orbitClosure (PEqualNP.Gct.detPoly ℂ (m ^ c + 1))

namespace PEqualNP.Gct

open MvPolynomial

/-- The Zariski closure of the orbit: the polynomials at which every polynomial in the coefficients that vanishes on the orbit
vanishes too. It contains `orbitClosure f` (`MS.orbitClosure_subset_zariski`). -/
def zariskiOrbitClosure {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial ι ℂ) : Set (MvPolynomial ι ℂ) :=
  {h | ∀ Q : MvPolynomial (ι →₀ ℕ) ℂ,
    (∀ g : Matrix.GeneralLinearGroup ι ℂ, eval (fun s => (linSubst (g : Matrix ι ι ℂ) f).coeff s) Q = 0) →
      eval (fun s => h.coeff s) Q = 0}

/-- The projective form: `h` is a coefficientwise limit of scalar multiples of `x ↦ f (g_k x)` with `det g_k = 1`. For `h ≠ 0` this says
that the point `[h]` is a limit of points of the `SL`-orbit of `[f]` in projective space. -/
def projectiveSLClosure {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial ι ℂ) : Set (MvPolynomial ι ℂ) :=
  {h | ∃ (g : ℕ → Matrix.SpecialLinearGroup ι ℂ) (a : ℕ → ℂ),
    ∀ s, Filter.Tendsto (fun k => a k * (linSubst (g k : Matrix ι ι ℂ) f).coeff s) Filter.atTop (nhds (h.coeff s))}

end PEqualNP.Gct

/-- The same statement for the Zariski closure (stronger). -/
def PaddedPermanentNotMemZariski : Prop :=
  ∀ c : ℕ, 1 ≤ c → ∃ m₀ : ℕ, ∀ m ≥ m₀,
    PEqualNP.Gct.paddedPerm ℂ m (m ^ c) ∉ PEqualNP.Gct.zariskiOrbitClosure (PEqualNP.Gct.detPoly ℂ (m ^ c + 1))

/-- The same statement for limits of the `SL`-orbit in projective space. -/
def PaddedPermanentNotMemProjective : Prop :=
  ∀ c : ℕ, 1 ≤ c → ∃ m₀ : ℕ, ∀ m ≥ m₀,
    PEqualNP.Gct.paddedPerm ℂ m (m ^ c) ∉ PEqualNP.Gct.projectiveSLClosure (PEqualNP.Gct.detPoly ℂ (m ^ c + 1))
