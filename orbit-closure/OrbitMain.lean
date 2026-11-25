/-
SPDX-License-Identifier: Apache-2.0
-/
import Solution
import Bridge
import Variants
import BorderDet

/-- The statement, from the theorem of vp-vnp on approximating circuits. -/
theorem padded_permanent_not_mem : PaddedPermanentNotMem := fun c hc => MS.bridge Solution.mainTheoremApprox c hc

/-- The same for the Zariski closure. -/
theorem padded_permanent_not_mem_zariski : PaddedPermanentNotMemZariski := MS.bridge_zariski Solution.mainTheoremApprox

/-- The same for limits of the `SL`-orbit in projective space. -/
theorem padded_permanent_not_mem_projective : PaddedPermanentNotMemProjective := MS.bridge_projective Solution.mainTheoremApprox

/-- Border determinantal expressions of the permanent over `ℂ` have superpolynomial size. -/
theorem border_det_superpolynomial : BorderDetSuperpolynomial := MS.bridge_border Solution.mainTheoremApprox

/-- The cubic border bound, in the form of `L-gct-026`. -/
theorem border_det_cubic :
    ∃ (c m0 : ℕ), 0 < c ∧ ∀ m n : ℕ, m0 ≤ m → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → m ^ 3 ≤ c * n := by
  obtain ⟨m₀, h⟩ := border_det_superpolynomial 3
  exact ⟨1, m₀, one_pos, fun m n hm hb => by rw [one_mul]; exact (h m hm n hb).le⟩

#print axioms padded_permanent_not_mem
#print axioms padded_permanent_not_mem_zariski
#print axioms padded_permanent_not_mem_projective
#print axioms border_det_superpolynomial
#print axioms border_det_cubic
