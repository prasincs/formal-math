/-
SPDX-License-Identifier: Apache-2.0
-/
import Solution
import Bridge
import Variants

/-- The statement, from the theorem of vp-vnp on approximating circuits. -/
theorem padded_permanent_not_mem : PaddedPermanentNotMem := fun c hc => MS.bridge Solution.mainTheoremApprox c hc

/-- The same for the Zariski closure. -/
theorem padded_permanent_not_mem_zariski : PaddedPermanentNotMemZariski := MS.bridge_zariski Solution.mainTheoremApprox

/-- The same for limits of the `SL`-orbit in projective space. -/
theorem padded_permanent_not_mem_projective : PaddedPermanentNotMemProjective := MS.bridge_projective Solution.mainTheoremApprox

#print axioms padded_permanent_not_mem
#print axioms padded_permanent_not_mem_zariski
#print axioms padded_permanent_not_mem_projective
