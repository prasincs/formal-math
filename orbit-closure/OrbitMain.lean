/-
SPDX-License-Identifier: Apache-2.0
-/
import Solution
import Bridge

/-- The statement, from the theorem of vp-vnp on approximating circuits. -/
theorem padded_permanent_not_mem : PaddedPermanentNotMem := fun c hc => MS.bridge Solution.mainTheoremApprox c hc

#print axioms padded_permanent_not_mem
