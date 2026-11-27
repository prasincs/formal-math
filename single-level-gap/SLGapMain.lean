/-
SPDX-License-Identifier: Apache-2.0
-/
import SLGapProof

/-- Amano–Maruoka's lower bound for single-level circuits, for every bipartite graph with no 4-cycle. -/
theorem single_level_lower : SingleLevelLower := fun m C H _ hC4 hs hf => SingleLevelGap.lower C H hC4 hs hf

/-- An explicit polynomial gap between single-level circuits and monotone formulas. -/
theorem single_level_gap : SingleLevelGap := fun k hk => SingleLevelGap.gap k hk

#print axioms single_level_lower
#print axioms single_level_gap
