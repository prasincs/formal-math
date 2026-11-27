/-
SPDX-License-Identifier: Apache-2.0
-/
import SLGapProof

/-- Amano–Maruoka's lower bound for single-level circuits, for every bipartite graph with no 4-cycle. -/
theorem single_level_lower : SingleLevelLower := fun m C H _ hC4 hs hf => SingleLevelGap.lower C H hC4 hs hf

/-- Lemma 2 of the paper: the lower bound for every `(t, s)`-free bipartite graph. -/
theorem single_level_lower_ts : SingleLevelLowerTS := fun t s m C H _ ht hs hfree hsg hf =>
  SingleLevelGap.lower2 C H t s ht hs hfree hsg hf

/-- An explicit polynomial gap between single-level circuits and monotone formulas. -/
theorem single_level_gap : SingleLevelGap := fun k hk => SingleLevelGap.gap k hk

#print axioms single_level_lower
#print axioms single_level_lower_ts
#print axioms single_level_gap
