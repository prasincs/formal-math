# How this was made

Written by Claude (Anthropic's AI system, in Claude Code) at the request of the repository owner, who set the goal and the safety rules. No human checked the mathematics; the Lean statement was read by Claude
against the paper.

**Time line (UTC).**
25 November 2026, 08:16 a group of Claude agents working on the single level conjecture found Problem 22 in the original version of Jukna's paper and proposed the graph `a c = b + d`.
08:22 the whole development (`Gap.lean`, one file, Lean 4.36.0) compiled. 09:27 axioms checked.
25–26 November: search for earlier work (see README); hand proof of the general form with norm graphs, reviewed by two Gemini models, written up as a paper.
26–27 November: `Gap.lean` (sha256 `1a0cf8f9…abf00`) split into this project's layout, the namespace renamed from `Gap` to `SingleLevelGap`, rebuilt, and checked with nanoda.

**Where the ideas come from.** See the README: the lower bound is Amano and Maruoka's, the graph and the upper-bound method are Jukna's. The Lean text is ours.

**Changes from `Gap.lean`.** The definitions the statements use moved, unchanged, to `SLGapStatement.lean`. One proof (`val_gate`) had to change: it restated the `match` inside
`Circ.val`, which only works in the same file; it now splits on the `match` instead. The OR-AND-OR lower bound at the end of `Gap.lean` is not used by the statements and was left out.

**Safety rules used.** No network in any build or check. Lean 4.36.0 and Mathlib `fc4f59e5` with its packages at the commits in `lake-manifest.json`, prebuilt in a container volume from an earlier
project; one file of the `batteries` checkout differs from its commit (a symlink stored as a text file, `docs/README.md`). lean4export `df81913e` (tag `v4.36.0-rc1`), built in the container.
nanoda `0da9f98f`, binary sha256 `d6b700d5…4811`, built from source earlier. A pattern scan of the Lean text (`sorry`, `native_decide`, `axiom`, `#eval`, `run_cmd`, `unsafe`, `implemented_by`, `macro`, `elab`) found nothing.

**What went wrong.**
* The first split broke `val_gate` (above); found by the build.
* The search for earlier work came after the proof.

**What was not done.** No Comparator run; no check on a second machine; no human review of the definitions.
