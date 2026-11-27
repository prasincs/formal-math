# An explicit gap for single-level monotone circuits, in Lean 4

Over `GF(2^k)`, let `X = Y = GF(2^k)^2` (so `N = 4^k` vertices on each side), join `(a, b) ∈ X` to `(c, d) ∈ Y` when `a c = b + d`, and add all edges inside `X` and inside `Y`.
The edge function of this graph, `OR` of `x_u ∧ x_v` over its edges, has a monotone formula with at most `N (8k + 2 + 8k(k^2+2)^2)` leaves, yet every single-level
monotone circuit for it (no AND gate below another AND gate) has at least `8^k / 4 = N^(3/2) / 4` gates. With `n = 2N` vertices this is a gap of `n^(1/2 - o(1))`, for an explicit graph.

```lean
theorem single_level_gap : ∀ k : ℕ, 0 < k →
    Rep (4 ^ k * (8 * k + 2 + 8 * k * (k ^ 2 + 2) ^ 2)) (satf (Hr (F := GaloisField 2 k))) ∧
    ∀ (m : ℕ) (C : Circ (GaloisField 2 k × GaloisField 2 k) (GaloisField 2 k × GaloisField 2 k) m), C.single →
      (∀ x, C.val x C.out = true ↔ satf Hr x) → 8 ^ k ≤ 4 * m
```

Also proved, for every finite bipartite graph `H` between `X` and `Y` and all `t, s ≥ 2`: if no `t` vertices of `X` have
`s` common neighbours, every single-level circuit for `H` plus a clique on each side has at least
`|E(H)| / (4 (t - 1) (s - 1))` gates (`single_level_lower_ts`, Lemma 2 of the paper). The case `t = s = 2`, graphs with no
4-cycle, is `single_level_lower`.

```lean
theorem single_level_lower_ts : ∀ {X Y : Type} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] (t s m : ℕ)
    (C : Circ X Y m) (H : X → Y → Prop) [DecidablePred fun p : X × Y => H p.1 p.2],
    2 ≤ t → 2 ≤ s → (∀ (A : Finset X) (B : Finset Y), t ≤ A.card → s ≤ B.card → ∃ a ∈ A, ∃ b ∈ B, ¬ H a b) →
    C.single → (∀ x, C.val x C.out = true ↔ satf H x) →
    (Finset.univ.filter fun p : X × Y => H p.1 p.2).card ≤ 4 * (t - 1) * (s - 1) * m
```

The file to read is [SLGapStatement.lean](SLGapStatement.lean) (imports only Mathlib): circuits with fan-in two and no constants (`Circ`, `Circ.val`), AND-free wires and single-level circuits,
the edge function `satf`, monotone formulas and their leaf count (`Fm`, `Rep`), the relation `Hr`, and the two statements.

## What is ours

**The mathematics is mostly not ours.** The lower bound for graphs with no 4-cycle is Amano and Maruoka's (*Algorithmica* 46, 2006; ISAAC 2004), which Jukna extended
(*Disproving the single level conjecture*, SIAM J. Comput. 36(1), 2006, Lemma 3.13). The graph `a c = b + d` is the sum-product graph (Jukna, *Boolean Function Complexity*, 2012, Example 7.5).
The upper bound replaces address bits by ORs of variables, Jukna's method in the same paper. What is ours: the observation that these together give an explicit graph, which Jukna asked for as Problem 22
of the original ECCC version of his paper (TR05-021, February 2005), and the Lean text. A paper with the general form (norm graphs, gap `n^(1 - 1/t - o(1))` for every fixed `t`, proved by hand, not in Lean)
is in [paper/](paper/); see below.

## Earlier work

Searched 25–26 November 2026, after the proof. Read: the original TR05-021 (February 2005), its Revision 2 and Comment 1, and the author's copy of the SIAM version; Amano–Maruoka (Algorithmica);
Jukna's 2012 book (by search of the whole text) and his 2013 survey chapter; Krapivin, Przybocki and Subercaseaux (arXiv 2603.28954, 2026), who separate single-level circuits for the threshold-2 function
by a lower-order term only; the forward citations of the SIAM, Algorithmica and CPC papers on Semantic Scholar (by title). None states an explicit graph with a polynomial gap. Problem 22 is absent from
Revision 2 and the journal version, without comment. Not read: Revision 1 (downloaded; no extractable text), Lenz and Wegener (TCS 1991), Pudlák–Rödl–Savický (1988).

## Limits

* Only `t = 2`. The norm-graph version needs the Kollár–Rónyai–Szabó theorem, which is not in Mathlib.
* The upper bound is a formula bound, so the theorem gives the gap against formulas and therefore also against circuits; the circuit bound `O(n log n)` of the paper is not formalized.
* For norm graphs, the `(t, t! + 1)`-freeness (Kollár–Rónyai–Szabó) and the size of the norm circuit are not formalized, so the
  gap `n^(1 - 1/t - o(1))` is proved here only through its lower-bound half.
* Circuits here have no constants; the paper's lower bound assumes the same.

## Checking it

    lake build                  # Lean 4.36.0, Mathlib fc4f59e5 (its v4.36.0 release)

`SLGapMain.lean` prints the axioms of the three theorems: `propext`, `Classical.choice`, `Quot.sound`. Second kernel: nanoda checked the export of the three theorems (33,301 declarations) and rejected
all 16 tampered copies in `verify/nanoda.json`, each of which changes what is claimed; see `verify/nanoda.log`. How it was made: [PROCESS.md](PROCESS.md).

## The paper

[paper/single-level-gap.tex](paper/single-level-gap.tex) (draft, open items marked TODO): *An explicit polynomial gap between single-level and general monotone circuits*,
by Prasanna Gautam. For every fixed `t ≥ 2`, bipartite norm graphs with a clique on each side give `C₁(f_G)/C(f_G) = n^(1 - 1/t - o(1))`, also against monotone formulas;
the case `t = 2` is the Lean theorem above. Appendix A says what AI assistants did and how their output was checked.

The workflow `.github/workflows/single-level-gap-paper.yml` builds [normgap/](normgap/) (Rust, no dependencies), checks its adjacency circuit against field arithmetic
on small fields, regenerates the data of Figure 4 and fails if it differs from `paper/figures/gap-t*.dat`, then compiles the PDF; download it from the workflow run, or from a
release for tags `single-level-gap-v*`. The paper and its figures are under CC BY 4.0 ([paper/LICENSE](paper/LICENSE)); everything else here is under Apache 2.0.
