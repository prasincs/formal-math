# formal-math

Lean 4 proofs, one project per folder. Each project builds on its own, with its own toolchain and pins.

| Project | Statement | Rests on | Checked by |
|---|---|---|---|
| [orbit-closure](orbit-closure/) | for every `c ≥ 1` and large `m`, the padded `m × m` permanent is not in the orbit closure of the determinant of size `m ^ c + 1`, over ℂ (limits, Zariski closure, and projective `SL` form); its border determinantal complexity is superpolynomial | Anthropic's [vp-vnp](https://github.com/anthropics/formal-math/tree/main/vp-vnp) (an AI-written proof that no human mathematician has checked), Mathlib | Lean 4.33.1, nanoda |
| [single-level-gap](single-level-gap/) | an explicit graph on `n = 2·4^k` vertices (the graph `a c = b + d` over `GF(2^k)`, a clique on each side) whose edge function has monotone formulas with `n · k^O(1)` leaves but needs `n^(3/2) / 2^(7/2)` gates in every single-level circuit: an explicit `n^(1/2 - o(1))` gap, Jukna's Problem 22; and the single-level lower bound `|E(H)| / (4 (t-1)(s-1))` for every `(t, s)`-free `H` | Amano–Maruoka's lower bound and Jukna's upper-bound method (proved here, not imported), Mathlib | Lean 4.36.0, nanoda |

Read "checked" narrowly: a kernel accepted the proof of the statement as written in Lean. That the definitions say what is meant is for a reader to judge, and each project has one short
file for that. Most of the mathematics and the Lean text here is written by AI; each project's `PROCESS.md` says by whom, what is borrowed, and what went wrong.

How a project is laid out, and what it must have before it is listed: [docs/projects.md](docs/projects.md). Corrections, earlier work we missed, and doubts about a definition are welcome as issues.

Apache 2.0, see LICENSE and the NOTICE file of each project.
