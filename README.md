# formal-math

Lean 4 proofs, one project per folder. Each project builds on its own, with its own toolchain and pins.

| Project | Statement | Rests on | Checked by |
|---|---|---|---|
| [orbit-closure](orbit-closure/) | for every `c ≥ 1` and large `m`, the padded `m × m` permanent is not in the orbit closure of the determinant of size `m ^ c + 1`, over ℂ (limits, Zariski closure, and projective `SL` form) | Anthropic's [vp-vnp](https://github.com/anthropics/formal-math/tree/main/vp-vnp) (an AI-written proof that no human mathematician has checked), Mathlib | Lean 4.33.1, nanoda |

Read "checked" narrowly: a kernel accepted the proof of the statement as written in Lean. That the definitions say what is meant is for a reader to judge, and each project has one short
file for that. Most of the mathematics and the Lean text here is written by AI; each project's `PROCESS.md` says by whom, what is borrowed, and what went wrong.

How a project is laid out, and what it must have before it is listed: [docs/projects.md](docs/projects.md). Corrections, earlier work we missed, and doubts about a definition are welcome as issues.

Apache 2.0, see LICENSE and the NOTICE file of each project.
