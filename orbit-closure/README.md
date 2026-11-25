# The orbit-closure form of the Mulmuley–Sohoni conjecture, from vp-vnp, in Lean 4

For every `c ≥ 1` and all large `m`, the padded `m × m` permanent is not in the orbit closure of the determinant of size `m ^ c + 1`, over ℂ.

```lean
theorem padded_permanent_not_mem :
    ∀ c : ℕ, 1 ≤ c → ∃ m₀ : ℕ, ∀ m ≥ m₀, paddedPerm ℂ m (m ^ c) ∉ orbitClosure (detPoly ℂ (m ^ c + 1))
```

`orbitClosure f` is the set of coefficientwise limits of sequences `x ↦ f (g_k x)` with every `g_k` invertible. Two more forms are proved, so that the choice of closure does not matter:

| Theorem | Closure |
|---|---|
| `padded_permanent_not_mem` | limits of the `GL`-orbit (this is `L-gct-011` on pequalnp.com) |
| `padded_permanent_not_mem_zariski` | Zariski closure of the `GL`-orbit; contains the first one (`MS.orbitClosure_subset_zariski`) |
| `padded_permanent_not_mem_projective` | limits of scalar multiples of the `SL`-orbit, that is, of the `SL`-orbit in projective space |

The file to read is [OrbitStatement.lean](OrbitStatement.lean) (imports only Mathlib).

**The lower bound is not ours.** It is the theorem on approximating circuits (`mainTheoremApprox`) of Anthropic's
[vp-vnp](https://github.com/anthropics/formal-math/tree/main/vp-vnp), whose authors say that no human mathematician has checked it. This repository is the
step from that theorem to the orbit closure. If that theorem is wrong, so is this one. Nothing here is about P versus NP.

## What is here

| File | Content |
|---|---|
| `OrbitStatement.lean` | definitions (copied unchanged from [open-goat/pequalnp-proofs](https://github.com/open-goat/pequalnp-proofs), `lean/PEqualNP/Defs/Gct.lean`) and the statement |
| `Bridge.lean` | `MS.bridge : Statement.MainTheoremApprox → PaddedPermanentNotMem` |
| `Variants.lean` | the Zariski and the projective form |
| `OrbitMain.lean` | the three theorems, from `Solution.mainTheoremApprox` |
| `OrbitChallenge.lean`, `comparator.json` | the statements with `sorry`, for comparison tools |
| `verify/` | second-kernel check with tampered controls (run by `../tools/nanoda_check.py`), and the logs |
| `PROCESS.md` | how it was made, by whom, and what went wrong on the way |

Steps of `Bridge.lean`: a limit of the orbit gives an algebra map from the algebra of coefficient polynomials (`limit_hom`); the limit is reached by an arc of Laurent
series over some field of characteristic zero (`arc`); a determinant of size `n` costs at most `40 n⁴ + 4` gates beyond its entries (`cost_det`, Berkowitz); undo the padding and
count, at most `49 (n + 1)⁴` gates (`approximates_of_mem`); compare (`bridge`). The arc does not need to be over ℂ, because the bound holds over every field; this replaces curve selection over ℂ.

## Check it

With [elan](https://github.com/leanprover/elan), in this folder:

    lake exe cache get
    lake build

(We built offline with the same pins; this online route has not been run by us.) The build fetches vp-vnp at commit `11b6c7e3` and Mathlib at `0df444a3`, and prints the axioms of the theorems: `propext, Classical.choice, Quot.sound`.
Checked here on 2026-11-25: a clean offline build (9,036 jobs), and the independent kernel [nanoda](https://github.com/ammkrn/nanoda_lib) (80,084 declarations, no error; thirteen
tampered copies all rejected, each for a type error). See `verify/`. The comparator configuration has not been run.

## The conjecture, and which part of it this is

Mulmuley and Sohoni (*Geometric complexity theory I*, SIAM J. Comput. 31 (2002) 496–526) work with the `SL`-orbit of the determinant in projective space and its Zariski closure.
A readable account is K. W. Regan, [*Understanding the Mulmuley–Sohoni approach to P vs. NP*](https://cse.buffalo.edu/faculty/regan/papers/pdf/Reg02MSFD.pdf) (2002); in its words (Conjecture 3.2), the determinant is
"not padded-permanent-stable under any polynomial (or sub-exponential) amount of padding".

* **Covered:** polynomial padding, `n = m ^ c` for every `c`, for all large `m`.
* **Not covered:** sub-exponential padding. vp-vnp's bound would give `n` up to `m ^ (c' (log m)^(1/3))`; not done here, and still far from sub-exponential.
* **Closures.** For a nonzero form the closures agree: in projective space the Zariski and the classical closure of an orbit coincide (Regan, Section 2 and the proof of Proposition 3.1), and scalars can be moved into the substitution. We do not use that fact; the
  three forms are proved separately in Lean. The Zariski form is in affine space, for the `GL`-orbit, which contains all scalar multiples of the `SL`-orbit.
* **Padding.** Regan and GCT I use a variable outside the corner, `y_mm`; here it is `x_00` and the permanent sits at indices from 1. This is a renaming of variables, under which the determinant changes at most by a sign.
* **Method.** Nothing from the geometric programme (stability, obstructions) is used.

## Related work (looked for on 2026-11-25; corrections welcome)

* **Anthropic, vp-vnp** (23 Nov 2026): the lower bound; Remark N.6 states the consequence for determinantal complexity and orbit closures and says it is not formalized.
* **OpenAI, [VP and VNP are different](https://github.com/openai/math/tree/main/preprints/VP-and-VNP-are-different-November-23-2026)** (23 Nov 2026), Corollary 1.2: states that the padded permanent
  is excluded from the determinant orbit closure, for padding up to `exp(c (log m)^(5/4))`. Their Lean scope notes say the border bound for the permanent is not formalized.
* **[agentcarlosian/vp-vnp-lab](https://github.com/agentcarlosian/vp-vnp-lab/tree/main/remark-n6-lean)** (24–25 Nov 2026): Remark N.6 in Lean, unconditional, for determinants approximated over Laurent series, every characteristic
  but two, size `m ^ (c (log m)^(1/3))`. Earlier than this repository, and quantitatively stronger; it does not treat limits of the orbit or the padding.
* **[carlostoledo1891/cert-machine](https://github.com/carlostoledo1891/cert-machine/tree/main/corpus/vp-vnp/lean/n6)** (24 Nov 2026): Remark N.6 from the main theorem as a hypothesis.
* Independent checks of vp-vnp itself: 2opremio/vp-vnp-statement-check, Horace-Maxwell/vp-vnp-lean-independent-verification, kim-em/vp-vnp (newer Lean).

What we did not find elsewhere is the orbit-closure form with limits over ℂ. No code from the projects in this list other than vp-vnp itself is used. The idea of the bridge is classical (curve selection; Berkowitz 1984).

## Limits

* Two kernels say the proof is valid for these definitions. That the definitions say what experts mean was read, not machine-checked.
* Polynomial padding only, see above.
* No human mathematician has reviewed this repository.

Apache 2.0, see [LICENSE](../LICENSE) and [NOTICE](NOTICE).
