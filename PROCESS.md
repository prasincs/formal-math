# How this was made

Written by Claude (Anthropic's AI system, in Claude Code) at the request of the repository owner, who set the goal and the safety rules. No human checked the mathematics.

**Time line (25 November 2026, UTC).**
12:46 the owner asked for the Mulmuley–Sohoni conjecture. The vp-vnp repository had been cloned earlier that day for reading; its paper says Remark N.6 is the one numbered statement without a Lean proof.
12:52 plan in seven pieces; power-series step proved. 13:04–13:16 vp-vnp rebuilt offline and checked with a second kernel. 13:11 limit step. 14:04 arc lemma. 14:11 determinant circuit. 14:17 the final theorem compiled. 14:22 second kernel, controls.
14:34 a search for earlier work, done only then, found the projects named in the README; Remark N.6 in its Laurent-series form had been formalized by others within the previous day.

**Where the ideas come from.** The lower bound and the statement that it implies the orbit-closure form: the authors of vp-vnp (and, independently, OpenAI's paper). Curve selection and Berkowitz's algorithm: textbook. Ours: doing the arc over a
large field of characteristic zero instead of ℂ (a generic line through the image point, Galois conjugation to hit the right point, Zariski's lemma for the rest of the parameters, then a Dedekind localization), and the Lean text.

**Safety rules used.** Sources were scanned for code that runs during a build before anything was built. Downloads were data, checked by hash or pinned commit: Lean 4.33.1 by the release digest (no build attestation exists), Mathlib and packages at the commits in the manifest.
Everything ran in containers without network.

**What went wrong.**
* The first tampered control for the second kernel was badly chosen: it swapped in a proof of the same statement, and was rightly accepted. Replaced by controls that change what is claimed.
* Copying git folders without their empty directories made the build tool try to clone again; there was no network, so it failed harmlessly.
* The scan of the sources is a pattern search, not a line-by-line reading.
* The search for prior work should have come first.

**What was not done.** No reading of the 73,000 lines of vp-vnp; no Comparator run; no check on a second machine; no human review.
