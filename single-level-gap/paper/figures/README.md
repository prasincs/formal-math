# Figures

| File | Figure | Source |
|---|---|---|
| fig-setup.tex | 1: the graph G = H ∪ K_X ∪ K_Y and the shape of a single-level circuit | TikZ, hand-drawn |
| fig-charging.tex | 2: the charging step of Lemma 2 (case b ≥ s) | TikZ, hand-drawn |
| fig-upper.tex | 3: the monotone circuit of Lemma 3 | TikZ, hand-drawn |
| fig-gap.tex | 4: computed gap bound for norm graphs, t = 2, 3, 4 | pgfplots over gap-t{2,3,4}.dat |

The data files come from the `normgap` program (Rust, no dependencies):

    cd ../../normgap && cargo build --release
    for t in 2 3 4; do ./target/release/normgap dat $t 64 > ../paper/figures/gap-t$t.dat; done

Columns: k, log2 n, log2 of the Lemma 2 lower bound |E(H)|/(4(t-1)t!), log2 of the Lemma 3 circuit size,
their difference (`gapcirc`, plotted), and the same for the formula upper bound (`logub`, `gapformula`).
`normgap verify k t` checks the adjacency circuit against field arithmetic on all input pairs.
