//! normgap: numbers and checks for the explicit single-level gap on norm graphs.
//!
//! Graph: q = 2^k, F = GF(q^t) (m = k t bits), X = Y = F, x ~ y iff Norm(x + y) = 1,
//! Norm(z) = z^(1 + q + ... + q^(t-1)) (Kollar-Ronyai-Szabo norm graph, bipartite form).
//! G = H plus a clique on each side. f_G(x) = OR over edges of x_u x_v.
//!
//! Upper bound: f_G = T2(X) | T2(Y) | (OR X & OR Y & phi), where phi is a negation-normal-form
//! formula for "Norm(x + y) = 1" over the 2m address bits, and every literal "bit j of the
//! X-vertex is e" is replaced by s_j^e = OR of the N/2 X-vertices with that bit. This tool
//! builds phi as a dual-rail AND/OR circuit, verifies it against direct field arithmetic on all
//! (x, y) for small m, and counts the leaves of its formula unfolding exactly (as f64).
//!
//! Lower bound (claim B, hand argument): every single-level circuit for f_G has at least
//! |H| / (4 (t-1) (s-1)) gates when H has no K_{t,s} with t vertices in X. For t = 2 this is the
//! Lean-proved |H| / 4 bound. The tool computes s - 1 = max common neighbourhood of t X-vertices
//! exactly for small cases (sum graph: translate so one vertex is 0).

use std::env;

// ---------------- GF(2^m), m <= 64 ----------------
fn pmulmod(mut a: u128, mut b: u128, p: u128, m: u32) -> u128 {
    let mut r = 0u128;
    while b != 0 {
        if b & 1 == 1 {
            r ^= a;
        }
        b >>= 1;
        a <<= 1;
        if a >> m & 1 == 1 {
            a ^= p;
        }
    }
    r
}
fn pgcd(mut a: u128, mut b: u128) -> u128 {
    let deg = |x: u128| 127 - x.leading_zeros() as i32;
    while b != 0 {
        while a != 0 && deg(a) >= deg(b) {
            a ^= b << (deg(a) - deg(b));
        }
        std::mem::swap(&mut a, &mut b);
    }
    a
}
fn x_pow_2pow(e: u32, p: u128, m: u32) -> u128 {
    let mut r = 2u128; // x
    for _ in 0..e {
        r = pmulmod(r, r, p, m);
    }
    r
}
fn irreducible(p: u128, m: u32) -> bool {
    if x_pow_2pow(m, p, m) != 2 {
        return false;
    }
    let mut r = 2;
    let mut mm = m;
    while mm > 1 {
        while mm % r != 0 {
            r += 1;
        }
        let h = x_pow_2pow(m / r, p, m) ^ 2;
        if pgcd(p, h) != 1 {
            return false;
        }
        while mm % r == 0 {
            mm /= r;
        }
    }
    true
}
fn find_irreducible(m: u32) -> u128 {
    // lowest-weight first: trinomials, then pentanomials
    let top = 1u128 << m;
    for a in 1..m {
        let p = top | 1 << a | 1;
        if irreducible(p, m) {
            return p;
        }
    }
    for a in 1..m {
        for b in 1..a {
            for c in 1..b {
                let p = top | 1 << a | 1 << b | 1 << c | 1;
                if irreducible(p, m) {
                    return p;
                }
            }
        }
    }
    panic!("no irreducible of degree {m}")
}

struct Field {
    m: u32,
    p: u128,
}
impl Field {
    fn mul(&self, a: u128, b: u128) -> u128 {
        pmulmod(a, b, self.p, self.m)
    }
    fn pow2k(&self, mut a: u128, e: u32) -> u128 {
        for _ in 0..e {
            a = self.mul(a, a);
        }
        a
    }
    fn norm(&self, z: u128, k: u32, t: u32) -> u128 {
        let mut r = 1u128;
        let mut c = z;
        for _ in 0..t {
            r = self.mul(r, c);
            c = self.pow2k(c, k);
        }
        r
    }
}

// ---------------- dual-rail NNF circuit with formula leaf counts ----------------
#[derive(Clone, Copy)]
enum Gate {
    Lit(u32, bool),
    And(usize, usize),
    Or(usize, usize),
}
#[derive(Clone, Copy)]
enum W {
    C(bool),
    R(usize, usize), // (positive rail, negative rail)
}
struct Circ {
    g: Vec<Gate>,
    leaves: Vec<f64>,
}
impl Circ {
    fn push(&mut self, g: Gate) -> usize {
        let l = match g {
            Gate::Lit(..) => 1.0,
            Gate::And(a, b) | Gate::Or(a, b) => self.leaves[a] + self.leaves[b],
        };
        self.g.push(g);
        self.leaves.push(l);
        self.g.len() - 1
    }
    fn input(&mut self, v: u32) -> W {
        let p = self.push(Gate::Lit(v, true));
        let n = self.push(Gate::Lit(v, false));
        W::R(p, n)
    }
    fn not(&self, a: W) -> W {
        match a {
            W::C(b) => W::C(!b),
            W::R(p, n) => W::R(n, p),
        }
    }
    fn and(&mut self, a: W, b: W) -> W {
        match (a, b) {
            (W::C(false), _) | (_, W::C(false)) => W::C(false),
            (W::C(true), x) | (x, W::C(true)) => x,
            (W::R(ap, an), W::R(bp, bn)) => {
                let p = self.push(Gate::And(ap, bp));
                let n = self.push(Gate::Or(an, bn));
                W::R(p, n)
            }
        }
    }
    fn or(&mut self, a: W, b: W) -> W {
        let (na, nb) = (self.not(a), self.not(b));
        let r = self.and(na, nb);
        self.not(r)
    }
    fn xor(&mut self, a: W, b: W) -> W {
        match (a, b) {
            (W::C(c), x) | (x, W::C(c)) => {
                if c {
                    self.not(x)
                } else {
                    x
                }
            }
            _ => {
                let nb = self.not(b);
                let na = self.not(a);
                let t1 = self.and(a, nb);
                let t2 = self.and(na, b);
                self.or(t1, t2)
            }
        }
    }
    fn reduce(&mut self, mut v: Vec<W>, op: fn(&mut Circ, W, W) -> W, unit: bool) -> W {
        if v.is_empty() {
            return W::C(unit);
        }
        while v.len() > 1 {
            let mut nv = vec![];
            for ch in v.chunks(2) {
                nv.push(if ch.len() == 2 { op(self, ch[0], ch[1]) } else { ch[0] });
            }
            v = nv;
        }
        v[0]
    }
    /// gates (not literals) in the cone of `out`
    fn cone_gates(&self, out: usize) -> usize {
        let mut seen = vec![false; out + 1];
        seen[out] = true;
        let mut cnt = 0;
        for i in (0..=out).rev() {
            if !seen[i] {
                continue;
            }
            match self.g[i] {
                Gate::Lit(..) => {}
                Gate::And(a, b) | Gate::Or(a, b) => {
                    cnt += 1;
                    seen[a] = true;
                    seen[b] = true;
                }
            }
        }
        cnt
    }
    fn eval(&self, out: usize, inp: &[bool]) -> bool {
        let mut val = vec![false; out + 1];
        for i in 0..=out {
            val[i] = match self.g[i] {
                Gate::Lit(v, pol) => inp[v as usize] == pol,
                Gate::And(a, b) => val[a] && val[b],
                Gate::Or(a, b) => val[a] || val[b],
            };
        }
        val[out]
    }
}

fn build_phi(f: &Field, k: u32, t: u32) -> (Circ, W) {
    let m = f.m as usize;
    let mut c = Circ { g: vec![], leaves: vec![] };
    let x: Vec<W> = (0..m).map(|i| c.input(i as u32)).collect();
    let y: Vec<W> = (0..m).map(|i| c.input((m + i) as u32)).collect();
    let z: Vec<W> = (0..m).map(|i| c.xor(x[i], y[i])).collect();
    // conjugates z^(q^i): linear maps
    let mut conj = vec![z.clone()];
    for i in 1..t {
        let imgs: Vec<u128> = (0..m).map(|j| f.pow2k(1u128 << j, k * i)).collect();
        let w: Vec<W> = (0..m)
            .map(|r| {
                let terms: Vec<W> = (0..m).filter(|&j| imgs[j] >> r & 1 == 1).map(|j| z[j]).collect();
                c.reduce(terms, Circ::xor, false)
            })
            .collect();
        conj.push(w);
    }
    // x^d mod p for d < 2m - 1
    let red: Vec<u128> = (0..2 * m - 1)
        .map(|d| {
            let mut r = 1u128;
            for _ in 0..d {
                r = f.mul(r, 2);
            }
            r
        })
        .collect();
    let mul = |c: &mut Circ, a: &Vec<W>, b: &Vec<W>| -> Vec<W> {
        let mut prods = vec![vec![W::C(false); m]; m];
        for j in 0..m {
            for l in 0..m {
                prods[j][l] = c.and(a[j], b[l]);
            }
        }
        (0..m)
            .map(|r| {
                let mut terms = vec![];
                for j in 0..m {
                    for l in 0..m {
                        if red[j + l] >> r & 1 == 1 {
                            terms.push(prods[j][l]);
                        }
                    }
                }
                c.reduce(terms, Circ::xor, false)
            })
            .collect()
    };
    // balanced product tree of the t conjugates
    let mut lev = conj;
    while lev.len() > 1 {
        let mut nl = vec![];
        let mut i = 0;
        while i < lev.len() {
            if i + 1 < lev.len() {
                let p = mul(&mut c, &lev[i], &lev[i + 1]);
                nl.push(p);
            } else {
                nl.push(lev[i].clone());
            }
            i += 2;
        }
        lev = nl;
    }
    let nm = &lev[0];
    let lits: Vec<W> = (0..m).map(|r| if r == 0 { nm[0] } else { c.not(nm[r]) }).collect();
    let out = c.reduce(lits, Circ::and, true);
    (c, out)
}

fn max_common(f: &Field, k: u32, t: u32) -> (u64, usize) {
    // H: x ~ y iff Norm(x + y) = 1. Common nbrs of {x_1..x_t} = translate x_1 to 0:
    // |{z : Norm(z + a_i) = 1 for all i}| with a_1 = 0, a_i distinct nonzero.
    let n = 1usize << f.m;
    let words = (n + 63) / 64;
    let mut s1 = vec![0u64; words]; // S = {z : Norm(z) = 1}
    let mut deg = 0u64;
    for z in 0..n {
        if f.norm(z as u128, k, t) == 1 {
            s1[z / 64] |= 1 << (z % 64);
            deg += 1;
        }
    }
    // shifted set S + a = {z : Norm(z + a) = 1} = {s + a}
    let shift = |a: usize| -> Vec<u64> {
        let mut v = vec![0u64; words];
        for z in 0..n {
            if s1[z / 64] >> (z % 64) & 1 == 1 {
                let w = z ^ a;
                v[w / 64] |= 1 << (w % 64);
            }
        }
        v
    };
    let shifts: Vec<Vec<u64>> = (0..n).map(shift).collect();
    let mut best = 0usize;
    fn rec(i: usize, t: usize, start: usize, n: usize, cur: &Vec<u64>, shifts: &Vec<Vec<u64>>, best: &mut usize) {
        let cnt: usize = cur.iter().map(|w| w.count_ones() as usize).sum();
        if cnt <= *best && i < t {
            // cannot exceed best by intersecting more
            if i > 0 {
                return;
            }
        }
        if i == t {
            *best = (*best).max(cnt);
            return;
        }
        for a in start..n {
            let nx: Vec<u64> = cur.iter().zip(&shifts[a]).map(|(x, y)| x & y).collect();
            rec(i + 1, t, a + 1, n, &nx, shifts, best);
        }
    }
    rec(1, t as usize, 1, n, &s1, &shifts, &mut best);
    (deg, best)
}

fn fact(t: u32) -> f64 {
    (1..=t).map(|x| x as f64).product()
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("table");
    match mode {
        "verify" => {
            // verify phi on all (x, y) and the K_{t,s} statistic, small cases
            let k: u32 = args[2].parse().unwrap();
            let t: u32 = args[3].parse().unwrap();
            let m = k * t;
            let f = Field { m, p: find_irreducible(m) };
            let (c, out) = build_phi(&f, k, t);
            let op = match out {
                W::R(p, _) => p,
                _ => panic!("constant phi"),
            };
            let n = 1usize << m;
            let mut bad = 0u64;
            let mut ones = 0u64;
            let mut inp = vec![false; 2 * m as usize];
            for x in 0..n {
                for y in 0..n {
                    for i in 0..m as usize {
                        inp[i] = x >> i & 1 == 1;
                        inp[m as usize + i] = y >> i & 1 == 1;
                    }
                    let want = f.norm((x ^ y) as u128, k, t) == 1;
                    let got = c.eval(op, &inp);
                    if want {
                        ones += 1;
                    }
                    if want != got {
                        bad += 1;
                    }
                }
            }
            println!(
                "verify k={k} t={t} m={m} p={:#x}: pairs={} edges={} mismatches={} phi_leaves={} gates={}",
                f.p, n * n, ones, bad, c.leaves[op], c.g.len()
            );
            let (deg, mc) = max_common(&f, k, t);
            println!(
                "  degree={deg} (expected (q^t-1)/(q-1)={}), max common nbrs of {t} X-vertices = {mc} (KRS bound t! = {})",
                ((1u64 << m) - 1) / ((1u64 << k) - 1),
                fact(t)
            );
        }
        _ => {
            // table of log2 sizes: lower bound vs formula, using s - 1 = t! (KRS)
            let t: u32 = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(3);
            let kmax: u32 = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(64 / t);
            // "dat": whitespace table for pgfplots (paper figure); "table": human-readable
            let dat = mode == "dat";
            if dat {
                println!("k logn loglb logubc gapcirc logub gapformula");
            } else {
                println!("t={t}: N=q^t per side, n=2N; LB=|H|/(4(t-1)t!), UB=formula leaves; all log2");
                println!("{:>3} {:>4} {:>8} {:>8} {:>8} {:>10} {:>8} {:>8} {:>9} {:>10} {:>8}", "k", "m", "log2 n", "log2|H|", "log2 LB", "log2 phi", "log2 UB", "gap", "phi gates", "log2 UBcirc", "gapcirc");
            }
            for k in 1..=kmax {
                let m = k * t;
                if m > 64 {
                    break;
                }
                let f = Field { m, p: find_irreducible(m) };
                let (c, out) = build_phi(&f, k, t);
                let (phi, pg) = match out {
                    W::R(p, _) => (c.leaves[p], c.cone_gates(p)),
                    _ => (0.0, 0),
                };
                let nn = (2f64).powi(m as i32);
                let deg = ((2f64).powi(m as i32) - 1.0) / ((2f64).powi(k as i32) - 1.0);
                let edges = nn * deg;
                let lb = edges / (4.0 * (t as f64 - 1.0) * fact(t));
                let ub = nn / 2.0 * phi + 2.0 * nn + 2.0 * m as f64 * nn;
                // circuit: 2m sums of N/2 letters per side (N/2 - 1 gates each), OR X = s_0^0 | s_0^1,
                // T2 = m ANDs + (m-1) ORs per side, phi gates, two ANDs and two final ORs
                let ubc = 2.0 * (2.0 * m as f64 * (nn / 2.0 - 1.0) + 1.0 + (2 * m - 1) as f64) + pg as f64 + 4.0;
                if dat {
                    println!(
                        "{} {:.3} {:.3} {:.3} {:.3} {:.3} {:.3}",
                        k,
                        (2.0 * nn).log2(),
                        lb.log2(),
                        ubc.log2(),
                        (lb / ubc).log2(),
                        ub.log2(),
                        (lb / ub).log2()
                    );
                    continue;
                }
                println!(
                    "{:>3} {:>4} {:>8.2} {:>8.2} {:>8.2} {:>10.2} {:>8.2} {:>8.2} {:>9} {:>10.2} {:>8.2}",
                    k,
                    m,
                    (2.0 * nn).log2(),
                    edges.log2(),
                    lb.log2(),
                    phi.log2(),
                    ub.log2(),
                    (lb / ub).log2(),
                    pg,
                    ubc.log2(),
                    (lb / ubc).log2()
                );
            }
        }
    }
}
