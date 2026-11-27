/-
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-! # Single-level circuits: the definitions and the two statements

Read this file to check that the statements say what is meant. It imports Mathlib only.
The definitions are copied unchanged from the proof development (`Gap.lean`); the proof is in `SLGapProof.lean`. -/

namespace SingleLevelGap

variable {X Y : Type} [DecidableEq X] [DecidableEq Y]

/-- A wire: an input (a vertex of either side) or a gate. -/
abbrev Wire (X Y : Type) (m : ℕ) := (X ⊕ Y) ⊕ Fin m

/-- A circuit with `m` fan-in-two gates; `isAnd i` says gate `i` is an AND, otherwise it is an OR; gates read earlier wires. -/
structure Circ (X Y : Type) (m : ℕ) where
  isAnd : Fin m → Bool
  inp : Fin m → Bool → Wire X Y m
  out : Wire X Y m
  back : ∀ i b j, inp i b = Sum.inr j → j < i

/-- The value of every wire at an input. -/
def Circ.val {m : ℕ} (C : Circ X Y m) (x : X ⊕ Y → Bool) : Wire X Y m → Bool
  | Sum.inl v => x v
  | Sum.inr i =>
    let a := match h : C.inp i false with
      | Sum.inl v => x v
      | Sum.inr j => have := C.back i false j h; C.val x (Sum.inr j)
    let b := match h : C.inp i true with
      | Sum.inl v => x v
      | Sum.inr j => have := C.back i true j h; C.val x (Sum.inr j)
    if C.isAnd i then a && b else a || b
termination_by w => match w with | Sum.inl _ => 0 | Sum.inr i => (i : ℕ) + 1
decreasing_by all_goals (simp_wf; omega)

/-- A wire below which there is no AND gate. -/
def Circ.andFree {m : ℕ} (C : Circ X Y m) : Wire X Y m → Prop
  | Sum.inl _ => True
  | Sum.inr i => C.isAnd i = false ∧ ∀ b j, (h : C.inp i b = Sum.inr j) → C.andFree (Sum.inr j)
termination_by w => match w with | Sum.inl _ => 0 | Sum.inr i => (i : ℕ) + 1
decreasing_by all_goals (have := C.back _ _ _ h; simp_wf; omega)

/-- Single level: no AND gate below another AND gate. -/
def Circ.single {m : ℕ} (C : Circ X Y m) : Prop := ∀ i, C.isAnd i = true → ∀ b, C.andFree (C.inp i b)

/-- The edge function of the saturated extension of `H`: two vertices on one side, or an edge of `H`. -/
def satf (H : X → Y → Prop) (x : X ⊕ Y → Bool) : Prop :=
  (∃ a a' : X, a ≠ a' ∧ x (Sum.inl a) = true ∧ x (Sum.inl a') = true) ∨
  (∃ b b' : Y, b ≠ b' ∧ x (Sum.inr b) = true ∧ x (Sum.inr b') = true) ∨
  ∃ a b, H a b ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true

end SingleLevelGap

namespace SingleLevelGap

/-- Monotone formulas with variables in `V`. -/
inductive Fm (V : Type) where
  | var : V → Fm V
  | and : Fm V → Fm V → Fm V
  | or : Fm V → Fm V → Fm V

def Fm.eval {V : Type} (x : V → Bool) : Fm V → Bool
  | .var v => x v
  | .and a b => a.eval x && b.eval x
  | .or a b => a.eval x || b.eval x

/-- The number of leaves. -/
def Fm.leaves {V : Type} : Fm V → ℕ
  | .var _ => 1
  | .and a b => a.leaves + b.leaves
  | .or a b => a.leaves + b.leaves

/-- Some monotone formula with at most `s` leaves decides `P`. -/
def Rep {V : Type} (s : ℕ) (P : (V → Bool) → Prop) : Prop := ∃ φ : Fm V, φ.leaves ≤ s ∧ ∀ x, φ.eval x = true ↔ P x

section field
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {k : ℕ} (β : Module.Basis (Fin k) (ZMod 2) F)

/-- The incidence relation. -/
def Hr (u v : F × F) : Prop := u.1 * v.1 = u.2 + v.2

end field

end SingleLevelGap

open SingleLevelGap

/-- The lower bound (Amano–Maruoka form): if the bipartite graph `H` has no 4-cycle, every single-level circuit computing
the edge function of `H` plus a clique on each side has at least a quarter as many gates as `H` has edges. -/
def SingleLevelLower : Prop :=
  ∀ {X Y : Type} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] (m : ℕ) (C : Circ X Y m) (H : X → Y → Prop)
    [DecidablePred fun p : X × Y => H p.1 p.2],
    (∀ a a' b b', H a b → H a b' → H a' b → H a' b' → a = a' ∨ b = b') → C.single →
    (∀ x, C.val x C.out = true ↔ satf H x) → (Finset.univ.filter fun p : X × Y => H p.1 p.2).card ≤ 4 * m

/-- The explicit gap: over `GF(2^k)`, with `N = 4^k` vertices on each side and the `N^(3/2)` edges `a c = b + d`, both sides made
cliques, the edge function has a monotone formula with at most `N (8k + 2 + 8k(k^2+2)^2)` leaves, and every single-level
circuit for it has at least `8^k / 4 = N^(3/2) / 4` gates. -/
def SingleLevelGap : Prop :=
  ∀ k : ℕ, 0 < k →
    Rep (4 ^ k * (8 * k + 2 + 8 * k * (k ^ 2 + 2) ^ 2)) (satf (Hr (F := GaloisField 2 k))) ∧
    ∀ (m : ℕ) (C : Circ (GaloisField 2 k × GaloisField 2 k) (GaloisField 2 k × GaloisField 2 k) m), C.single →
      (∀ x, C.val x C.out = true ↔ satf Hr x) → 8 ^ k ≤ 4 * m
