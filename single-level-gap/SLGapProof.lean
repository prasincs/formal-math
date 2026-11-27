/-
SPDX-License-Identifier: Apache-2.0
-/
import SLGapStatement


/-! Lower bound for single-level monotone circuits of the saturated extension of a bipartite graph with no 4-cycle. -/

namespace SingleLevelGap

variable {X Y : Type} [DecidableEq X] [DecidableEq Y]


theorem val_gate {m : ℕ} (C : Circ X Y m) (x : X ⊕ Y → Bool) (i : Fin m) :
    C.val x (Sum.inr i) = if C.isAnd i then C.val x (C.inp i false) && C.val x (C.inp i true) else C.val x (C.inp i false) || C.val x (C.inp i true) := by
  rw [Circ.val]
  -- `Circ.val` lives in `SLGapStatement`, so its `match` cannot be restated here; split on it instead.
  congr 1 <;> congr 1 <;> split <;> rename_i h <;> (conv_rhs => rw [h]) <;> rw [Circ.val]


theorem andFree_gate {m : ℕ} (C : Circ X Y m) (i : Fin m) (h : C.andFree (Sum.inr i)) : C.isAnd i = false ∧ ∀ b, C.andFree (C.inp i b) := by
  rw [Circ.andFree] at h
  refine ⟨h.1, fun b => ?_⟩
  rcases e : C.inp i b with v | j
  · rw [Circ.andFree]; trivial
  · exact h.2 b j e


def one (v : X ⊕ Y) : X ⊕ Y → Bool := fun w => decide (w = v)
def two (a : X) (b : Y) : X ⊕ Y → Bool := fun w => decide (w = Sum.inl a) || decide (w = Sum.inr b)

/-- The letters of a wire. -/
def Circ.S {m : ℕ} (C : Circ X Y m) (w : Wire X Y m) : Set (X ⊕ Y) := {v | C.val (one v) w = true}

/-- Induction on wires. -/
theorem wind {m : ℕ} (C : Circ X Y m) (P : Wire X Y m → Prop) (h0 : ∀ v, P (Sum.inl v)) (h1 : ∀ i, (∀ b, P (C.inp i b)) → P (Sum.inr i)) : ∀ w, P w := by
  have key : ∀ (k : ℕ) (i : Fin m), (i : ℕ) < k → P (Sum.inr i) := by
    intro k
    induction k with
    | zero => intro i hi; omega
    | succ k ih =>
      intro i hi
      refine h1 i fun b => ?_
      rcases e : C.inp i b with v | j
      · exact h0 v
      · exact ih j (by have : j < i := C.back i b j e; have : (j : ℕ) < (i : ℕ) := this; omega)
  rintro (v | i)
  · exact h0 v
  · exact key (i + 1) i (by omega)

theorem val_or {m : ℕ} (C : Circ X Y m) (x : X ⊕ Y → Bool) (i : Fin m) (h : C.isAnd i = false) :
    C.val x (Sum.inr i) = true ↔ ∃ b, C.val x (C.inp i b) = true := by
  rw [val_gate, h]
  simp

theorem val_and {m : ℕ} (C : Circ X Y m) (x : X ⊕ Y → Bool) (i : Fin m) (h : C.isAnd i = true) :
    C.val x (Sum.inr i) = true ↔ ∀ b, C.val x (C.inp i b) = true := by
  rw [val_gate, h]
  simp

theorem val_inl {m : ℕ} (C : Circ X Y m) (x : X ⊕ Y → Bool) (v : X ⊕ Y) : C.val x (Sum.inl v) = x v := by
  rw [Circ.val]

/-- An AND-free wire is the OR of its letters. -/
theorem val_free {m : ℕ} (C : Circ X Y m) (x : X ⊕ Y → Bool) : ∀ w, C.andFree w → (C.val x w = true ↔ ∃ v ∈ C.S w, x v = true) := by
  refine wind C _ ?_ ?_
  · intro v _
    rw [val_inl]
    constructor
    · intro h; exact ⟨v, by simp [Circ.S, val_inl, one], h⟩
    · rintro ⟨u, hu, h⟩
      have : u = v := by simpa [Circ.S, val_inl, one] using hu
      rw [← this]; exact h
  · intro i ih h
    obtain ⟨h1, h2⟩ := andFree_gate C i h
    rw [val_or C x i h1]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨v, hv, hx⟩ := (ih b (h2 b)).1 hb
      exact ⟨v, (val_or C _ i h1).2 ⟨b, hv⟩, hx⟩
    · rintro ⟨v, hv, hx⟩
      obtain ⟨b, hb⟩ := (val_or C _ i h1).1 hv
      exact ⟨b, (ih b (h2 b)).2 ⟨v, hb, hx⟩⟩

theorem S_or {m : ℕ} (C : Circ X Y m) (i : Fin m) (h : C.isAnd i = false) (v : X ⊕ Y) : v ∈ C.S (Sum.inr i) ↔ ∃ b, v ∈ C.S (C.inp i b) :=
  val_or C _ i h

/-- Where a letter of a set of at least two letters of one side first meets another one. -/
theorem meet {Z : Type} {m : ℕ} (C : Circ X Y m) (e : Z → X ⊕ Y) (z : Z) : ∀ w, C.andFree w → e z ∈ C.S w → (∃ z', z' ≠ z ∧ e z' ∈ C.S w) →
    (∀ y y' : Z, e y = e y' → y = y') →
    ∃ (h : Fin m) (t : Bool), C.isAnd h = false ∧ (∀ y, e y ∈ C.S (C.inp h t) ↔ y = z) ∧ (∃ z', z' ≠ z ∧ e z' ∈ C.S (Sum.inr h)) ∧
      ∀ y, e y ∈ C.S (Sum.inr h) → e y ∈ C.S w := by
  refine wind C _ ?_ ?_
  · rintro v _ hz ⟨z', hne, hz'⟩ hinj
    exfalso
    apply hne
    apply hinj
    have h1 : e z = v := by simpa [Circ.S, val_inl, one] using hz
    have h2 : e z' = v := by simpa [Circ.S, val_inl, one] using hz'
    rw [h1, h2]
  · intro i ih hf hz hz' hinj
    obtain ⟨h1, h2⟩ := andFree_gate C i hf
    obtain ⟨b, hb⟩ := (S_or C i h1 _).1 hz
    by_cases hm : ∃ z', z' ≠ z ∧ e z' ∈ C.S (C.inp i b)
    · obtain ⟨h, t, a1, a2, a3, a4⟩ := ih b (h2 b) hb hm hinj
      exact ⟨h, t, a1, a2, a3, fun y hy => (S_or C i h1 _).2 ⟨b, a4 y hy⟩⟩
    · refine ⟨i, b, h1, fun y => ⟨fun hy => ?_, fun hy => by rw [hy]; exact hb⟩, hz', fun y hy => hy⟩
      by_contra hne
      exact hm ⟨y, hne, hy⟩

/-- The code of an edge. -/
def R {m : ℕ} (C : Circ X Y m) (H : X → Y → Prop) (u : X) (v : Y) (c : Fin m × Bool × Bool) : Prop :=
  (C.isAnd c.1 = true ∧ (∀ a, Sum.inl a ∈ C.S (C.inp c.1 c.2.1) ↔ a = u) ∧ ∀ b, Sum.inr b ∈ C.S (C.inp c.1 (!c.2.1)) ↔ b = v) ∨
  (C.isAnd c.1 = false ∧ c.2.2 = true ∧ (∀ b, Sum.inr b ∈ C.S (C.inp c.1 c.2.1) ↔ b = v) ∧ (∃ b, b ≠ v ∧ Sum.inr b ∈ C.S (Sum.inr c.1)) ∧
    ∀ b, Sum.inr b ∈ C.S (Sum.inr c.1) → H u b) ∨
  (C.isAnd c.1 = false ∧ c.2.2 = false ∧ (∀ a, Sum.inl a ∈ C.S (C.inp c.1 c.2.1) ↔ a = u) ∧ (∃ a, a ≠ u ∧ Sum.inl a ∈ C.S (Sum.inr c.1)) ∧
    ∀ a, Sum.inl a ∈ C.S (Sum.inr c.1) → H a v)

theorem R_inj {m : ℕ} (C : Circ X Y m) (H : X → Y → Prop) (hC4 : ∀ a a' b b', H a b → H a b' → H a' b → H a' b' → a = a' ∨ b = b')
    (u u' : X) (v v' : Y) (c : Fin m × Bool × Bool) (h : R C H u v c) (h' : R C H u' v' c) : u = u' ∧ v = v' := by
  have mem : ∀ w, w ∈ C.S (C.inp c.1 c.2.1) → C.isAnd c.1 = false → w ∈ C.S (Sum.inr c.1) := fun w hw hf => (S_or C _ hf _).2 ⟨_, hw⟩
  rcases h with ⟨o, h1, h2⟩ | ⟨o, t, h1, ⟨b, hb, hb1⟩, h3⟩ | ⟨o, t, h1, ⟨b, hb, hb1⟩, h3⟩ <;>
  rcases h' with ⟨o', k1, k2⟩ | ⟨o', t', k1, _, k3⟩ | ⟨o', t', k1, _, k3⟩
  · exact ⟨(k1 u).1 ((h1 u).2 rfl), (k2 v).1 ((h2 v).2 rfl)⟩
  · rw [o] at o'; cases o'
  · rw [o] at o'; cases o'
  · rw [o] at o'; cases o'
  · have e : v = v' := (k1 v).1 ((h1 v).2 rfl)
    subst e
    have hv := mem _ ((h1 v).2 rfl) o
    exact ⟨(hC4 u u' b v (h3 b hb1) (h3 v hv) (k3 b hb1) (k3 v hv)).resolve_right hb, rfl⟩
  · rw [t] at t'; cases t'
  · rw [o] at o'; cases o'
  · rw [t] at t'; cases t'
  · have e : u = u' := (k1 u).1 ((h1 u).2 rfl)
    subst e
    have hu := mem _ ((h1 u).2 rfl) o
    exact ⟨rfl, (hC4 b u v v' (h3 b hb1) (k3 b hb1) (h3 u hu) (k3 u hu)).resolve_left hb⟩

theorem not_one (H : X → Y → Prop) (v : X ⊕ Y) : ¬ satf H (one v) := by
  rintro (⟨a, a', h, h1, h2⟩ | ⟨a, a', h, h1, h2⟩ | ⟨a, b, _, h1, h2⟩)
  · have h1 : Sum.inl a = v := by simpa [one] using h1
    have h2 : Sum.inl a' = v := by simpa [one] using h2
    exact h (Sum.inl.inj (h1.trans h2.symm))
  · have h1 : Sum.inr a = v := by simpa [one] using h1
    have h2 : Sum.inr a' = v := by simpa [one] using h2
    exact h (Sum.inr.inj (h1.trans h2.symm))
  · have h1 : Sum.inl a = v := by simpa [one] using h1
    have h2 : Sum.inr b = v := by simpa [one] using h2
    cases h1.trans h2.symm

theorem sat_two (H : X → Y → Prop) (a : X) (b : Y) : satf H (two a b) ↔ H a b := by
  constructor
  · rintro (⟨c, c', h, h1, h2⟩ | ⟨c, c', h, h1, h2⟩ | ⟨c, d, h, h1, h2⟩)
    · have h1 : c = a := by simpa [two] using h1
      have h2 : c' = a := by simpa [two] using h2
      exact absurd (h1.trans h2.symm) h
    · have h1 : c = b := by simpa [two] using h1
      have h2 : c' = b := by simpa [two] using h2
      exact absurd (h1.trans h2.symm) h
    · have h1 : c = a := by simpa [two] using h1
      have h2 : d = b := by simpa [two] using h2
      rw [← h1, ← h2]; exact h
  · intro h
    exact Or.inr (Or.inr ⟨a, b, h, by simp [two], by simp [two]⟩)

/-- At an edge the output is true through an AND gate below `satf H`. -/
theorem descend {m : ℕ} (C : Circ X Y m) (H : X → Y → Prop) (a : X) (b : Y) : ∀ w, (∀ x, C.val x w = true → satf H x) → C.val (two a b) w = true →
    ∃ g, C.isAnd g = true ∧ (∀ x, C.val x (Sum.inr g) = true → satf H x) ∧ C.val (two a b) (Sum.inr g) = true := by
  refine wind C _ ?_ ?_
  · intro v hle _
    exact absurd (hle (one v) (by rw [val_inl]; simp [one])) (not_one H v)
  · intro i ih hle hv
    by_cases hi : C.isAnd i = true
    · exact ⟨i, hi, hle, hv⟩
    · have hi : C.isAnd i = false := by simpa using hi
      obtain ⟨t, ht⟩ := (val_or C _ i hi).1 hv
      exact ih t (fun x hx => hle x ((val_or C _ i hi).2 ⟨t, hx⟩)) ht

theorem code {m : ℕ} (C : Circ X Y m) (H : X → Y → Prop) (hC4 : ∀ a a' b b', H a b → H a b' → H a' b → H a' b' → a = a' ∨ b = b') (hs : C.single)
    (hf : ∀ x, C.val x C.out = true ↔ satf H x) (u : X) (v : Y) (huv : H u v) : ∃ c, R C H u v c := by
  obtain ⟨g, hg, hle, hgv⟩ := descend C H u v C.out (fun x hx => (hf x).1 hx) ((hf _).2 ((sat_two H u v).2 huv))
  have fr := hs g hg
  have hab := (val_and C _ g hg).1 hgv
  -- the two operands have no letter in common
  have disj : ∀ w t, w ∈ C.S (C.inp g t) → w ∈ C.S (C.inp g (!t)) → False := by
    intro w t h1 h2
    refine not_one H w (hle _ ((val_and C _ g hg).2 fun b => ?_))
    rcases Bool.eq_or_eq_not b t with rfl | rfl
    · exact h1
    · exact h2
  have ex : ∀ t, Sum.inl u ∈ C.S (C.inp g t) ∨ Sum.inr v ∈ C.S (C.inp g t) := by
    intro t
    obtain ⟨w, hw, hx⟩ := (val_free C _ _ (fr t)).1 (hab t)
    have : w = Sum.inl u ∨ w = Sum.inr v := by simpa [two] using hx
    rcases this with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  obtain ⟨t, htu, htv⟩ : ∃ t, Sum.inl u ∈ C.S (C.inp g t) ∧ Sum.inr v ∈ C.S (C.inp g (!t)) := by
    rcases ex true with h | h
    · rcases ex false with h' | h'
      · exact (disj _ true h h').elim
      · exact ⟨true, h, h'⟩
    · rcases ex false with h' | h'
      · exact ⟨false, h', h⟩
      · exact (disj _ true h h').elim
  have prod : ∀ a b, Sum.inl a ∈ C.S (C.inp g t) → Sum.inr b ∈ C.S (C.inp g (!t)) → H a b := by
    intro a b ha hb
    refine (sat_two H a b).1 (hle _ ((val_and C _ g hg).2 fun s => ?_))
    rcases Bool.eq_or_eq_not s t with rfl | rfl
    · exact (val_free C _ _ (fr _)).2 ⟨_, ha, by simp [two]⟩
    · exact (val_free C _ _ (fr _)).2 ⟨_, hb, by simp [two]⟩
  by_cases hP : ∃ a, a ≠ u ∧ Sum.inl a ∈ C.S (C.inp g t)
  · obtain ⟨h, s, k1, k2, k3, k4⟩ := meet C (fun a : X => (Sum.inl a : X ⊕ Y)) u _ (fr t) htu hP (fun _ _ => Sum.inl.inj)
    exact ⟨(h, s, false), Or.inr (Or.inr ⟨k1, rfl, k2, k3, fun a ha => prod a v (k4 a ha) htv⟩)⟩
  · by_cases hQ : ∃ b, b ≠ v ∧ Sum.inr b ∈ C.S (C.inp g (!t))
    · obtain ⟨h, s, k1, k2, k3, k4⟩ := meet C (fun b : Y => (Sum.inr b : X ⊕ Y)) v _ (fr (!t)) htv hQ (fun _ _ => Sum.inr.inj)
      exact ⟨(h, s, true), Or.inr (Or.inl ⟨k1, rfl, k2, k3, fun b hb => prod u b htu (k4 b hb)⟩)⟩
    · refine ⟨(g, t, true), Or.inl ⟨hg, fun a => ⟨fun ha => ?_, fun ha => by rw [ha]; exact htu⟩, fun b => ⟨fun hb => ?_, fun hb => by rw [hb]; exact htv⟩⟩⟩
      · by_contra hne; exact hP ⟨a, hne, ha⟩
      · by_contra hne; exact hQ ⟨b, hne, hb⟩

/-- A single-level circuit for the saturated extension of a bipartite graph with no 4-cycle has at least a quarter as many gates as the graph has edges. -/
theorem lower [Fintype X] [Fintype Y] {m : ℕ} (C : Circ X Y m) (H : X → Y → Prop) [DecidablePred fun p : X × Y => H p.1 p.2]
    (hC4 : ∀ a a' b b', H a b → H a b' → H a' b → H a' b' → a = a' ∨ b = b') (hs : C.single)
    (hf : ∀ x, C.val x C.out = true ↔ satf H x) : (Finset.univ.filter fun p : X × Y => H p.1 p.2).card ≤ 4 * m := by
  classical
  have hc : ∀ p : X × Y, ∃ c : Option (Fin m × Bool × Bool), H p.1 p.2 → ∃ d, c = some d ∧ R C H p.1 p.2 d := by
    intro p
    by_cases hp : H p.1 p.2
    · obtain ⟨d, hd⟩ := code C H hC4 hs hf p.1 p.2 hp
      exact ⟨some d, fun _ => ⟨d, rfl, hd⟩⟩
    · exact ⟨none, fun h => absurd h hp⟩
  choose φ hφ using hc
  have := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun p : X × Y => H p.1 p.2) (t := (Finset.univ : Finset (Fin m × Bool × Bool)).map Function.Embedding.some) φ (by
    intro p hp
    obtain ⟨d, hd, _⟩ := hφ p (by simpa using hp)
    simp [hd]) (by
    intro p hp p' hp' e
    obtain ⟨d, hd, h1⟩ := hφ p (by simpa using hp)
    obtain ⟨d', hd', h2⟩ := hφ p' (by simpa using hp')
    have : d = d' := Option.some.inj (by rw [← hd, ← hd', e])
    rw [← this] at h2
    obtain ⟨a, b⟩ := R_inj C H hC4 _ _ _ _ _ h1 h2
    exact Prod.ext a b)
  rw [Finset.card_map] at this
  refine this.trans ?_
  rw [Finset.card_univ]
  simp
  omega

/-! ### The lower bound for `(t, s)`-free graphs

The same charging as above, with thresholds `t` and `s` in place of `2`: instead of an injective code, every code
receives at most `(t - 1) (s - 1)` edges. -/

/-- The letters of a wire on one side, as a finite set. -/
noncomputable def L [Fintype X] [Fintype Y] {Z : Type} [Fintype Z] {m : ℕ} (C : Circ X Y m) (e : Z → X ⊕ Y)
    (w : Wire X Y m) : Finset Z := by
  classical
  exact Finset.univ.filter fun z => e z ∈ C.S w

theorem mem_L [Fintype X] [Fintype Y] {Z : Type} [Fintype Z] {m : ℕ} (C : Circ X Y m) (e : Z → X ⊕ Y)
    (w : Wire X Y m) (z : Z) : z ∈ L C e w ↔ e z ∈ C.S w := by
  classical
  simp [L]

/-- Walking up from a letter `z` in an AND-free wire with at least `r` letters on one side: the first wire with at least
`r` letters is an OR gate `h` whose operand on the walk has fewer than `r`. -/
theorem meet' [Fintype X] [Fintype Y] {Z : Type} [Fintype Z] {m : ℕ} (C : Circ X Y m) (e : Z → X ⊕ Y)
    (hinj : Function.Injective e) (r : ℕ) (hr : 2 ≤ r) (z : Z) :
    ∀ w, C.andFree w → e z ∈ C.S w → r ≤ (L C e w).card →
    ∃ (h : Fin m) (b : Bool), C.isAnd h = false ∧ e z ∈ C.S (C.inp h b) ∧ (L C e (C.inp h b)).card < r ∧
      r ≤ (L C e (Sum.inr h)).card ∧ ∀ y, e y ∈ C.S (Sum.inr h) → e y ∈ C.S w := by
  refine wind C _ ?_ ?_
  · intro v _ hz hcard
    exfalso
    have hsub : L C e (Sum.inl v) ⊆ {z} := by
      intro y hy
      have hy' := (mem_L C e _ y).1 hy
      have e1 : e y = v := by simpa [Circ.S, val_inl, one] using hy'
      have e2 : e z = v := by simpa [Circ.S, val_inl, one] using hz
      exact Finset.mem_singleton.2 (hinj (e1.trans e2.symm))
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  · intro i ih hf hz hcard
    obtain ⟨h1, h2⟩ := andFree_gate C i hf
    obtain ⟨b, hb⟩ := (S_or C i h1 _).1 hz
    by_cases hm : r ≤ (L C e (C.inp i b)).card
    · obtain ⟨h, k, a1, a2, a3, a4, a5⟩ := ih b (h2 b) hb hm
      exact ⟨h, k, a1, a2, a3, a4, fun y hy => (S_or C i h1 _).2 ⟨b, a5 y hy⟩⟩
    · exact ⟨i, b, h1, hb, by omega, hcard, fun y hy => hy⟩

/-- The code of an edge for `(t, s)`-free graphs: an AND gate with few letters on both sides, or the first OR gate with
at least `s` letters in `Y` (part bit `true`), or with at least `t` letters in `X` (part bit `false`). -/
def R2 [Fintype X] [Fintype Y] {m : ℕ} (C : Circ X Y m) (H : X → Y → Prop) (t s : ℕ) (u : X) (v : Y)
    (c : Fin m × Bool × Bool) : Prop :=
  (C.isAnd c.1 = true ∧ Sum.inl u ∈ C.S (C.inp c.1 c.2.1) ∧ Sum.inr v ∈ C.S (C.inp c.1 (!c.2.1)) ∧
    (L C (Sum.inl : X → X ⊕ Y) (C.inp c.1 c.2.1)).card < t ∧ (L C (Sum.inr : Y → X ⊕ Y) (C.inp c.1 (!c.2.1))).card < s) ∨
  (C.isAnd c.1 = false ∧ c.2.2 = true ∧ Sum.inr v ∈ C.S (C.inp c.1 c.2.1) ∧
    (L C (Sum.inr : Y → X ⊕ Y) (C.inp c.1 c.2.1)).card < s ∧ s ≤ (L C (Sum.inr : Y → X ⊕ Y) (Sum.inr c.1)).card ∧
    ∀ b, Sum.inr b ∈ C.S (Sum.inr c.1) → H u b) ∨
  (C.isAnd c.1 = false ∧ c.2.2 = false ∧ Sum.inl u ∈ C.S (C.inp c.1 c.2.1) ∧
    (L C (Sum.inl : X → X ⊕ Y) (C.inp c.1 c.2.1)).card < t ∧ t ≤ (L C (Sum.inl : X → X ⊕ Y) (Sum.inr c.1)).card ∧
    ∀ a, Sum.inl a ∈ C.S (Sum.inr c.1) → H a v)

/-- Every edge of `H` has a code. -/
theorem code2 [Fintype X] [Fintype Y] {m : ℕ} (C : Circ X Y m) (H : X → Y → Prop) (t s : ℕ) (ht : 2 ≤ t) (hs2 : 2 ≤ s)
    (hsg : C.single) (hf : ∀ x, C.val x C.out = true ↔ satf H x) (u : X) (v : Y) (huv : H u v) :
    ∃ c, R2 C H t s u v c := by
  obtain ⟨g, hg, hle, hgv⟩ := descend C H u v C.out (fun x hx => (hf x).1 hx) ((hf _).2 ((sat_two H u v).2 huv))
  have fr := hsg g hg
  have hab := (val_and C _ g hg).1 hgv
  have disj : ∀ w k, w ∈ C.S (C.inp g k) → w ∈ C.S (C.inp g (!k)) → False := by
    intro w k h1 h2
    refine not_one H w (hle _ ((val_and C _ g hg).2 fun b => ?_))
    rcases Bool.eq_or_eq_not b k with rfl | rfl
    · exact h1
    · exact h2
  have ex : ∀ k, Sum.inl u ∈ C.S (C.inp g k) ∨ Sum.inr v ∈ C.S (C.inp g k) := by
    intro k
    obtain ⟨w, hw, hx⟩ := (val_free C _ _ (fr k)).1 (hab k)
    have : w = Sum.inl u ∨ w = Sum.inr v := by simpa [two] using hx
    rcases this with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  obtain ⟨k, htu, htv⟩ : ∃ k, Sum.inl u ∈ C.S (C.inp g k) ∧ Sum.inr v ∈ C.S (C.inp g (!k)) := by
    rcases ex true with h | h
    · rcases ex false with h' | h'
      · exact (disj _ true h h').elim
      · exact ⟨true, h, h'⟩
    · rcases ex false with h' | h'
      · exact ⟨false, h', h⟩
      · exact (disj _ true h h').elim
  have prod : ∀ a b, Sum.inl a ∈ C.S (C.inp g k) → Sum.inr b ∈ C.S (C.inp g (!k)) → H a b := by
    intro a b ha hb
    refine (sat_two H a b).1 (hle _ ((val_and C _ g hg).2 fun s' => ?_))
    rcases Bool.eq_or_eq_not s' k with rfl | rfl
    · exact (val_free C _ _ (fr _)).2 ⟨_, ha, by simp [two]⟩
    · exact (val_free C _ _ (fr _)).2 ⟨_, hb, by simp [two]⟩
  by_cases hP : t ≤ (L C (Sum.inl : X → X ⊕ Y) (C.inp g k)).card
  · obtain ⟨h, b, k1, k2, k3, k4, k5⟩ := meet' C (Sum.inl : X → X ⊕ Y) Sum.inl_injective t ht u _ (fr k) htu hP
    exact ⟨(h, b, false), Or.inr (Or.inr ⟨k1, rfl, k2, k3, k4, fun a ha => prod a v (k5 a ha) htv⟩)⟩
  · by_cases hQ : s ≤ (L C (Sum.inr : Y → X ⊕ Y) (C.inp g (!k))).card
    · obtain ⟨h, b, k1, k2, k3, k4, k5⟩ := meet' C (Sum.inr : Y → X ⊕ Y) Sum.inr_injective s hs2 v _ (fr (!k)) htv hQ
      exact ⟨(h, b, true), Or.inr (Or.inl ⟨k1, rfl, k2, k3, k4, fun b' hb => prod u b' htu (k5 b' hb)⟩)⟩
    · exact ⟨(g, k, true), Or.inl ⟨hg, htu, htv, Nat.lt_of_not_le hP, Nat.lt_of_not_le hQ⟩⟩

/-- The edges with a given code lie in a product of two sets with at most `(t - 1) (s - 1)` pairs. -/
theorem fibre2 [Fintype X] [Fintype Y] {m : ℕ} (C : Circ X Y m) (H : X → Y → Prop) (t s : ℕ)
    (hfree : ∀ (A : Finset X) (B : Finset Y), t ≤ A.card → s ≤ B.card → ∃ a ∈ A, ∃ b ∈ B, ¬ H a b)
    (c : Fin m × Bool × Bool) :
    ∃ (P1 : Finset X) (P2 : Finset Y), P1.card * P2.card ≤ (t - 1) * (s - 1) ∧
      ∀ u v, R2 C H t s u v c → u ∈ P1 ∧ v ∈ P2 := by
  classical
  -- common neighbours of a large set have few elements
  have nx : ∀ T : Finset Y, s ≤ T.card → (Finset.univ.filter fun a : X => ∀ b ∈ T, H a b).card < t := by
    intro T hT
    by_contra hc
    obtain ⟨a, ha, b, hb, hn⟩ := hfree (Finset.univ.filter fun a : X => ∀ b ∈ T, H a b) T (by omega) hT
    exact hn ((Finset.mem_filter.1 ha).2 b hb)
  have ny : ∀ A : Finset X, t ≤ A.card → (Finset.univ.filter fun b : Y => ∀ a ∈ A, H a b).card < s := by
    intro A hA
    by_contra hc
    obtain ⟨a, ha, b, hb, hn⟩ := hfree A (Finset.univ.filter fun b : Y => ∀ a ∈ A, H a b) hA (by omega)
    exact hn ((Finset.mem_filter.1 hb).2 a ha)
  by_cases hex : ∃ u v, R2 C H t s u v c
  swap
  · exact ⟨∅, ∅, by simp, fun u v h => absurd ⟨u, v, h⟩ hex⟩
  obtain ⟨u0, v0, h0⟩ := hex
  rcases h0 with ⟨o, _, _, ca, cb⟩ | ⟨o, p, _, cb, cs, _⟩ | ⟨o, p, _, ca, ct, _⟩
  · refine ⟨L C (Sum.inl : X → X ⊕ Y) (C.inp c.1 c.2.1), L C (Sum.inr : Y → X ⊕ Y) (C.inp c.1 (!c.2.1)),
      Nat.mul_le_mul (by omega) (by omega), fun u v h => ?_⟩
    rcases h with ⟨_, hu, hv, _, _⟩ | ⟨o', _⟩ | ⟨o', _⟩
    · exact ⟨(mem_L C _ _ u).2 hu, (mem_L C _ _ v).2 hv⟩
    · rw [o] at o'; cases o'
    · rw [o] at o'; cases o'
  · refine ⟨Finset.univ.filter fun a : X => ∀ b ∈ L C (Sum.inr : Y → X ⊕ Y) (Sum.inr c.1), H a b,
      L C (Sum.inr : Y → X ⊕ Y) (C.inp c.1 c.2.1), Nat.mul_le_mul (by have := nx _ cs; omega) (by omega),
      fun u v h => ?_⟩
    rcases h with ⟨o', _⟩ | ⟨_, _, hv, _, _, hH⟩ | ⟨_, p', _⟩
    · rw [o] at o'; cases o'
    · exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, fun b hb => hH b ((mem_L C _ _ b).1 hb)⟩, (mem_L C _ _ v).2 hv⟩
    · rw [p] at p'; cases p'
  · refine ⟨L C (Sum.inl : X → X ⊕ Y) (C.inp c.1 c.2.1),
      Finset.univ.filter fun b : Y => ∀ a ∈ L C (Sum.inl : X → X ⊕ Y) (Sum.inr c.1), H a b,
      Nat.mul_le_mul (by omega) (by have := ny _ ct; omega), fun u v h => ?_⟩
    rcases h with ⟨o', _⟩ | ⟨_, p', _⟩ | ⟨_, _, hu, _, _, hH⟩
    · rw [o] at o'; cases o'
    · rw [p] at p'; cases p'
    · exact ⟨(mem_L C _ _ u).2 hu, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun a ha => hH a ((mem_L C _ _ a).1 ha)⟩⟩

/-- Lemma 2 of the paper: a single-level circuit for the saturated extension of a `(t, s)`-free bipartite graph has at
least `|E(H)| / (4 (t - 1) (s - 1))` gates. -/
theorem lower2 [Fintype X] [Fintype Y] {m : ℕ} (C : Circ X Y m) (H : X → Y → Prop) [DecidablePred fun p : X × Y => H p.1 p.2]
    (t s : ℕ) (ht : 2 ≤ t) (hs2 : 2 ≤ s)
    (hfree : ∀ (A : Finset X) (B : Finset Y), t ≤ A.card → s ≤ B.card → ∃ a ∈ A, ∃ b ∈ B, ¬ H a b)
    (hsg : C.single) (hf : ∀ x, C.val x C.out = true ↔ satf H x) :
    (Finset.univ.filter fun p : X × Y => H p.1 p.2).card ≤ 4 * (t - 1) * (s - 1) * m := by
  classical
  have hc : ∀ p : X × Y, ∃ c : Option (Fin m × Bool × Bool), H p.1 p.2 → ∃ d, c = some d ∧ R2 C H t s p.1 p.2 d := by
    intro p
    by_cases hp : H p.1 p.2
    · obtain ⟨d, hd⟩ := code2 C H t s ht hs2 hsg hf p.1 p.2 hp
      exact ⟨some d, fun _ => ⟨d, rfl, hd⟩⟩
    · exact ⟨none, fun h => absurd h hp⟩
  choose φ hφ using hc
  have key := Finset.card_le_mul_card_image_of_maps_to (f := φ)
    (s := Finset.univ.filter fun p : X × Y => H p.1 p.2)
    (t := (Finset.univ : Finset (Fin m × Bool × Bool)).map Function.Embedding.some)
    (by
      intro p hp
      obtain ⟨d, hd, _⟩ := hφ p (by simpa using hp)
      simp [hd])
    ((t - 1) * (s - 1))
    (by
      intro b hb
      obtain ⟨d, -, rfl⟩ := Finset.mem_map.1 hb
      obtain ⟨P1, P2, hcard, hmem⟩ := fibre2 C H t s hfree d
      refine le_trans (Finset.card_le_card (t := P1 ×ˢ P2) ?_) (by rw [Finset.card_product]; exact hcard)
      intro p hp
      obtain ⟨hpE, hpd⟩ := Finset.mem_filter.1 hp
      obtain ⟨d', hd', hR⟩ := hφ p (by simpa using hpE)
      have : d' = d := Option.some.inj (hd'.symm.trans hpd)
      rw [this] at hR
      exact Finset.mem_product.2 (hmem p.1 p.2 hR))
  rw [Finset.card_map, Finset.card_univ] at key
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at key
  calc (Finset.univ.filter fun p : X × Y => H p.1 p.2).card ≤ (t - 1) * (s - 1) * (m * (2 * 2)) := key
    _ = 4 * (t - 1) * (s - 1) * m := by ring

end SingleLevelGap

namespace SingleLevelGap


variable {V : Type}

theorem Rep.mono {s t : ℕ} {P : (V → Bool) → Prop} (h : Rep s P) (hst : s ≤ t) : Rep t P := by
  obtain ⟨φ, h1, h2⟩ := h
  exact ⟨φ, h1.trans hst, h2⟩

theorem Rep.var (v : V) : Rep 1 fun x => x v = true := ⟨.var v, le_rfl, fun _ => Iff.rfl⟩

theorem Rep.or {s t : ℕ} {P Q : (V → Bool) → Prop} (h : Rep s P) (h' : Rep t Q) : Rep (s + t) fun x => P x ∨ Q x := by
  obtain ⟨φ, h1, h2⟩ := h
  obtain ⟨ψ, k1, k2⟩ := h'
  refine ⟨.or φ ψ, Nat.add_le_add h1 k1, fun x => ?_⟩
  show _ ↔ P x ∨ Q x
  rw [← h2, ← k2, Fm.eval, Bool.or_eq_true]

theorem Rep.and {s t : ℕ} {P Q : (V → Bool) → Prop} (h : Rep s P) (h' : Rep t Q) : Rep (s + t) fun x => P x ∧ Q x := by
  obtain ⟨φ, h1, h2⟩ := h
  obtain ⟨ψ, k1, k2⟩ := h'
  refine ⟨.and φ ψ, Nat.add_le_add h1 k1, fun x => ?_⟩
  show _ ↔ P x ∧ Q x
  rw [← h2, ← k2, Fm.eval, Bool.and_eq_true]

theorem Rep.ex {ι : Type} {s : ℕ} (P : ι → (V → Bool) → Prop) : ∀ l : List ι, l ≠ [] → (∀ i ∈ l, Rep s (P i)) → Rep (l.length * s) fun x => ∃ i ∈ l, P i x
  | [], h, _ => absurd rfl h
  | [i], _, h => by simpa using h i (by simp)
  | i :: j :: l, _, h => by
    have h1 := (h i (by simp)).or (Rep.ex P (j :: l) (by simp) fun a ha => h a (List.mem_cons_of_mem _ ha))
    have e : (i :: j :: l).length * s = s + (j :: l).length * s := by simp only [List.length_cons]; ring
    rw [e]
    simpa only [List.mem_cons, exists_eq_or_imp] using h1

theorem Rep.all {ι : Type} {s : ℕ} (P : ι → (V → Bool) → Prop) : ∀ l : List ι, l ≠ [] → (∀ i ∈ l, Rep s (P i)) → Rep (l.length * s) fun x => ∀ i ∈ l, P i x
  | [], h, _ => absurd rfl h
  | [i], _, h => by simpa using h i (by simp)
  | i :: j :: l, _, h => by
    have h1 := (h i (by simp)).and (Rep.all P (j :: l) (by simp) fun a ha => h a (List.mem_cons_of_mem _ ha))
    have e : (i :: j :: l).length * s = s + (j :: l).length * s := by simp only [List.length_cons]; ring
    rw [e]
    simpa only [List.mem_cons, forall_eq_or_imp] using h1

theorem Rep.congr {s : ℕ} {P Q : (V → Bool) → Prop} (h : Rep s P) (e : ∀ x, P x ↔ Q x) : Rep s Q := by
  obtain ⟨φ, h1, h2⟩ := h
  exact ⟨φ, h1, fun x => (h2 x).trans (e x)⟩

/-- The OR of the variables of a nonempty finite set. -/
theorem Rep.set {ι : Type} [Fintype ι] (e : ι → V) (p : ι → Prop) [DecidablePred p] (h : ∃ i, p i) : Rep (Fintype.card ι) fun x => ∃ i, p i ∧ x (e i) = true := by
  have hl : (Finset.univ.filter p).toList ≠ [] := by
    obtain ⟨i, hi⟩ := h
    intro h0
    have : i ∈ (Finset.univ.filter p).toList := by simp [hi]
    rw [h0] at this
    simp at this
  have h1 := Rep.ex (s := 1) (fun i x => x (e i) = true) _ hl fun i _ => Rep.var (e i)
  refine (h1.mono ?_).congr fun x => ?_
  · rw [Finset.length_toList, Nat.mul_one]
    exact Finset.card_le_univ _
  · simp

/-- `U x τ` says that the input `x` has the type `τ`. A bit `b` of the type: `b = 1` and `b = 0` both have monotone formulas, correct on typed inputs. -/
def Bit {T : Type} (U : (V → Bool) → T → Prop) (s : ℕ) (b : T → ZMod 2) : Prop :=
  ∃ P Q : (V → Bool) → Prop, Rep s P ∧ Rep s Q ∧ ∀ x τ, U x τ → ((P x ↔ b τ = 1) ∧ (Q x ↔ b τ = 0))

theorem z2 (c d : ZMod 2) : ((c = 1 ∧ d = 0 ∨ c = 0 ∧ d = 1 ↔ c + d = 1) ∧ (c = 1 ∧ d = 1 ∨ c = 0 ∧ d = 0 ↔ c + d = 0)) ∧ ((c = 1 ∧ d = 1 ↔ c * d = 1) ∧ (c = 0 ∨ d = 0 ↔ c * d = 0)) := by
  revert c d; decide

variable {T : Type} {U : (V → Bool) → T → Prop}

theorem Bit.add {s t : ℕ} {a b : T → ZMod 2} (h : Bit U s a) (h' : Bit U t b) : Bit U (2 * (s + t)) fun x => a x + b x := by
  obtain ⟨P, Q, hP, hQ, h1⟩ := h
  obtain ⟨P', Q', hP', hQ', h2⟩ := h'
  refine ⟨_, _, ((hP.and hQ').or (hQ.and hP')).mono (by omega), ((hP.and hP').or (hQ.and hQ')).mono (by omega), fun x τ hx => ?_⟩
  obtain ⟨a1, a2⟩ := h1 x τ hx
  obtain ⟨b1, b2⟩ := h2 x τ hx
  rw [a1, a2, b1, b2]
  exact (z2 _ _).1

theorem Bit.mul {s t : ℕ} {a b : T → ZMod 2} (h : Bit U s a) (h' : Bit U t b) : Bit U (s + t) fun x => a x * b x := by
  obtain ⟨P, Q, hP, hQ, h1⟩ := h
  obtain ⟨P', Q', hP', hQ', h2⟩ := h'
  refine ⟨_, _, hP.and hP', hQ.or hQ', fun x τ hx => ?_⟩
  obtain ⟨a1, a2⟩ := h1 x τ hx
  obtain ⟨b1, b2⟩ := h2 x τ hx
  rw [a1, a2, b1, b2]
  exact (z2 _ _).2

theorem Bit.mono {s t : ℕ} {a : T → ZMod 2} (h : Bit U s a) (hst : s ≤ t) : Bit U t a := by
  obtain ⟨P, Q, hP, hQ, h1⟩ := h
  exact ⟨P, Q, hP.mono hst, hQ.mono hst, h1⟩

/-- A sum of at most `2 ^ t` bits. -/
theorem Bit.sum {s : ℕ} {ι : Type} (a : ι → T → ZMod 2) : ∀ (t : ℕ) (l : List ι), l ≠ [] → l.length ≤ 2 ^ t → (∀ i ∈ l, Bit U s (a i)) →
    Bit U (4 ^ t * s) fun x => (l.map fun i => a i x).sum := by
  intro t
  induction t with
  | zero =>
    intro l hl hlen h
    rcases l with _ | ⟨i, _ | ⟨j, l⟩⟩
    · exact absurd rfl hl
    · simpa using h i (by simp)
    · simp at hlen
  | succ t ih =>
    intro l hl hlen h
    by_cases hs : l.length ≤ 2 ^ t
    · exact (ih l hl hs h).mono (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega)))
    · have hpos : 0 < 2 ^ t := by positivity
      have hp2 : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [pow_succ]; omega
      have l1 : (l.take (2 ^ t)).length = 2 ^ t := by rw [List.length_take]; omega
      have l2 : (l.drop (2 ^ t)).length = l.length - 2 ^ t := List.length_drop
      have h1 := ih (l.take (2 ^ t)) (List.ne_nil_of_length_pos (by omega)) (by omega) fun i hi => h i (List.mem_of_mem_take hi)
      have h2 := ih (l.drop (2 ^ t)) (List.ne_nil_of_length_pos (by omega)) (by omega) fun i hi => h i (List.mem_of_mem_drop hi)
      have h3 := (h1.add h2).mono (t := 4 ^ (t + 1) * s) (by rw [pow_succ]; linarith)
      have e : ∀ x, ((l.take (2 ^ t)).map fun i => a i x).sum + ((l.drop (2 ^ t)).map fun i => a i x).sum = (l.map fun i => a i x).sum := by
        intro x
        rw [← List.sum_append, ← List.map_append, List.take_append_drop]
      simpa only [e] using h3

section field
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {k : ℕ} (β : Module.Basis (Fin k) (ZMod 2) F)


theorem Hr_c4 (a a' b b' : F × F) (h1 : Hr a b) (h2 : Hr a b') (h3 : Hr a' b) (h4 : Hr a' b') : a = a' ∨ b = b' := by
  simp only [Hr] at *
  by_cases h : a.1 = a'.1
  · left
    refine Prod.ext h ?_
    rw [← h] at h3
    have : a.2 + b.2 = a'.2 + b.2 := by rw [← h1, ← h3]
    exact add_right_cancel this
  · right
    have e : (a.1 - a'.1) * (b.1 - b'.1) = 0 := by linear_combination h1 - h2 - h3 + h4
    rcases mul_eq_zero.1 e with e | e
    · exact absurd (sub_eq_zero.1 e) h
    · have e1 := sub_eq_zero.1 e
      refine Prod.ext e1 ?_
      rw [← e1] at h2
      exact add_left_cancel (h1.symm.trans h2)

/-- Exactly one vertex on each side. -/
def Uq (x : (F × F) ⊕ (F × F) → Bool) (τ : (F × F) × (F × F)) : Prop :=
  (∀ a, x (Sum.inl a) = true ↔ a = τ.1) ∧ ∀ b, x (Sum.inr b) = true ↔ b = τ.2

/-- The address bits of a vertex. -/
def ad (β : Module.Basis (Fin k) (ZMod 2) F) (u : F × F) : Fin k ⊕ Fin k → ZMod 2
  | Sum.inl i => β.repr u.1 i
  | Sum.inr i => β.repr u.2 i

theorem ad_ex (j : Fin k ⊕ Fin k) (e : ZMod 2) : ∃ u : F × F, ad β u j = e := by
  rcases j with i | i
  · exact ⟨(e • β i, 0), by simp [ad]⟩
  · exact ⟨(0, e • β i), by simp [ad]⟩

theorem ad_inj (u u' : F × F) (h : ∀ j, ad β u j = ad β u' j) : u = u' :=
  Prod.ext (β.repr.injective (Finsupp.ext fun i => h (Sum.inl i))) (β.repr.injective (Finsupp.ext fun i => h (Sum.inr i)))

/-- One address bit of one side. -/
theorem bitX (j : Fin k ⊕ Fin k) : Bit Uq (Fintype.card (F × F)) (fun τ => ad β τ.1 j) := by
  refine ⟨_, _, Rep.set Sum.inl (fun u => ad β u j = 1) (ad_ex β j 1), Rep.set Sum.inl (fun u => ad β u j = 0) (ad_ex β j 0), fun x τ hx => ⟨?_, ?_⟩⟩ <;>
  · constructor
    · rintro ⟨u, h1, h2⟩
      have hu := (hx.1 u).1 h2
      subst hu; exact h1
    · intro h
      exact ⟨_, h, (hx.1 _).2 rfl⟩

theorem bitY (j : Fin k ⊕ Fin k) : Bit Uq (Fintype.card (F × F)) (fun τ => ad β τ.2 j) := by
  refine ⟨_, _, Rep.set Sum.inr (fun u => ad β u j = 1) (ad_ex β j 1), Rep.set Sum.inr (fun u => ad β u j = 0) (ad_ex β j 0), fun x τ hx => ⟨?_, ?_⟩⟩ <;>
  · constructor
    · rintro ⟨u, h1, h2⟩
      have hu := (hx.2 u).1 h2
      subst hu; exact h1
    · intro h
      exact ⟨_, h, (hx.2 _).2 rfl⟩

/-- Two vertices of one side differ in an address bit. -/
theorem two_side (β : Module.Basis (Fin k) (ZMod 2) F) (e : F × F → V) (hk : 0 < k) : Rep (4 * k * Fintype.card (F × F)) fun x => ∃ a a' : F × F, a ≠ a' ∧ x (e a) = true ∧ x (e a') = true := by
  have h1 := Rep.ex (s := Fintype.card (F × F) + Fintype.card (F × F)) (fun (j : Fin k ⊕ Fin k) (x : V → Bool) =>
    (∃ u, ad β u j = 1 ∧ x (e u) = true) ∧ ∃ u, ad β u j = 0 ∧ x (e u) = true) (Finset.univ : Finset (Fin k ⊕ Fin k)).toList
    (by
      intro h0
      have : Sum.inl ⟨0, hk⟩ ∈ (Finset.univ : Finset (Fin k ⊕ Fin k)).toList := by simp
      rw [h0] at this
      simp at this) fun j _ => (Rep.set e (fun u => ad β u j = 1) (ad_ex β j 1)).and (Rep.set e (fun u => ad β u j = 0) (ad_ex β j 0))
  refine (h1.mono (le_of_eq ?_)).congr fun x => ?_
  · rw [Finset.length_toList, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]; ring
  · simp only [Finset.mem_toList, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, ⟨u, h1, h2⟩, u', h3, h4⟩
      refine ⟨u, u', ?_, h2, h4⟩
      rintro rfl
      rw [h1] at h3
      exact absurd h3 (by decide)
    · rintro ⟨a, a', hne, h1, h2⟩
      obtain ⟨j, hj⟩ : ∃ j, ad β a j ≠ ad β a' j := by
        by_contra hc
        push Not at hc
        exact hne (ad_inj β a a' hc)
      have two : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      refine ⟨j, ?_⟩
      rcases two (ad β a j) with h | h <;> rcases two (ad β a' j) with h' | h'
      · exact absurd (h.trans h'.symm) hj
      · exact ⟨⟨a', h', h2⟩, a, h, h1⟩
      · exact ⟨⟨a, h, h1⟩, a', h', h2⟩
      · exact absurd (h.trans h'.symm) hj

/-- The terms of coordinate `i` of `a * c + b + d`. -/
def term (β : Module.Basis (Fin k) (ZMod 2) F) : (Fin k × Fin k) ⊕ Bool → Fin k → (F × F) × (F × F) → ZMod 2
  | Sum.inl p, _, τ => ad β τ.1 (Sum.inl p.1) * ad β τ.2 (Sum.inl p.2)
  | Sum.inr false, i, τ => ad β τ.1 (Sum.inr i)
  | Sum.inr true, i, τ => ad β τ.2 (Sum.inr i)

/-- The list of the terms of coordinate `i`. -/
noncomputable def tl (β : Module.Basis (Fin k) (ZMod 2) F) (i : Fin k) : List ((Fin k × Fin k) ⊕ Bool) :=
  ((Finset.univ.filter fun p : Fin k × Fin k => β.repr (β p.1 * β p.2) i = 1).toList.map Sum.inl) ++ [Sum.inr false, Sum.inr true]

theorem coord (i : Fin k) (τ : (F × F) × (F × F)) : ((tl β i).map fun q => term β q i τ).sum = β.repr (τ.1.1 * τ.2.1 + τ.1.2 + τ.2.2) i := by
  obtain ⟨⟨a, b⟩, c, d⟩ := τ
  have e : β.repr (a * c) i = ∑ p : Fin k × Fin k, if β.repr (β p.1 * β p.2) i = 1 then β.repr a p.1 * β.repr c p.2 else 0 := by
    conv_lhs => rw [← β.sum_repr a, ← β.sum_repr c]
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    rw [map_sum, Finsupp.finsetSum_apply, Finset.univ_product_univ]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have two : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    split_ifs with h
    · rw [h, mul_one]
    · rw [(two _).resolve_right h, mul_zero]
  simp only [tl, List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, map_add, Finsupp.add_apply]
  rw [e, ← Finset.sum_filter]
  simp only [term, ad, Function.comp_def, add_zero, add_assoc]
  congr 1
  exact Finset.sum_map_toList _ _

/-- The saturated extension has a monotone formula with about `|X|` times a power of `k` leaves. -/
theorem upper (β : Module.Basis (Fin k) (ZMod 2) F) (hk : 0 < k) : Rep (Fintype.card (F × F) * (8 * k + 2 + 8 * k * (k ^ 2 + 2) ^ 2)) (satf (Hr (F := F))) := by
  set N := Fintype.card (F × F) with hN
  have tb : ∀ i, ∀ q ∈ tl β i, Bit Uq (2 * N) fun τ => term β q i τ := by
    rintro i (p | q) _
    · exact ((bitX β (Sum.inl p.1)).mul (bitY β (Sum.inl p.2))).mono (by omega)
    · cases q
      · exact (bitX β (Sum.inr i)).mono (by omega)
      · exact (bitY β (Sum.inr i)).mono (by omega)
  have len : ∀ i, (tl β i).length ≤ k ^ 2 + 2 := by
    intro i
    simp only [tl, List.length_append, List.length_map, Finset.length_toList, List.length_cons, List.length_nil]
    have := Finset.card_filter_le (Finset.univ : Finset (Fin k × Fin k)) (fun p => β.repr (β p.1 * β p.2) i = 1)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at this
    nlinarith
  set t := Nat.clog 2 (k ^ 2 + 2) with ht
  have ht1 : k ^ 2 + 2 ≤ 2 ^ t := Nat.le_pow_clog (by norm_num) _
  have ht2 : 2 ^ t ≤ 2 * (k ^ 2 + 2) := by
    have h1 : 2 ^ (t - 1) < k ^ 2 + 2 := by
      have := Nat.pow_pred_clog_lt_self 2 (x := k ^ 2 + 2) (by omega)
      simpa [Nat.pred_eq_sub_one] using this
    have h2 : 0 < t := Nat.clog_pos (by norm_num) (by omega)
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero h2.ne'
    rw [hr] at h1 ⊢
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at h1 ⊢
    rw [pow_succ]; omega
  have h4 : 4 ^ t ≤ 4 * (k ^ 2 + 2) ^ 2 := by
    have : (4 : ℕ) ^ t = 2 ^ t * 2 ^ t := by rw [← mul_pow]; norm_num
    rw [this]
    nlinarith
  have bt : ∀ i, Bit Uq (4 * (k ^ 2 + 2) ^ 2 * (2 * N)) fun τ => ((tl β i).map fun q => term β q i τ).sum := fun i =>
    (Bit.sum (fun q => term β q i) t (tl β i) (by simp [tl]) ((len i).trans ht1) (tb i)).mono (Nat.mul_le_mul_right _ h4)
  choose P Q hP hQ hPQ using bt
  have all := Rep.all (fun i x => Q i x) (Finset.univ : Finset (Fin k)).toList (by
    intro h0
    have : (⟨0, hk⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)).toList := by simp
    rw [h0] at this
    simp at this) fun i _ => hQ i
  have sX := two_side (V := (F × F) ⊕ (F × F)) β Sum.inl hk
  have sY := two_side (V := (F × F) ⊕ (F × F)) β Sum.inr hk
  have oX := Rep.set (V := (F × F) ⊕ (F × F)) (Sum.inl : F × F → _) (fun _ => True) ⟨0, trivial⟩
  have oY := Rep.set (V := (F × F) ⊕ (F × F)) (Sum.inr : F × F → _) (fun _ => True) ⟨0, trivial⟩
  refine ((sX.or (sY.or ((oX.and oY).and all))).mono (le_of_eq ?_)).congr fun x => ?_
  · rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]
    ring
  · unfold satf
    by_cases hX : ∃ a a' : F × F, a ≠ a' ∧ x (Sum.inl a) = true ∧ x (Sum.inl a') = true
    · exact ⟨fun _ => Or.inl hX, fun _ => Or.inl hX⟩
    by_cases hY : ∃ b b' : F × F, b ≠ b' ∧ x (Sum.inr b) = true ∧ x (Sum.inr b') = true
    · exact ⟨fun _ => Or.inr (Or.inl hY), fun _ => Or.inr (Or.inl hY)⟩
    refine or_congr_right (or_congr_right ?_)
    have uq : ∀ u w : F × F, x (Sum.inl u) = true → x (Sum.inr w) = true → Uq x (u, w) := by
      intro u w hu hw
      refine ⟨fun a => ⟨fun ha => ?_, fun ha => by rw [ha]; exact hu⟩, fun b => ⟨fun hb => ?_, fun hb => by rw [hb]; exact hw⟩⟩
      · by_contra hne; exact hX ⟨a, u, hne, ha, hu⟩
      · by_contra hne; exact hY ⟨b, w, hne, hb, hw⟩
    have key : ∀ u w : F × F, x (Sum.inl u) = true → x (Sum.inr w) = true → ((∀ i, Q i x) ↔ Hr u w) := by
      intro u w hu hw
      have hU := uq u w hu hw
      have e1 : ∀ i, Q i x ↔ β.repr (u.1 * w.1 + u.2 + w.2) i = 0 := fun i => by
        rw [← coord β i (u, w)]
        exact (hPQ i x (u, w) hU).2
      have e2 : (∀ i, Q i x) ↔ u.1 * w.1 + u.2 + w.2 = 0 := by
        rw [← β.repr.map_eq_zero_iff]
        constructor
        · intro h; exact Finsupp.ext fun i => (e1 i).1 (h i)
        · intro h i; rw [e1, h]; rfl
      have c2 : ∀ z : F, z + z = 0 := fun z => by
        have : (2 : ZMod 2) • z = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
        rw [← this, show (2 : ZMod 2) = 1 + 1 by decide, add_smul, one_smul]
      rw [e2, Hr]
      constructor
      · intro h; linear_combination h - c2 (u.2 + w.2)
      · intro h; linear_combination h + c2 (u.2 + w.2)
    constructor
    · rintro ⟨⟨⟨u, _, hu⟩, w, _, hw⟩, hq⟩
      exact ⟨u, w, (key u w hu hw).1 (fun i => hq i (by simp)), hu, hw⟩
    · rintro ⟨u, w, h, hu, hw⟩
      exact ⟨⟨⟨u, trivial, hu⟩, w, trivial, hw⟩, fun i _ => (key u w hu hw).2 h i⟩

end field

/-- The number of edges. -/
theorem card_Hr {F : Type} [Field F] [Fintype F] [DecidableEq F] [DecidablePred fun p : (F × F) × (F × F) => Hr p.1 p.2] :
    (Finset.univ.filter fun p : (F × F) × (F × F) => Hr p.1 p.2).card = Fintype.card F ^ 3 := by
  have : (Finset.univ.filter fun p : (F × F) × (F × F) => Hr p.1 p.2) = (Finset.univ : Finset (F × F × F)).map ⟨fun q => ((q.1, q.2.1), (q.2.2, q.1 * q.2.2 - q.2.1)), by
      rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1.1, h.1.2, h.2.1⟩⟩ := by
    ext ⟨⟨a, b⟩, c, d⟩
    rw [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨_, h⟩
      have h : a * c = b + d := h
      refine ⟨(a, b, c), Finset.mem_univ _, ?_⟩
      show ((a, b), (c, a * c - b)) = ((a, b), (c, d))
      rw [h, add_sub_cancel_left]
    · rintro ⟨⟨a', b', c'⟩, _, h⟩
      have h : ((a', b'), (c', a' * c' - b')) = ((a, b), (c, d)) := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
      refine ⟨Finset.mem_univ _, ?_⟩
      show a' * c' = b' + (a' * c' - b')
      ring
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_prod]
  ring

/-- An explicit polynomial gap: over `GF(2^k)`, `N = 4^k` vertices on each side, `N^(3/2)` edges `a c = b + d`, both sides made cliques.
The edge function has a monotone formula with at most `N * (8k + 2 + 8k(k^2+2)^2)` leaves, and every single-level monotone fan-in-two circuit for it has at least `N^(3/2) / 4` gates. -/
theorem gap (k : ℕ) (hk : 0 < k) :
    Rep (4 ^ k * (8 * k + 2 + 8 * k * (k ^ 2 + 2) ^ 2)) (satf (Hr (F := GaloisField 2 k))) ∧
    ∀ (m : ℕ) (C : Circ (GaloisField 2 k × GaloisField 2 k) (GaloisField 2 k × GaloisField 2 k) m), C.single →
      (∀ x, C.val x C.out = true ↔ satf Hr x) → 8 ^ k ≤ 4 * m := by
  classical
  have : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 2 k) = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 k hk.ne']
  constructor
  · have hd : Module.finrank (ZMod 2) (GaloisField 2 k) = k := GaloisField.finrank 2 hk.ne'
    have β : Module.Basis (Fin k) (ZMod 2) (GaloisField 2 k) := Module.finBasisOfFinrankEq _ _ hd
    have h := upper β hk
    have e : Fintype.card (GaloisField 2 k × GaloisField 2 k) = 4 ^ k := by
      rw [Fintype.card_prod, hc, ← mul_pow]; norm_num
    rw [e] at h
    exact h
  · intro m C hs hf
    have h := lower C Hr Hr_c4 hs hf
    rw [card_Hr, hc] at h
    calc 8 ^ k = (2 ^ k) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ 4 * m := h

end SingleLevelGap
