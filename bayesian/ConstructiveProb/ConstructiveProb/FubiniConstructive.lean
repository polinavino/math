/-
# Products are not unique, without ultrafilters

`ProductFreedom.lean` shows non-uniqueness of product valuations on `Set (ℕ × ℕ)` using a free
ultrafilter, which needs a choice principle. Here the same phenomenon is shown without choice, on
the Boolean algebra of *eventually order-determined* sets: `A ⊆ ℕ × ℕ` such that for all
`m, m' ≥ N` membership depends only on whether `m < m'`, `m = m'` or `m > m'`. The two iterated
limits, `L` (first `m' → ∞`, then `m → ∞`) and `R` (the other order), are `{0,1}`-valued Boolean
homomorphisms on this algebra, hence valuations. They agree on every rectangle `S × T` with `S`,
`T` eventually constant, where both give the product of the marginal limits, and they differ on
the triangle `{m < m'}`. Core Lean only; `#print axioms` reports at most `propext`.
-/

namespace ConstructiveProb.Fubini

/-- Eventually order-determined: for `m, m' ≥ N`, `A m m'` is `lt`, `eq` or `gt` according to
the order of `m` and `m'`. -/
structure EOD (A : Nat → Nat → Bool) where
  N : Nat
  lt : Bool
  eq : Bool
  gt : Bool
  spec : ∀ m m', N ≤ m → N ≤ m' →
    A m m' = if m < m' then lt else if m = m' then eq else gt

/-- The iterated limit with `m' → ∞` first. -/
def L {A : Nat → Nat → Bool} (w : EOD A) : Bool := w.lt
/-- The iterated limit with `m → ∞` first. -/
def R {A : Nat → Nat → Bool} (w : EOD A) : Bool := w.gt

/-- The limits do not depend on the witness. -/
theorem L_wd {A : Nat → Nat → Bool} (w w' : EOD A) : L w = L w' := by
  have h1 := w.spec (w.N + w'.N) (w.N + w'.N + 1) (by omega) (by omega)
  have h2 := w'.spec (w.N + w'.N) (w.N + w'.N + 1) (by omega) (by omega)
  rw [if_pos (by omega)] at h1 h2
  exact h1.symm.trans h2

theorem R_wd {A : Nat → Nat → Bool} (w w' : EOD A) : R w = R w' := by
  have h1 := w.spec (w.N + w'.N + 1) (w.N + w'.N) (by omega) (by omega)
  have h2 := w'.spec (w.N + w'.N + 1) (w.N + w'.N) (by omega) (by omega)
  rw [if_neg (by omega), if_neg (by omega)] at h1 h2
  exact h1.symm.trans h2

/-! ### Boolean operations -/

def union {A B : Nat → Nat → Bool} (a : EOD A) (b : EOD B) : EOD (fun m m' => A m m' || B m m') where
  N := a.N + b.N
  lt := a.lt || b.lt
  eq := a.eq || b.eq
  gt := a.gt || b.gt
  spec m m' h1 h2 := by
    rw [a.spec m m' (by omega) (by omega), b.spec m m' (by omega) (by omega)]
    split <;> (try split) <;> rfl

def inter {A B : Nat → Nat → Bool} (a : EOD A) (b : EOD B) : EOD (fun m m' => A m m' && B m m') where
  N := a.N + b.N
  lt := a.lt && b.lt
  eq := a.eq && b.eq
  gt := a.gt && b.gt
  spec m m' h1 h2 := by
    rw [a.spec m m' (by omega) (by omega), b.spec m m' (by omega) (by omega)]
    split <;> (try split) <;> rfl

def compl {A : Nat → Nat → Bool} (a : EOD A) : EOD (fun m m' => !A m m') where
  N := a.N
  lt := !a.lt
  eq := !a.eq
  gt := !a.gt
  spec m m' h1 h2 := by
    rw [a.spec m m' h1 h2]
    split <;> (try split) <;> rfl

theorem L_union {A B} (a : EOD A) (b : EOD B) : L (union a b) = (L a || L b) := rfl
theorem L_inter {A B} (a : EOD A) (b : EOD B) : L (inter a b) = (L a && L b) := rfl
theorem L_compl {A} (a : EOD A) : L (compl a) = !L a := rfl
theorem R_union {A B} (a : EOD A) (b : EOD B) : R (union a b) = (R a || R b) := rfl
theorem R_inter {A B} (a : EOD A) (b : EOD B) : R (inter a b) = (R a && R b) := rfl
theorem R_compl {A} (a : EOD A) : R (compl a) = !R a := rfl

/-- The `{0,1}` value. -/
def val (b : Bool) : Nat := if b then 1 else 0

/-- **`L` and `R` are modular.** -/
theorem L_modular {A B} (a : EOD A) (b : EOD B) :
    val (L a) + val (L b) = val (L (union a b)) + val (L (inter a b)) := by
  rw [L_union, L_inter]; cases L a <;> cases L b <;> rfl

theorem R_modular {A B} (a : EOD A) (b : EOD B) :
    val (R a) + val (R b) = val (R (union a b)) + val (R (inter a b)) := by
  rw [R_union, R_inter]; cases R a <;> cases R b <;> rfl

/-! ### Rectangles and the triangle -/

/-- An eventually constant subset of `ℕ`. -/
structure EC (S : Nat → Bool) where
  N : Nat
  v : Bool
  spec : ∀ m, N ≤ m → S m = v

/-- The rectangle `S × T`. -/
def rect {S T : Nat → Bool} (s : EC S) (t : EC T) : EOD (fun m m' => S m && T m') where
  N := s.N + t.N
  lt := s.v && t.v
  eq := s.v && t.v
  gt := s.v && t.v
  spec m m' h1 h2 := by
    rw [s.spec m (by omega), t.spec m' (by omega)]
    split <;> (try split) <;> rfl

/-- **Both iterated limits are product valuations**: on rectangles they give the product of the
marginal limits. -/
theorem rect_L {S T} (s : EC S) (t : EC T) : L (rect s t) = (s.v && t.v) := rfl
theorem rect_R {S T} (s : EC S) (t : EC T) : R (rect s t) = (s.v && t.v) := rfl

/-- The triangle `{m < m'}`. -/
def tri : EOD (fun m m' => decide (m < m')) where
  N := 0
  lt := true
  eq := false
  gt := false
  spec m m' _ _ := by
    by_cases h : m < m'
    · rw [if_pos h]; exact decide_eq_true h
    · rw [if_neg h]
      by_cases e : m = m'
      · rw [if_pos e]; exact decide_eq_false h
      · rw [if_neg e]; exact decide_eq_false h

/-- **The two product valuations differ.** -/
theorem tri_L : L tri = true := rfl
theorem tri_R : R tri = false := rfl

theorem products_differ : L tri ≠ R tri := by decide

end ConstructiveProb.Fubini
