/-
# Linear logic's obstruction: the modularity transplant collapses

`NonDistributive.lean` shows the sharp/point correspondence fails outright on `M3`, a bounded
lattice: distributivity, not completeness, is the real dividing line. This file asks the same
question one step further out: fixing completeness and distributivity but replacing the lattice
meet `⊓` in `LValuation`'s modularity axiom with a tensor `⊗`, linear logic's conjunction, that
need not be idempotent (`a ⊗ a ≠ a` in general, unlike `a ⊓ a = a`).

The answer is a collapse sharper than `M3`'s: not the absence of a sharp valuation on some
particular lattice, but every `v` satisfying the naive transplant of modularity is *forced* to
have `v (a ⊗ a) = v a`, for every `a`, regardless of how `Ω` and `⊗` are chosen. The proof needs
nothing about `⊗` beyond its appearance in the axiom -- no associativity, no distributivity over
`⊔`, no unit. So no valuation of this shape can ever separate `a` from `a ⊗ a`, exactly the
information a non-idempotent `⊗` exists to carry, and the `⊗`-analogue of
`LValuation.exists_sharp_separating` fails for every choice of `⊗`, not merely for a witnessed
counterexample as `M3` was for `⊓`.
-/
import Mathlib.Order.Lattice
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.ENNReal.Operations

open scoped ENNReal

noncomputable section

variable {Ω : Type*} [SemilatticeSup Ω]

/-- The naive transplant of `LValuation`'s modularity axiom, substituting a binary operation `t`
(linear logic's `⊗`, kept fully abstract) for the lattice meet. -/
def IsTensorValuation (v : Ω → ℝ≥0∞) (t : Ω → Ω → Ω) : Prop :=
  ∀ a b, v a + v b = v (a ⊔ b) + v (t a b)

/-- **The transplant forces collapse.** Any `v` satisfying the naive `⊗`-modularity axiom cannot
distinguish `a` from `t a a`, for every `a` of finite value. Setting `b := a` and using only
`a ⊔ a = a` already gives it, before any hypothesis on `t` is used. -/
theorem IsTensorValuation.collapse {v : Ω → ℝ≥0∞} {t : Ω → Ω → Ω} (h : IsTensorValuation v t)
    {a : Ω} (ha : v a ≠ ⊤) : v (t a a) = v a := by
  have hself := h a a
  rw [sup_idem] at hself
  exact ((ENNReal.add_right_inj ha).mp hself).symm

/-- No valuation satisfying the transplanted axiom separates `a` from `t a a`, even when they
genuinely differ: the collapse above holds independently of whether `t a a = a`. -/
theorem IsTensorValuation.not_separating {v : Ω → ℝ≥0∞} {t : Ω → Ω → Ω}
    (h : IsTensorValuation v t) {a : Ω} (ha : v a ≠ ⊤) : v a = v (t a a) :=
  (h.collapse ha).symm

/-- **The dichotomy, as a joint impossibility.** No `v` can both satisfy the transplanted
modularity axiom for `t` and discriminate some finite-valued `a` from `t a a`. This is the
sharpest way to say what `collapse` forces: grading a non-idempotent `t` with this paper's
compositional law, and keeping the one distinction a non-idempotent `t` exists to make, are
mutually exclusive for every `Ω`, every `t`, and every `a` -- a candidate probabilistic semantics
for `t` must give up one or the other, not by design choice but by proof. -/
theorem not_isTensorValuation_of_discriminates {v : Ω → ℝ≥0∞} {t : Ω → Ω → Ω} {a : Ω}
    (ha : v a ≠ ⊤) (hne : v (t a a) ≠ v a) : ¬ IsTensorValuation v t :=
  fun h => hne (h.collapse ha)

end

/-! ## A concrete, non-idempotent witness

`(ℕ, max, +)` is a genuine instance of the shape above: `max` is the lattice join, and `+` is
associative and commutative but not idempotent (`1 + 1 = 2 ≠ 1`), exactly linear logic's `⊗`
shape, so the hypothesis of `IsTensorValuation.collapse` is not vacuous. Running the same
substitution at `a = 0`, the join and tensor unit coincide, forces every such `v` constant. -/

theorem forced_constant_of_add_valuation {v : ℕ → ℝ≥0∞} (h : IsTensorValuation v (· + ·))
    (hfin : ∀ n, v n ≠ ⊤) (n : ℕ) : v n = v 0 := by
  have h0 := h 0 n
  simp only [Nat.max_eq_right (Nat.zero_le n), Nat.zero_add] at h0
  exact ((ENNReal.add_left_inj (hfin n)).mp h0).symm

theorem not_isTensorValuation_of_ne_const {v : ℕ → ℝ≥0∞} (hfin : ∀ n, v n ≠ ⊤)
    {m n : ℕ} (hmn : v m ≠ v n) : ¬ IsTensorValuation v (· + ·) := by
  intro h
  exact hmn ((forced_constant_of_add_valuation h hfin m).trans
    (forced_constant_of_add_valuation h hfin n).symm)
