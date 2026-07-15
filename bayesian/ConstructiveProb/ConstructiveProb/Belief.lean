/-
# The Dempster–Shafer bridge: a valuation is a 2-monotone capacity on its Booleanization

README §4 flags a frontier: the double-negation nucleus `A ↦ Aᶜᶜ` sends a frame onto its
**Booleanization** — the regular (`¬¬`-stable) elements, which form a genuine Boolean algebra à la
Glivenko, with meet `⊓`, join `A ⊔_B B := (A ⊔ B)ᶜᶜ`, and complement `¬`. Restricted there, a
valuation should be a **Dempster–Shafer belief function**. This file turns the defining inequality
of that claim into a theorem.

**What is proved.** For *every* valuation and *all* `a, b`,

  `v a + v b ≤ v (a ⊔ b)ᶜᶜ + v (a ⊓ b)`.

Read on the regular elements — where `(a ⊔ b)ᶜᶜ` *is* the join and `a ⊓ b` *is* the meet — this is
exactly **2-monotonicity (supermodularity)**: `Bel(a ∨ b) + Bel(a ∧ b) ≥ Bel a + Bel b`, the
hallmark inequality of a Dempster–Shafer belief function. The proof is a one-liner: modularity
turns `v a + v b` into `v(a ⊔ b) + v(a ⊓ b)`, and monotonicity lifts `a ⊔ b` up to its double
negation `(a ⊔ b)ᶜᶜ ≥ a ⊔ b`. The inequality's *defect* is precisely the double-negation gap
`v(a⊔b)ᶜᶜ − v(a⊔b)` — the same non-classicality measured elsewhere in the development.

**Intuitively:** passing to the Booleanization "rounds each proposition up to its regular core",
which can only *add* plausibility to a disjunction; so inclusion–exclusion, an equality on the
frame, becomes a one-sided inequality on the Boolean algebra — and that one-sidedness *is* what
makes the result a belief function rather than an additive probability.

**Belief and plausibility.** With `Bel = v` and the dual `Pl a := 1 − v aᶜ`, the
belief–plausibility interval `[Bel a, Pl a]` has width exactly the **slack**: `Pl a − v a =
slack a` — the Dempster–Shafer "ignorance", here a structural quantity (`= μ(∂A)` in the measure
model), not anyone's hesitation.

**The full tower.** A *bona fide* DS belief function is `∞`-monotone (totally monotone), a family
of inequalities indexed by finite subsets. This file proves the `2`-monotone case (the standard
convex-capacity hallmark); `InclusionExclusion.lean` closes the rest of the tower
(`Valuation.infty_monotone`), by the same one-line mechanism applied to the full
inclusion–exclusion identity — which holds *with equality* on the frame join
(`Valuation.inclusion_exclusion`).
-/
import ConstructiveProb.Basic

open scoped ENNReal

namespace ConstructiveProb

variable {Ω : Type*} [Order.Frame Ω]

/-- **Two-monotonicity — the belief-function inequality.** For every valuation and all `a, b`,
`v a + v b ≤ v (a ⊔ b)ᶜᶜ + v (a ⊓ b)`. On the regular elements (the Booleanization), where
`(a ⊔ b)ᶜᶜ` is the Boolean join, this reads `Bel(a ∨ b) + Bel(a ∧ b) ≥ Bel a + Bel b`: `v` is a
**2-monotone (supermodular) capacity**, i.e. a Dempster–Shafer belief function (its defining
convex-capacity inequality). Proof: modularity plus `a ⊔ b ≤ (a ⊔ b)ᶜᶜ`. -/
theorem Valuation.two_monotone (v : Valuation Ω) (a b : Ω) :
    v a + v b ≤ v (a ⊔ b)ᶜᶜ + v (a ⊓ b) := by
  rw [v.modular a b]
  gcongr
  exact v.mono le_compl_compl

/-- The **plausibility** dual of a valuation: `Pl a := 1 − v aᶜ`. With `Bel = v`, the pair
`(Bel a, Pl a) = (v a, 1 − v aᶜ)` is the Dempster–Shafer belief/plausibility interval. -/
noncomputable def Valuation.plausibility (v : Valuation Ω) (a : Ω) : ℝ≥0∞ := 1 - v aᶜ

/-- **Belief never exceeds plausibility:** `v a ≤ Pl a`. This is the Dempster–Shafer inequality
`Bel a ≤ Pl a`, just `v a + v aᶜ ≤ 1` rearranged. -/
theorem Valuation.self_le_plausibility (v : Valuation Ω) (a : Ω) :
    v a ≤ v.plausibility a := by
  have h : v a + v aᶜ ≤ 1 := add_compl_le_one v a
  have hfin : v aᶜ ≠ ∞ := (lt_of_le_of_lt (v.le_one aᶜ) ENNReal.one_lt_top).ne
  calc v a = (v a + v aᶜ) - v aᶜ := (ENNReal.add_sub_cancel_right hfin).symm
    _ ≤ 1 - v aᶜ := tsub_le_tsub_right h (v aᶜ)
    _ = v.plausibility a := rfl

/-- **The belief–plausibility interval has width exactly the slack:** `Pl a − Bel a = slack a`. The
Dempster–Shafer "ignorance" is the constructive slack `1 − (v a + v aᶜ)` — a structural quantity,
not an agent's uncertainty. -/
theorem Valuation.plausibility_sub_self (v : Valuation Ω) (a : Ω) :
    v.plausibility a - v a = v.slack a := by
  unfold Valuation.plausibility Valuation.slack
  rw [tsub_tsub, add_comm (v aᶜ) (v a)]

end ConstructiveProb
