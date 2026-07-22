/-
# Constructive Probability — formalisation scaffold

Companion to `../probability_philosophy_handoff.md`.

## The thesis, stated so a machine can check it

The Cox tradition derives probability from desiderata on "plausibility": under suitable
regularity axioms (Cox 1946, as repaired post-Halpern 1999 by Van Horn and by
Arnborg–Sjödin), any consistent extension of **classical** logic to degrees of certainty
is — *up to a monotone rescaling* — the probability calculus. Paris–Vencovská separately
single out the maximum-entropy prior as the unique inference process. Neither result gives a
literally unique formula: both fix an isomorphism class under an explicit axiom set, and the
naive unqualified "uniqueness" is false (Halpern's finite counterexamples). What is robust is
the boundary condition: in every case the {0,1}-valued limit is a **Boolean algebra**, where
`P a + P aᶜ = 1` (Kolmogorov additivity).

We change one boundary condition. We ask for the calculus whose certainty limit is
**constructive (intuitionistic) logic**, whose algebra is a **Heyting algebra**
(here: a `Order.Frame`, i.e. a complete Heyting algebra — the locale of an
"epistemic situation"). A Heyting algebra has *no involutive negation*:
`a ⊔ aᶜ = ⊤` fails in general, though `a ⊓ aᶜ = ⊥` still holds.

Central prediction of the handoff doc (§7.3): dropping excluded middle forces the
measure to be **non-additive on complements** — `P a + P aᶜ ≤ 1`, with a gap. The
resulting object coincides with what Dempster–Shafer theory calls a *belief function* —
but here the gap carries **no epistemic reading**: it is a structural quantity, the
valuation of the region excluded middle leaves undecided (concretely, the measure of a
topological boundary — see the GMT section), not anyone's "ignorance". Failure of excluded
middle ⟺ failure of complement-additivity. Below this is not a slogan: `add_compl_le_one`
proves the ≤,
and `classical_additivity` proves that the gap closes to 0 *exactly* in the Boolean
(classical-logic) case.

## Library surface we build on (all from mathlib v4.31.0)

* `Order.Frame`              — complete Heyting algebra = a locale (extends `HeytingAlgebra`).
* `inf_compl_eq_bot`         — `a ⊓ aᶜ = ⊥` in any Heyting algebra.
* `sup_compl_eq_top`         — `a ⊔ aᶜ = ⊤`, available *only* in Boolean algebras.
* `Order.PrimeSeparator`     — the prime-ideal separation theorem, used to build a slack-carrying
                               valuation wherever excluded middle fails (`sharp_iff_point`, the
                               hard direction of the R3 hinge).
* `ENNReal` (`ℝ≥0∞`)         — value type for the valuation.
* `Mathlib.Topology.Sets.Opens` — `Opens X` is the canonical locale (opens of a space);
                               its logic is intuitionistic. Our running example of an
                               epistemic situation, and the setting of the GMT bridge.

(The `¬¬`-stable *regular* elements — `Mathlib.Order.Heyting.Regular` — are **not** used: they
look like the classical fragment but are not (see "The classical (Kolmogorov) fragment" below);
the fragment on which `v` is genuinely additive is the *complemented* elements.)
-/
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.PrimeIdeal
import Mathlib.Order.PrimeSeparator
import Mathlib.Topology.Sets.Opens
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open scoped ENNReal

namespace ConstructiveProb

variable {Ω : Type*}

/-- A **plausibility valuation** on a frame `Ω` (the locale of an epistemic situation).

This is the constructive analogue of a finitely-additive probability: the additivity we
*keep* after dropping complements is the lattice-theoretic **modular law**
`v a + v b = v (a ⊔ b) + v (a ⊓ b)`, which is the natural form of inclusion–exclusion on a
locale (the finite shadow of a Scott-continuous localic valuation). We deliberately do
*not* assume `v aᶜ = 1 - v a`; whether that holds is governed by excluded middle. -/
structure Valuation (Ω : Type*) [Order.Frame Ω] where
  toFun : Ω → ℝ≥0∞
  map_bot' : toFun ⊥ = 0
  map_top' : toFun ⊤ = 1
  mono' : Monotone toFun
  modular' : ∀ a b, toFun a + toFun b = toFun (a ⊔ b) + toFun (a ⊓ b)

namespace Valuation

variable [Order.Frame Ω]

instance : CoeFun (Valuation Ω) (fun _ => Ω → ℝ≥0∞) := ⟨toFun⟩

@[simp] theorem map_bot (v : Valuation Ω) : v ⊥ = 0 := v.map_bot'
@[simp] theorem map_top (v : Valuation Ω) : v ⊤ = 1 := v.map_top'
theorem mono (v : Valuation Ω) : Monotone v := v.mono'
theorem modular (v : Valuation Ω) (a b : Ω) : v a + v b = v (a ⊔ b) + v (a ⊓ b) :=
  v.modular' a b

theorem le_one (v : Valuation Ω) (a : Ω) : v a ≤ 1 := by
  simpa using v.mono (le_top : a ≤ ⊤)

/-- **The complement identity.** Modularity plus `a ⊓ aᶜ = ⊥` collapses the meet term, so
`v a + v aᶜ` measures exactly the join `a ⊔ aᶜ` — the "instance of excluded middle" for `a`. -/
theorem add_compl_eq_sup (v : Valuation Ω) (a : Ω) : v a + v aᶜ = v (a ⊔ aᶜ) := by
  have h := v.modular a aᶜ
  rwa [inf_compl_eq_bot, v.map_bot, add_zero] at h

/-- **Constructive sub-additivity (proved).** Because `a ⊔ aᶜ` need not be `⊤`, complements
can under-shoot: `v a + v aᶜ ≤ 1`. This is the Dempster–Shafer inequality, here *derived*
from intuitionistic logic rather than posited. -/
theorem add_compl_le_one (v : Valuation Ω) (a : Ω) : v a + v aᶜ ≤ 1 := by
  rw [add_compl_eq_sup]; simpa using v.le_one (a ⊔ aᶜ)

/-- Excluded middle *for `a`* (i.e. `a` is complemented, `a ⊔ aᶜ = ⊤`) forces additivity of
the complement. The gap is closed pointwise exactly where classical logic is recovered. -/
theorem add_compl_eq_one_of_sup_eq_top (v : Valuation Ω) {a : Ω} (h : a ⊔ aᶜ = ⊤) :
    v a + v aᶜ = 1 := by
  rw [add_compl_eq_sup, h, v.map_top]

/-- The **constructive slack** at `a`: the amount by which excluded middle fails for `a`,
i.e. by which `v (a ⊔ aᶜ)` falls short of `v ⊤`. `slack v a = 0` iff `v (a ⊔ aᶜ) = 1`. This
is the gap that Dempster–Shafer theory would call "ignorance", but structurally it is just the
valuation of the undecided region (the measure of a boundary — see the GMT section); no
epistemic subject is implied. -/
noncomputable def slack (v : Valuation Ω) (a : Ω) : ℝ≥0∞ := 1 - (v a + v aᶜ)

theorem slack_eq_one_sub_sup (v : Valuation Ω) (a : Ω) : v.slack a = 1 - v (a ⊔ aᶜ) := by
  rw [slack, add_compl_eq_sup]

/-! ### Decomposing the slack via the `(¬¬a, ¬a)` pair

The pair `(aᶜᶜ, aᶜ)` = `(¬¬a, ¬a)` is **disjoint** (`aᶜᶜ ⊓ aᶜ = ⊥` always) but generally **not a
partition** (`aᶜᶜ ⊔ aᶜ = ⊤` is weak excluded middle, not a theorem). Running the disjoint pair
through modularity splits the Dempster–Shafer slack into two logically independent gaps:
`slack a = (v aᶜᶜ − v a) + (1 − v aᶜᶜ − v aᶜ)`. -/

/-- The **double-negation gap** at `a`: `v aᶜᶜ − v a ≥ 0`, by which `a` falls short of its
regularization `¬¬a = aᶜᶜ`. Zero when `a` is regular (`aᶜᶜ = a`). -/
noncomputable def dnGap (v : Valuation Ω) (a : Ω) : ℝ≥0∞ := v aᶜᶜ - v a

/-- The **De Morgan gap** (weak-excluded-middle gap) at `a`: `1 − (v aᶜᶜ + v aᶜ) ≥ 0`, by which
the *dense* element `aᶜᶜ ⊔ aᶜ` falls short of `⊤`. Zero when `aᶜᶜ ⊔ aᶜ = ⊤`. -/
noncomputable def deMorganGap (v : Valuation Ω) (a : Ω) : ℝ≥0∞ := 1 - (v aᶜᶜ + v aᶜ)

/-- `¬¬a` and `¬a` are disjoint (`aᶜᶜ ⊓ aᶜ = ⊥`), so modularity makes their valuations add to
the join — the mirror of `add_compl_eq_sup`, one level up in double negation. -/
theorem add_compl_compl_eq_sup (v : Valuation Ω) (a : Ω) : v aᶜᶜ + v aᶜ = v (aᶜᶜ ⊔ aᶜ) := by
  have hdisj : aᶜᶜ ⊓ aᶜ = ⊥ := by rw [inf_comm]; exact inf_compl_eq_bot
  have h := v.modular aᶜᶜ aᶜ
  rwa [hdisj, v.map_bot, add_zero] at h

/-- **The slack decomposition.** The Dempster–Shafer slack at `a` splits canonically into the
**double-negation gap** (how far `a` is from regular) and the **De Morgan gap** (how far weak
excluded middle fails): `slack a = dnGap a + deMorganGap a`. Both summands are `≥ 0`, and the
`v aᶜᶜ` term telescopes away. This resolves the single "ignorance" number into two logically
independent obstructions. -/
theorem slack_eq_dnGap_add_deMorganGap (v : Valuation Ω) (a : Ω) :
    v.slack a = v.dnGap a + v.deMorganGap a := by
  have hle1 : v a ≤ v aᶜᶜ := v.mono le_compl_compl
  have hle2 : v aᶜᶜ + v aᶜ ≤ 1 := by rw [add_compl_compl_eq_sup]; exact v.le_one _
  have hb : v a + v aᶜ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (add_compl_le_one v a)
  rw [slack, dnGap, deMorganGap]
  refine (ENNReal.sub_eq_of_eq_add hb ?_)
  -- reduce to the additive identity `1 = (dnGap + deMorganGap) + (v a + v aᶜ)`
  rw [show v aᶜᶜ - v a + (1 - (v aᶜᶜ + v aᶜ)) + (v a + v aᶜ)
        = (v aᶜᶜ - v a + v a) + ((1 - (v aᶜᶜ + v aᶜ)) + v aᶜ) from by ring,
      tsub_add_cancel_of_le hle1,
      show v aᶜᶜ + ((1 - (v aᶜᶜ + v aᶜ)) + v aᶜ)
        = (1 - (v aᶜᶜ + v aᶜ)) + (v aᶜᶜ + v aᶜ) from by ring,
      tsub_add_cancel_of_le hle2]

/-- The double-negation gap vanishes on regular elements (`aᶜᶜ = a`). -/
theorem dnGap_eq_zero_of_regular (v : Valuation Ω) {a : Ω} (ha : aᶜᶜ = a) : v.dnGap a = 0 := by
  rw [dnGap, ha, tsub_self]

/-- The De Morgan gap vanishes when weak excluded middle holds at `a` (`aᶜᶜ ⊔ aᶜ = ⊤`). -/
theorem deMorganGap_eq_zero_of_sup_eq_top (v : Valuation Ω) {a : Ω} (h : aᶜᶜ ⊔ aᶜ = ⊤) :
    v.deMorganGap a = 0 := by
  rw [deMorganGap, add_compl_compl_eq_sup, h, v.map_top, tsub_self]

/-- **For a regular element, all the slack is the De Morgan gap.** The double-negation gap is
then `0`, so `slack a = deMorganGap a = 1 − v (a ⊔ aᶜ)`. This is exactly why a valuation can still
carry slack on a *regular but uncomplemented* element: regularity kills one obstruction, not the
other. -/
theorem slack_eq_deMorganGap_of_regular (v : Valuation Ω) {a : Ω} (ha : aᶜᶜ = a) :
    v.slack a = v.deMorganGap a := by
  rw [slack_eq_dnGap_add_deMorganGap, dnGap_eq_zero_of_regular v ha, zero_add]

/-- The slack is zero exactly when *both* obstructions vanish. -/
theorem slack_eq_zero_iff (v : Valuation Ω) (a : Ω) :
    v.slack a = 0 ↔ v.dnGap a = 0 ∧ v.deMorganGap a = 0 := by
  rw [slack_eq_dnGap_add_deMorganGap, add_eq_zero]

end Valuation

/-! ## Convex combinations of valuations

The defining properties of a valuation — `v ⊥ = 0`, `v ⊤ = 1`, monotonicity, and above all the
modular law `v a + v b = v(a ⊔ b) + v(a ⊓ b)` — are all **linear** in `v`. So the valuations form
a **convex set**: an average of valuations (weights summing to one) is again a valuation, with no
new hypothesis required.

Intuitively, if you have several candidate "ways the uncertainty could be structured", any weighted
blend of them is itself such a way. Technically, this is the engine behind the mixture
characterization (`Valuation.eq_mix_deltaPoint`, in `Representation.lean`): because modularity
survives averaging, the point-additive *sharp* valuations can be blended freely and the blend stays
modular. That is the honest sense in which modularity is the "mixing-closure" of point additivity —
the constructive replacement for Van Horn's negation axiom R3 that `SumIrreducible.lean` shows
cannot be recovered from the disjunction data. -/

section ConvexStructure
open scoped BigOperators
variable [Order.Frame Ω] {ι : Type*} [Fintype ι]

/-- **A finite mixture of valuations is a valuation.** For weights `w : ι → ℝ≥0∞` summing to `1`
and a family of valuations `v i`, the affine combination `a ↦ ∑ i, w i · v i a` is again a
valuation. Every axiom is inherited term-by-term because each is linear in the valuation — in
particular modularity, which is why mixing requires no extra hypothesis. -/
noncomputable def Valuation.mix (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1) (v : ι → Valuation Ω) :
    Valuation Ω where
  toFun a := ∑ i, w i * v i a
  map_bot' := by simp only [Valuation.map_bot, mul_zero, Finset.sum_const_zero]
  map_top' := by simp only [Valuation.map_top, mul_one]; exact hw
  mono' a b hab := by
    refine Finset.sum_le_sum fun i _ => ?_
    gcongr
    exact (v i).mono hab
  modular' a b := by
    have h : ∀ i, w i * v i a + w i * v i b
        = w i * v i (a ⊔ b) + w i * v i (a ⊓ b) := fun i => by
      rw [← mul_add, ← mul_add, (v i).modular a b]
    calc (∑ i, w i * v i a) + ∑ i, w i * v i b
        = ∑ i, (w i * v i a + w i * v i b) := (Finset.sum_add_distrib).symm
      _ = ∑ i, (w i * v i (a ⊔ b) + w i * v i (a ⊓ b)) := Finset.sum_congr rfl fun i _ => h i
      _ = (∑ i, w i * v i (a ⊔ b)) + ∑ i, w i * v i (a ⊓ b) := Finset.sum_add_distrib

@[simp] theorem Valuation.mix_apply (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1) (v : ι → Valuation Ω)
    (a : Ω) : Valuation.mix w hw v a = ∑ i, w i * v i a := rfl

end ConvexStructure

/-! ## Classical limit: recovering Kolmogorov (proved)

When the logic is classical — `Ω` a complete Boolean algebra — every element is
complemented, so `add_compl_eq_one_of_sup_eq_top` applies uniformly and the slack
vanishes identically. This is the "Cox direction" of the thesis, machine-checked:
Boolean boundary condition ⟹ Kolmogorov complement rule. -/
section Classical
variable [CompleteBooleanAlgebra Ω]

/-- In the classical (Boolean) limit the valuation is complement-additive: `v a + v aᶜ = 1`
for every `a`. Excluded middle is exactly what closes the constructive gap. -/
theorem classical_additivity (v : Valuation Ω) (a : Ω) : v a + v aᶜ = 1 :=
  v.add_compl_eq_one_of_sup_eq_top (sup_compl_eq_top)

/-- Equivalently: the slack is identically zero when the logic is classical. -/
theorem classical_slack_zero (v : Valuation Ω) (a : Ω) : v.slack a = 0 := by
  rw [Valuation.slack, classical_additivity, tsub_self]

end Classical

/-! ## The Cox program: axioms and the regraduation theorem

The statements below are the conjectures from the handoff document, now pinned down and
**proved** (the section is `sorry`-free). `constructive_cox` is the central result; the
computability guard (`Halting.lean`) and the irreducibility of modularity
(`SumIrreducible.lean`) certify that its hypotheses are the right, non-collapsing ones. -/

section CoxProgram
variable [Order.Frame Ω]

/-- On any **chain** (`CompleteLinearOrder`), a non-bottom element pseudo-complements
*downward*: `m ≠ ⊥ → mᶜ ≤ m`, because `m ≤ mᶜ` would make `m` self-disjoint, i.e. `m = ⊥`.
This is exactly where excluded middle dies: `m ⊔ mᶜ = m ≠ ⊤`. -/
theorem compl_le_self_of_ne_bot {α : Type*} [CompleteLinearOrder α]
    {m : α} (hm : m ≠ ⊥) : mᶜ ≤ m := by
  rcases le_total mᶜ m with h | h
  · exact h
  · exact absurd (disjoint_self.mp (le_compl_iff_disjoint_right.mp h)) hm

/-- A concrete valuation on the complete chain `ℝ≥0∞`: the indicator `v x = 1` iff `x = ⊤`,
else `0`. Monotone, `v ⊥ = 0`, `v ⊤ = 1`, and modular for free — on a chain the pair `{a, b}`
equals `{a ⊔ b, a ⊓ b}` as a multiset, so *any* monotone map is modular. -/
noncomputable def chainVal : Valuation ℝ≥0∞ where
  toFun x := if x = ⊤ then 1 else 0
  map_bot' := by simp
  map_top' := by simp
  mono' a b h := by
    change (if a = ⊤ then (1 : ℝ≥0∞) else 0) ≤ if b = ⊤ then 1 else 0
    split_ifs with ha hb hb
    · exact le_rfl
    · rw [ha] at h; exact absurd (top_le_iff.mp h) hb
    · exact zero_le
    · exact le_rfl
  modular' a b := by
    rcases le_total a b with h | h
    · rw [sup_eq_right.mpr h, inf_eq_left.mpr h, add_comm]
    · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]

@[simp] theorem chainVal_apply (x : ℝ≥0∞) : chainVal x = if x = ⊤ then 1 else 0 := rfl

/-- **Non-triviality of the constructive gap (proved).** On the chain `ℝ≥0∞`, the element `1`
carries slack `1`: `1ᶜ = ⊥`, so `1 ⊔ 1ᶜ = 1 ≠ ⊤`, and `slack = 1 − v 1 = 1 − 0 = 1 > 0`.
Modularity does *not* secretly force additivity — the program is not vacuous. -/
theorem exists_positive_slack :
    ∃ (Ω : Type) (_ : Order.Frame Ω) (v : Valuation Ω) (a : Ω), 0 < v.slack a :=
  ⟨ℝ≥0∞, inferInstance, chainVal, 1, by
    have hsup : (1 : ℝ≥0∞) ⊔ (1 : ℝ≥0∞)ᶜ = 1 :=
      sup_eq_left.mpr (compl_le_self_of_ne_bot (by simp))
    rw [chainVal.slack_eq_one_sub_sup, hsup, chainVal_apply, if_neg ENNReal.one_ne_top]
    simp⟩

/-- A valuation is **sharp** if it is {0,1}-valued: the certainty limit. -/
def Valuation.IsSharp (v : Valuation Ω) : Prop := ∀ a, v a = 0 ∨ v a = 1

-- `sharp_iff_point` (sharp valuations ↔ prime ideals = points of the locale) is proved
-- further down, once `Ideal.toValuation` is available.

/-! ### The classical (Kolmogorov) fragment

Where does honest additive probability live inside the constructive theory?

**Correction forced by formalization.** The natural guess — "the `¬¬`-stable (*regular*)
elements" — is **wrong** for additivity. `v`'s modularity is with respect to the *frame* join
`⊔`, whereas the Boolean algebra of regulars uses the *regularized* join `(·⊔·)ᶜᶜ`. For a
regular `a`, `a ⊔ aᶜ` need not be `⊤` (regular ⊋ complemented), so `v a + v aᶜ = v(a ⊔ aᶜ)`
can still be `< 1`. Concretely, the open ray `(-∞,0)` in the locale of opens of `ℝ` is regular
but not complemented, and an *atomic* valuation with mass at `0` gives `v a + v aᶜ = 1 − v{0} < 1`.

The correct fragment is the **complemented** elements — those satisfying excluded middle
`a ⊔ aᶜ = ⊤`. On a connected locale this can be as small as `{⊥, ⊤}`: the classical part of a
constructive probability may be trivial. -/

/-- **Disjoint additivity** (unconditional): the additive core survives without excluded
middle. `a ⊓ b = ⊥ → v(a ⊔ b) = v a + v b`. -/
theorem Valuation.additive_of_disjoint (v : Valuation Ω) {a b : Ω} (h : a ⊓ b = ⊥) :
    v (a ⊔ b) = v a + v b := by
  have hm := v.modular a b
  rw [h, v.map_bot, add_zero] at hm
  exact hm.symm

/-- **The Kolmogorov fragment.** On the complemented elements (`a ⊔ aᶜ = ⊤`, i.e. excluded
middle holds for `a`), `v` obeys the classical complement law `v a + v aᶜ = 1`. This — not the
regular fragment — is how ordinary additive probability lives inside the constructive theory. -/
theorem Valuation.add_compl_eq_one_of_complemented (v : Valuation Ω) {a : Ω}
    (ha : a ⊔ aᶜ = ⊤) : v a + v aᶜ = 1 :=
  v.add_compl_eq_one_of_sup_eq_top ha

/-- The complemented elements are closed under complement (a step toward "they form a Boolean
sub-algebra"): if `a` satisfies excluded middle, so does `aᶜ`, since `a ≤ aᶜᶜ`. -/
theorem isComplemented_compl {a : Ω} (ha : a ⊔ aᶜ = ⊤) : aᶜ ⊔ aᶜᶜ = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← ha]
  exact sup_le (le_compl_compl.trans le_sup_right) le_sup_left

/-! ### Conditioning and the product rule (Cox's R2, on the valuation)

Bayesian updating is native. Conditioning renormalises the valuation below `b`, stays a
`Valuation` (this step uses frame distributivity), and the product rule and Bayes symmetry
hold — the content of Cox's R2, here *proved* of the localic modular valuation rather than
assumed. What genuinely fails constructively is total probability over `{a, aᶜ}`: they do not
tile `⊤`, so the conditional masses fall short of `v b` by the conditional slack
`v b − v ((a ⊔ aᶜ) ⊓ b)`. -/

theorem Valuation.ne_top (v : Valuation Ω) (a : Ω) : v a ≠ ⊤ :=
  ((v.le_one a).trans_lt ENNReal.one_lt_top).ne

/-- The **posterior** `v(· | b)`, conditioning on an element of positive plausibility, defined
by the ratio `v(a ⊓ b) / v b`. Again a valuation: `map_top'` renormalises to `1`, and
modularity uses frame distributivity to push `· ⊓ b` through `⊔`/`⊓`. -/
noncomputable def Valuation.condVal (v : Valuation Ω) (b : Ω) (hb : v b ≠ 0) : Valuation Ω where
  toFun a := v (a ⊓ b) / v b
  map_bot' := by rw [bot_inf_eq, v.map_bot, ENNReal.zero_div]
  map_top' := by rw [top_inf_eq]; exact ENNReal.div_self hb (v.ne_top b)
  mono' a a' h := ENNReal.div_le_div_right (v.mono (inf_le_inf_right b h)) _
  modular' a a' := by
    have h : v (a ⊓ b) + v (a' ⊓ b) = v ((a ⊔ a') ⊓ b) + v ((a ⊓ a') ⊓ b) := by
      have hmod := v.modular (a ⊓ b) (a' ⊓ b)
      rwa [← inf_sup_right, inf_inf_inf_comm, inf_idem] at hmod
    change v (a ⊓ b) / v b + v (a' ⊓ b) / v b
        = v ((a ⊔ a') ⊓ b) / v b + v ((a ⊓ a') ⊓ b) / v b
    rw [← ENNReal.add_div, ← ENNReal.add_div, h]

@[simp] theorem Valuation.condVal_apply (v : Valuation Ω) (b : Ω) (hb : v b ≠ 0) (a : Ω) :
    v.condVal b hb a = v (a ⊓ b) / v b := rfl

/-- **Product rule** (Cox's R2): `v(a | b) · v b = v(a ⊓ b)`. -/
theorem Valuation.condVal_mul (v : Valuation Ω) (b : Ω) (hb : v b ≠ 0) (a : Ω) :
    v.condVal b hb a * v b = v (a ⊓ b) := by
  rw [Valuation.condVal_apply, div_eq_mul_inv, mul_assoc,
      ENNReal.inv_mul_cancel hb (v.ne_top b), mul_one]

/-- **Bayes symmetry**: `v(a | b) · v b = v(b | a) · v a` (both equal `v(a ⊓ b)`). -/
theorem Valuation.condVal_symm (v : Valuation Ω) {a b : Ω} (ha : v a ≠ 0) (hb : v b ≠ 0) :
    v.condVal b hb a * v b = v.condVal a ha b * v a := by
  rw [v.condVal_mul b hb a, v.condVal_mul a ha b, inf_comm]

/-- The conditional masses of `a` and `aᶜ` given `b` sum to `v` of the join `(a ⊔ aᶜ) ⊓ b`. -/
theorem Valuation.cond_add_compl (v : Valuation Ω) (a b : Ω) :
    v (a ⊓ b) + v (aᶜ ⊓ b) = v ((a ⊔ aᶜ) ⊓ b) := by
  have hd : (a ⊓ b) ⊓ (aᶜ ⊓ b) = ⊥ := by
    rw [inf_inf_inf_comm, inf_compl_eq_bot, bot_inf_eq]
  rw [inf_sup_right]
  exact (v.additive_of_disjoint hd).symm

/-- **Total probability fails over `{a, aᶜ}`.** Because `a ⊔ aᶜ ≠ ⊤`, the conditional masses
fall short of `v b`; the gap `v b − v((a ⊔ aᶜ) ⊓ b)` is the (conditional) slack. -/
theorem Valuation.cond_add_compl_le (v : Valuation Ω) (a b : Ω) :
    v (a ⊓ b) + v (aᶜ ⊓ b) ≤ v b := by
  rw [v.cond_add_compl]; exact v.mono inf_le_right

/-- **Total probability over a genuine partition (prediction works).** If `a` and `a'` really
tile `⊤` — disjoint (`a ⊓ a' = ⊥`) *and* exhaustive (`a ⊔ a' = ⊤`) — then `v b` decomposes
exactly: `v b = v (a ⊓ b) + v (a' ⊓ b)`. This is the positive counterpart to
`cond_add_compl_le`: `{a, aᶜ}` is disjoint but not exhaustive, so it fails there. Marginalising
a prediction is valid precisely over families that genuinely join to `⊤`. -/
theorem Valuation.total_prob_of_partition (v : Valuation Ω) {a a' : Ω}
    (hdisj : a ⊓ a' = ⊥) (hcov : a ⊔ a' = ⊤) (b : Ω) :
    v b = v (a ⊓ b) + v (a' ⊓ b) := by
  have hd : (a ⊓ b) ⊓ (a' ⊓ b) = ⊥ := by rw [inf_inf_inf_comm, hdisj, bot_inf_eq]
  rw [← v.additive_of_disjoint hd, ← inf_sup_right, hcov, top_inf_eq]

/-- The same in **predictive form**: `v b = v(b | a)·v a + v(b | a')·v a'` — marginalise the
prediction of `b` over the partition `{a, a'}`, weighting each conditional by its prior. -/
theorem Valuation.total_prob_predictive (v : Valuation Ω) {a a' : Ω}
    (hdisj : a ⊓ a' = ⊥) (hcov : a ⊔ a' = ⊤) (b : Ω) (ha : v a ≠ 0) (ha' : v a' ≠ 0) :
    v b = v.condVal a ha b * v a + v.condVal a' ha' b * v a' := by
  rw [v.condVal_mul a ha b, v.condVal_mul a' ha' b, inf_comm b a, inf_comm b a']
  exact v.total_prob_of_partition hdisj hcov b

/-! ### Toward a constructive Cox theorem: R3 is the hinge

Van Horn's repaired Cox theorem (2003) axiomatises a plausibility calculus over **classical**
propositions. Its negation axiom — call it **R3** — posits that `plaus(¬A)` is a fixed
non-increasing function `S` of `plaus(A)` alone, and consistency forces `S∘S = id` (an
involution), which is exactly the `p ↦ 1 − p` complement rule. `S∘S = id` *is* double-negation
elimination; it is where classical logic enters, and every known Cox proof uses it.

The constructive move is to **drop R3** and keep only what survives without excluded middle:
the conjunction/product structure (conditioning and the product rule — proved above in
`condVal`/`condVal_mul`) and monotonicity of the Heyting pseudocomplement. *Caveat:* the
product structure does **not** by itself give modularity — classically the sum rule /
inclusion–exclusion is derived from R3 via De Morgan (`a ∨ b = ¬(¬a ∧ ¬b)`), a route blocked
constructively, so modularity is built into `Valuation` as a separate axiom rather than
derived. Van Horn already observes that dropping R3 yields a "two-dimensional theory needing
two numbers per proposition" — precisely the belief/plausibility pair `(v(A), 1 − v(¬A))` of
Dempster–Shafer, with the slack `1 − v(A) − v(¬A)` between them.

We isolate the exact content of R3's *conclusion* as a predicate, and pin down that it holds
**iff** the logic is classical. That reduces the whole "which axiom is classical?" question to
a single crisp equivalence. -/

/-- The conclusion of Cox's negation axiom R3, at the level of a valuation: the classical
complement rule `v(¬a) = 1 − v(a)`, i.e. the negation functional is `S(p) = 1 − p`. -/
def Valuation.HasClassicalNegation (v : Valuation Ω) : Prop := ∀ a, v a + v aᶜ = 1

/-- **Easy direction (proved).** If excluded middle holds in `Ω` (`a ⊔ aᶜ = ⊤` for every `a`),
then *every* valuation obeys the classical complement rule. Classical logic ⟹ R3's conclusion,
uniformly. -/
theorem hasClassicalNegation_of_em (hem : ∀ a : Ω, a ⊔ aᶜ = ⊤) (v : Valuation Ω) :
    v.HasClassicalNegation :=
  fun a => v.add_compl_eq_one_of_sup_eq_top (hem a)

section PrimeIdealValuation
open scoped Classical

/-- The **indicator of the complement of a prime ideal** `J` (with `⊤ ∉ J`): `v x = 0` if
`x ∈ J`, else `1`. This is a {0,1}-valued valuation — a "point"-like plausibility. Crucially
its modularity holds *because* `J` is prime: the only case needing primeness is `a,b ∉ J`,
where `a ⊓ b ∉ J` requires exactly `a ⊓ b ∈ J → a ∈ J ∨ b ∈ J`. -/
noncomputable def Ideal.toValuation (J : Order.Ideal Ω) (hJ : J.IsPrime) (htop : ⊤ ∉ J) :
    Valuation Ω where
  toFun x := if x ∈ J then 0 else 1
  map_bot' := by rw [if_pos J.bot_mem]
  map_top' := by rw [if_neg htop]
  mono' a b hab := by
    change (if a ∈ J then (0 : ℝ≥0∞) else 1) ≤ if b ∈ J then 0 else 1
    split_ifs with ha hb hb
    · exact le_rfl
    · exact zero_le
    · exact absurd (J.lower hab hb) ha
    · exact le_rfl
  modular' a b := by
    by_cases ha : a ∈ J <;> by_cases hb : b ∈ J
    · have h1 : a ⊔ b ∈ J := Order.Ideal.sup_mem ha hb
      have h2 : a ⊓ b ∈ J := J.lower inf_le_left ha
      rw [if_pos ha, if_pos hb, if_pos h1, if_pos h2]
    · have h1 : a ⊔ b ∉ J := fun h => hb (J.lower le_sup_right h)
      have h2 : a ⊓ b ∈ J := J.lower inf_le_left ha
      rw [if_pos ha, if_neg hb, if_neg h1, if_pos h2, zero_add, add_zero]
    · have h1 : a ⊔ b ∉ J := fun h => ha (J.lower le_sup_left h)
      have h2 : a ⊓ b ∈ J := J.lower inf_le_right hb
      rw [if_neg ha, if_pos hb, if_neg h1, if_pos h2]
    · have h1 : a ⊔ b ∉ J := fun h => ha (J.lower le_sup_left h)
      have h2 : a ⊓ b ∉ J := fun h => (hJ.mem_or_mem h).elim ha hb
      rw [if_neg ha, if_neg hb, if_neg h1, if_neg h2]

@[simp] theorem Ideal.toValuation_apply (J : Order.Ideal Ω) (hJ : J.IsPrime) (htop : ⊤ ∉ J)
    (x : Ω) : Ideal.toValuation J hJ htop x = if x ∈ J then 0 else 1 := rfl

end PrimeIdealValuation

/-! ### Sharp valuations are the points of the locale

A sharp (`{0,1}`-valued) valuation is exactly the complement-indicator of a prime ideal — the
certainty limit recovers the underlying logic and its points. (Without Scott-continuity these
are the *finitely*-prime points; the completely-prime/spatial ones are the Scott-continuous
sharp valuations.) -/

/-- The prime-ideal-complement indicators are sharp. -/
theorem Ideal.toValuation_isSharp (J : Order.Ideal Ω) (hJ : J.IsPrime) (htop : ⊤ ∉ J) :
    (Ideal.toValuation J hJ htop).IsSharp := by
  intro a
  rw [Ideal.toValuation_apply]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The **zero-set of a valuation is an ideal**: down-closed by monotonicity, closed under `⊔`
because in `ℝ≥0∞` a sum vanishes only if both summands do. (Sharpness not needed here.) -/
def Valuation.zeroIdeal (v : Valuation Ω) : Order.Ideal Ω where
  carrier := {a | v a = 0}
  lower' := by
    intro a b hba ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact le_antisymm ((v.mono hba).trans ha.le) zero_le
  nonempty' := ⟨⊥, by simp only [Set.mem_setOf_eq]; exact v.map_bot⟩
  directed' := by
    intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb
    refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
    simp only [Set.mem_setOf_eq]
    have hm := v.modular a b
    rw [ha, hb, zero_add] at hm
    exact le_antisymm (le_self_add.trans hm.symm.le) zero_le

@[simp] theorem Valuation.mem_zeroIdeal (v : Valuation Ω) {a : Ω} :
    a ∈ v.zeroIdeal ↔ v a = 0 := Iff.rfl

theorem Valuation.zeroIdeal_top_not_mem (v : Valuation Ω) : ⊤ ∉ v.zeroIdeal := by
  rw [Valuation.mem_zeroIdeal, v.map_top]; exact one_ne_zero

/-- **Primeness needs sharpness.** If `v` is sharp, its zero-set is a *prime* ideal: from
`v(x ⊓ y) = 0`, modularity gives `v x + v y = v(x ⊔ y) ≤ 1`, so `v x` and `v y` cannot both
be `1`. -/
theorem Valuation.zeroIdeal_isPrime (v : Valuation Ω) (hv : v.IsSharp) :
    v.zeroIdeal.IsPrime := by
  haveI : v.zeroIdeal.IsProper :=
    Order.Ideal.isProper_iff_top_notMem.mpr v.zeroIdeal_top_not_mem
  rw [Order.Ideal.isPrime_iff_mem_or_mem]
  intro x y hxy
  simp only [Valuation.mem_zeroIdeal] at hxy ⊢
  have hm := v.modular x y
  rw [hxy, add_zero] at hm
  have hle : v x + v y ≤ 1 := hm.symm ▸ v.le_one (x ⊔ y)
  rcases hv x with hx | hx
  · exact Or.inl hx
  · rcases hv y with hy | hy
    · exact Or.inr hy
    · rw [hx, hy] at hle; norm_num at hle

attribute [ext] Valuation

/-- **Round trip**: a sharp valuation is the indicator of its own zero-ideal's complement. -/
theorem Valuation.toValuation_zeroIdeal (v : Valuation Ω) (hv : v.IsSharp) :
    Ideal.toValuation v.zeroIdeal (v.zeroIdeal_isPrime hv) v.zeroIdeal_top_not_mem = v := by
  ext a
  rw [Ideal.toValuation_apply]
  by_cases ha : v a = 0
  · rw [if_pos (v.mem_zeroIdeal.mpr ha)]; exact ha.symm
  · rw [if_neg (fun h => ha (v.mem_zeroIdeal.mp h))]
    rcases hv a with h0 | h1
    · exact absurd h0 ha
    · exact h1.symm

/-- **Sharp valuations = points (prime ideals).** A valuation is `{0,1}`-valued iff it is the
complement-indicator of a prime ideal. The forward map sends `v` to its zero-ideal; the
backward map is `Ideal.toValuation`. -/
theorem sharp_iff_point (v : Valuation Ω) :
    v.IsSharp ↔ ∃ (J : Order.Ideal Ω) (hJ : J.IsPrime) (htop : ⊤ ∉ J),
      v = Ideal.toValuation J hJ htop := by
  constructor
  · intro hv
    exact ⟨v.zeroIdeal, v.zeroIdeal_isPrime hv, v.zeroIdeal_top_not_mem,
      (v.toValuation_zeroIdeal hv).symm⟩
  · rintro ⟨J, hJ, htop, rfl⟩
    exact Ideal.toValuation_isSharp J hJ htop

/-- **The R3 hinge, hard direction (proved).** Conversely, if *every* valuation obeys the
classical complement rule, then excluded middle must hold in `Ω`. Proof: if `a ⊔ aᶜ ≠ ⊤`, the
prime-ideal separation theorem gives a prime ideal `J` containing `a ⊔ aᶜ` but not `⊤`; its
complement-indicator valuation assigns `a ⊔ aᶜ` value `0`, so `v(a) + v(aᶜ) = 0 ≠ 1` — slack.
Together with `hasClassicalNegation_of_em` this gives **classical negation rule ⟺ excluded
middle**: R3 is exactly the axiom that assumes classical logic. -/
theorem em_of_forall_hasClassicalNegation
    (h : ∀ v : Valuation Ω, v.HasClassicalNegation) : ∀ a : Ω, a ⊔ aᶜ = ⊤ := by
  intro a
  by_contra hne
  have hdisj : Disjoint (↑(Order.PFilter.principal (⊤ : Ω)) : Set Ω)
      (↑(Order.Ideal.principal (a ⊔ aᶜ)) : Set Ω) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    rw [SetLike.mem_coe, Order.PFilter.mem_principal] at hx
    rw [SetLike.mem_coe, Order.Ideal.mem_principal] at hx2
    exact hne (top_le_iff.mp (hx.trans hx2))
  obtain ⟨J, hJprime, hIJ, hJF⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hdisj
  have hcJ : (a ⊔ aᶜ) ∈ J := SetLike.le_def.mp hIJ Order.Ideal.mem_principal_self
  have htop : (⊤ : Ω) ∉ J := by
    have hTF : (⊤ : Ω) ∈ (↑(Order.PFilter.principal (⊤ : Ω)) : Set Ω) :=
      SetLike.mem_coe.mpr (Order.PFilter.mem_principal.mpr le_rfl)
    have hnot := Set.disjoint_left.mp hJF hTF
    rwa [SetLike.mem_coe] at hnot
  have hcn := h (Ideal.toValuation J hJprime htop) a
  rw [(Ideal.toValuation J hJprime htop).add_compl_eq_sup,
      Ideal.toValuation_apply, if_pos hcJ] at hcn
  exact zero_ne_one hcn

/-- A **Cox plausibility model** on a frame `Ω`: conditional plausibilities `pl a b`
("plausibility of `a` given `b`") valued in `ℝ`, with Van Horn's structural axioms — R1
(real-valued, monotone in the first argument), the boundary conventions, and R2 (an
associative, continuous, strictly-monotone conjunction functional `F` — whose associativity is
Cox's functional equation, forcing a product rule after regraduation) — **but deliberately
WITHOUT the negation axiom R3.** Dropping R3 is the whole move: nothing ties `pl aᶜ b` to
`pl a b`, so the calculus is free to occupy the two-number (belief/plausibility) slack regime
instead of collapsing to `p ↦ 1 − p`. -/
structure CoxModel (Ω : Type*) [Order.Frame Ω] where
  /-- `pl a b` = plausibility of `a` given `b`. -/
  pl : Ω → Ω → ℝ
  /-- R1: more inclusive hypotheses are at least as plausible. -/
  mono_left : ∀ c, Monotone fun a => pl a c
  /-- Boundary: the impossible has plausibility `0`, … -/
  pl_bot : ∀ c, pl ⊥ c = 0
  /-- … the certain has plausibility `1`. -/
  pl_top : ∀ c, pl ⊤ c = 1
  /-- R2: a conjunction functional. -/
  F : ℝ → ℝ → ℝ
  /-- The plausibility of `a ⊓ b` given `c` depends, via `F`, only on `pl a (b ⊓ c)` (the
  first conjunct, given the second *and* `c`) and `pl b c` (the second conjunct, given `c`). -/
  conj : ∀ a b c, pl (a ⊓ b) c = F (pl a (b ⊓ c)) (pl b c)
  /-- Cox's functional equation: `F` is associative … -/
  F_assoc : ∀ x y z, F (F x y) z = F x (F y z)
  /-- … and strictly monotone in its first slot **on the interior `0 < y`**. The restriction
  matters: unrestricted `∀ y` is *vacuous* — `conj` at `b = ⊥` forces `F x 0 = 0` for every `x`
  (since `⊥ ⊓ c = ⊥`), so `F · 0` is constant and cannot be strictly monotone at `y = 0`, while
  `pl ⊥ ⊥ = 0 ≠ 1 = pl ⊤ ⊥` guarantees two arguments hit it. With `0 < y`, genuine
  (conditional) probability measures satisfy every field, so the structure is inhabited. This
  is exactly the boundary/domain subtlety behind Halpern's critique of Cox. -/
  F_strictMono_left : ∀ y, 0 < y → StrictMono fun x => F x y
  -- Cox additionally needs a *continuity/regularity* axiom on `F` (this is what Halpern's
  -- counterexample shows is indispensable); it is omitted from this first statement because it
  -- is a hypothesis for the *proof*, not part of the conjecture's shape. Add it when proving.
  -- NB: there is deliberately no field relating `pl aᶜ b` to `pl a b`. That missing field is
  -- exactly Van Horn's negation axiom R3.

/-- **Constructive Cox theorem (corrected statement, now proved).**
Every Cox model whose unconditional plausibility is *modular* regraduates to a `Valuation`:
there is a `g : ℝ → ℝ≥0∞`, strictly monotone on `[0,1]` with `g 0 = 0` and `g 1 = 1`, such that
`a ↦ g (M.pl a ⊤)` is (the underlying function of) a `Valuation Ω`.

**Scope of this theorem — read carefully.** This is the *sum-rule* half of the Cox story. Its
proof uses only `pl_bot`, `pl_top`, `mono_left` and the posited `hmod`, with `g = ENNReal.ofReal`;
it does **not** touch the conjunction functional `F` or its axioms (`F_assoc`,
`F_strictMono_left`, `conj`). That is deliberate: the *product-rule* half — that `F` regraduates
to multiplication — is a separate, logic-independent result (Aczél's theorem), carried out on
the positive cone in `Aczel.lean` (`Scale.aczelStatement_cone`, `exists_mul_generator`). The two
halves are proved independently; this theorem assembles the sum rule into a `Valuation`.

On a Boolean `Ω` a modular valuation is automatically complement-additive (`classical_additivity`,
`ModularCoxModel.classical_of_boolean`), recovering Van Horn's classical Cox conclusion; on a
general frame the absence of R3 leaves room for the Dempster–Shafer slack `1 − v a − v aᶜ`.

**Why modularity is a hypothesis, not a conclusion.** The conjunction/product axioms do **not**
force the unconditional plausibility to be modular — classically, inclusion–exclusion is derived
from R3 via De Morgan, and that derivation fails constructively. Indeed `modularity_irreducible`
(`SumIrreducible.lean`) exhibits a monotone, normalized, disjoint-additive plausibility that is
*not* modular, so modularity genuinely cannot be derived from the sum/disjunction data and must
be posited. It is the constructive replacement for the sum-rule half of R3. `Cox.lean` packages
the already-regraduated version as `ModularCoxModel` and proves `constructive_cox_of_modular`.

**Two corrections forced when discharging this.** The original bare statement was
not merely too strong but *unsatisfiable*: it demanded `StrictMono g` for `g : ℝ → ℝ≥0∞` with
`g 0 = 0`, yet strict monotonicity would force `g (-1) < g 0 = 0`, impossible in `ℝ≥0∞`. Two
fixes make it a true theorem. (1) The plausibility values lie in `[0,1]`, so strictness is only
meaningful there: `StrictMono` ⇝ `StrictMonoOn · (Icc 0 1)`. (2) The product rule cannot supply
inclusion–exclusion (the sum-rule half is irreducible — a disjunction is *not* a functional of
its marginals, unlike a conjunction via conditioning), so **modularity of the unconditional
plausibility is posited as an explicit hypothesis** — exactly the constructive replacement for
R3 identified in `Cox.lean`. With these, the regraduation is `g = ENNReal.ofReal` and the
plausibility genuinely *is* a `Valuation`. -/
theorem constructive_cox (M : CoxModel Ω)
    (hmod : ∀ a b : Ω, M.pl a ⊤ + M.pl b ⊤ = M.pl (a ⊔ b) ⊤ + M.pl (a ⊓ b) ⊤) :
    ∃ (v : Valuation Ω) (g : ℝ → ℝ≥0∞),
      StrictMonoOn g (Set.Icc 0 1) ∧ g 0 = 0 ∧ g 1 = 1 ∧ ∀ a, v a = g (M.pl a ⊤) := by
  have hnn : ∀ a : Ω, 0 ≤ M.pl a ⊤ := fun a =>
    (M.pl_bot ⊤).symm.trans_le (M.mono_left ⊤ (bot_le : (⊥ : Ω) ≤ a))
  refine ⟨{ toFun := fun a => ENNReal.ofReal (M.pl a ⊤)
            map_bot' := by simp [M.pl_bot ⊤]
            map_top' := by simp [M.pl_top ⊤]
            mono' := fun a b hab => ENNReal.ofReal_le_ofReal (M.mono_left ⊤ hab)
            modular' := fun a b => by
              rw [← ENNReal.ofReal_add (hnn a) (hnn b),
                ← ENNReal.ofReal_add (hnn (a ⊔ b)) (hnn (a ⊓ b)), hmod a b] },
          ENNReal.ofReal, ?_, ENNReal.ofReal_zero, ENNReal.ofReal_one, fun _ => rfl⟩
  intro x hx y _ hxy
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hx.1 hxy)).mpr hxy

/-- Deciding `a = ⊤` in `ℝ≥0∞` really is a `WithTop` constructor check: this instance is
**computable**. It matters for honesty: without it, the `if a = ⊤` in `coxModelENNReal` would
elaborate through `LinearOrder.toDecidableEq` on the *noncomputable classical* order structure
of `ℝ≥0∞`, and "the case split is a constructor check" would hold only in principle, not of the
code as written. Local instance, so the rest of the development is unaffected. -/
@[reducible] def decEqTopENNReal (a : ℝ≥0∞) : Decidable (a = ⊤) :=
  a.recTopCoe (isTrue rfl) fun _ => isFalse ENNReal.coe_ne_top

attribute [local instance] decEqTopENNReal

/-- **The Cox axioms are not vacuous.** A witness on the *genuinely non-Boolean* chain `ℝ≥0∞`
(the frame of `exists_positive_slack`), with plausibility `pl a _ = (if a = ⊤ then 1 else 0)`
and multiplication as the conjunction functional. The case split `a = ⊤` is a `WithTop`
constructor check — the local `Decidable` instance above (`decEqTopENNReal`) makes the `if`
below elaborate through that check rather than through the classical
`LinearOrder.toDecidableEq` — so, unlike a `Prop`-based model, the *case split* smuggles no
excluded middle into a theory about constructive logic. (The ambient meta-logic is still
classical mathlib, as everywhere; the point is object-level.) `constructive_cox` thus
quantifies over a nonempty class, guarding against the vacuity that the unrestricted
strict-monotonicity axiom caused. -/
noncomputable def coxModelENNReal : CoxModel ℝ≥0∞ where
  pl a _ := if a = ⊤ then 1 else 0
  mono_left c := by
    intro a b hab
    simp only []
    split_ifs with ha hb hb
    · exact le_rfl
    · exact absurd (top_le_iff.mp (ha ▸ hab)) hb
    · exact zero_le_one
    · exact le_rfl
  pl_bot c := by simp
  pl_top c := by simp
  F x y := x * y
  conj a b c := by
    by_cases ha : a = ⊤ <;> by_cases hb : b = ⊤ <;> simp [ha, hb, inf_eq_top_iff]
  F_assoc x y z := mul_assoc x y z
  F_strictMono_left y hy := by
    intro a b hab
    exact mul_lt_mul_of_pos_right hab hy

theorem nonempty_coxModel : Nonempty (CoxModel ℝ≥0∞) := ⟨coxModelENNReal⟩

/-- The witness also satisfies the **modularity hypothesis** of the corrected `constructive_cox`:
on the chain `ℝ≥0∞` the pair `{a ⊔ b, a ⊓ b}` equals `{a, b}`, so any monotone unconditional
plausibility is modular for free. Hence `constructive_cox` (with its `hmod` hypothesis) is not
vacuous — it applies to this genuinely non-Boolean model. -/
theorem coxModelENNReal_modular (a b : ℝ≥0∞) :
    coxModelENNReal.pl a ⊤ + coxModelENNReal.pl b ⊤
      = coxModelENNReal.pl (a ⊔ b) ⊤ + coxModelENNReal.pl (a ⊓ b) ⊤ := by
  rcases le_total a b with h | h
  · rw [sup_eq_right.mpr h, inf_eq_left.mpr h, add_comm]
  · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]

/-- `constructive_cox` applies non-vacuously: there is a Cox model meeting every hypothesis. -/
theorem constructive_cox_nonvacuous :
    ∃ (v : Valuation ℝ≥0∞) (g : ℝ → ℝ≥0∞),
      StrictMonoOn g (Set.Icc 0 1) ∧ g 0 = 0 ∧ g 1 = 1 ∧
        ∀ a, v a = g (coxModelENNReal.pl a ⊤) :=
  constructive_cox coxModelENNReal coxModelENNReal_modular

end CoxProgram

/-! ## Running example: the canonical locale of opens

`TopologicalSpace.Opens X` is a `Order.Frame`, so `Valuation (Opens X)` typechecks. Its
logic is intuitionistic (`U ⊔ Uᶜ ≠ ⊤` whenever `U` is not clopen), making it the natural
first testbed for `exists_positive_slack`. -/
example (X : Type*) [TopologicalSpace X] : Order.Frame (TopologicalSpace.Opens X) :=
  inferInstance

/-! ## The Gödel–McKinsey–Tarski bridge: a valuation is a measure on the opens

Intuitionistic logic embeds into the modal logic S4 by prefixing `□` to every subformula
(Gödel–McKinsey–Tarski), and semantically `□` is the **interior** operator: the intuitionistic
propositions are the *open* sets. So a classical, additive probability measure `μ` on a space
`X`, read only on its open sets, should be an intuitionistic-probability `Valuation` — with
`v U = μ U` playing the role of `P(□U)`, "the μ-measure of the region where `U` verifiably
holds". No notion of *belief* is involved: `v U` is the measure of an open set.

This makes the whole abstract theory concrete, and shows the slack is a structural quantity:
the Heyting negation of an open `U` is `interior (Uᶜ)`, so `v U + v Uᶜ = μ U + μ (interior Uᶜ)`
falls short of `1` by `μ (frontier U)` — the measure of the topological boundary, the region
that neither `U` nor its exterior covers. That boundary is exactly where excluded middle fails;
its μ-measure is the slack. Nothing epistemic, no believer — just `μ` of a frontier. -/

section GMT
open MeasureTheory TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A classical probability measure `μ`, restricted to the frame of open sets, **is** an
intuitionistic-probability `Valuation`: `v U = μ U = P(□U)`. Modularity is measure
inclusion–exclusion (`measure_union_add_inter`); the interior operator `□` is implicit in
working with `Opens X`. -/
noncomputable def _root_.MeasureTheory.Measure.toValuationOpens
    (μ : Measure X) [IsProbabilityMeasure μ] : Valuation (Opens X) where
  toFun U := μ (U : Set X)
  map_bot' := by simp
  map_top' := by simp
  mono' U V h := measure_mono (SetLike.coe_subset_coe.mpr h)
  modular' U V := by
    change μ (U : Set X) + μ (V : Set X)
        = μ ((U ⊔ V : Opens X) : Set X) + μ ((U ⊓ V : Opens X) : Set X)
    rw [Opens.coe_sup, Opens.coe_inf]
    exact (measure_union_add_inter _ V.isOpen.measurableSet).symm

@[simp] theorem _root_.MeasureTheory.Measure.toValuationOpens_apply
    (μ : Measure X) [IsProbabilityMeasure μ] (U : Opens X) :
    μ.toValuationOpens U = μ (U : Set X) := rfl

/-- `μ`'s **interior-measure**, `interiorMeasure S = μ (interior S) = P(□S)`, defined on *every*
subset: the μ-measure of the largest open set inside `S` — the region where `S` *verifiably*
holds. (This is the object the Dempster–Shafer literature names a "belief function" and reads
epistemically; we keep only the structural content — it is `μ` of an open set — and use that
name solely to point at the same object.) -/
noncomputable def _root_.MeasureTheory.Measure.interiorMeasure (μ : Measure X) (S : Set X) :
    ℝ≥0∞ := μ (interior S)

/-- **The Gödel–McKinsey–Tarski identification (concrete direction).** On the open (=
intuitionistic) propositions, `P(□·)` *is* the localic valuation: `v U = μ.interiorMeasure U`.
So the Heyting `Valuation` built from `μ` is exactly the restriction, to the opens, of the
classical `P(□·)` living on all of `Set X`. (The converse — that *every* localic valuation
arises this way from some classical measure — is the open representation direction, not proved
here.) -/
theorem toValuationOpens_eq_interiorMeasure (μ : Measure X) [IsProbabilityMeasure μ]
    (U : Opens X) : μ.toValuationOpens U = μ.interiorMeasure (U : Set X) := by
  rw [μ.toValuationOpens_apply]
  exact congrArg μ U.isOpen.interior_eq.symm

/-- `interiorMeasure` is complement-subadditive, `P(□S) + P(□Sᶜ) ≤ 1`: the interiors of `S` and
`Sᶜ` are disjoint, and the μ-mass they leave out is `μ (frontier S)`, the boundary where
excluded middle fails. A structural gap — the measure of a frontier, not anyone's ignorance. -/
theorem interiorMeasure_add_compl_le (μ : Measure X) [IsProbabilityMeasure μ] (S : Set X) :
    μ.interiorMeasure S + μ.interiorMeasure Sᶜ ≤ 1 := by
  have hdisj : Disjoint (interior S) (interior Sᶜ) :=
    Disjoint.mono interior_subset interior_subset disjoint_compl_right
  change μ (interior S) + μ (interior Sᶜ) ≤ 1
  rw [← measure_union hdisj isOpen_interior.measurableSet]
  exact le_trans (measure_mono (Set.subset_univ _)) measure_univ.le

end GMT

end ConstructiveProb
