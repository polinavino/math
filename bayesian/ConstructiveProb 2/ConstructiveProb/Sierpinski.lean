/-
# The Sierpiński model, concretely: slack = boundary mass, and the computability guard grounded

`Halting.lean` builds the halting valuation abstractly, on the value-chain `ℝ≥0∞`, and writes
"morally, machine `n` halts" for its middle element. This file replaces both "abstractly" and
"morally":

1. **The frame is the real one.** `Opens Prop` — the opens of the Sierpiński space, mathlib's
   actual topology of semidecidability, in which a proposition is open iff it is *verifiable*
   (`isOpen_iff_continuous_mem`). Its three opens `⊥ < haltsOpen < ⊤` are the observation frame of
   a single semi-decidable experiment: *nothing*, *it halted*, *everything*. The Σ₁ asymmetry is a
   theorem here, not a stipulation: `haltsOpenᶜ = ⊥` (`haltsOpen_compl`) — you cannot even
   partially refute a semidecidable proposition, because every nonempty open of Sierpiński space
   contains `True` (`true_mem_of_isOpen`).

2. **The valuation is a measure read through the GMT bridge**, not a hand-built chain map:
   `sierpinskiValuation p = (coinMeasure p).toValuationOpens`, where `coinMeasure p` is the
   two-point measure `p·δ_True + (1−p)·δ_False`. The slack computation is then the GMT slogan
   *verbatim*: `slack haltsOpen = 1 − p = coinMeasure p (frontier {q | q})`
   (`slack_eq_boundary`) — the measure of the boundary `{False}`, the point where the experiment
   stays silent forever. This is the concrete instance of `interiorMeasure_add_compl_le`'s
   "slack = μ(∂A)" reading, computed end-to-end on an honest space.

3. **The "morally" becomes `Nat.Partrec.Code`.** The sharp, slack-free classical readout — assign
   code `c` belief `1` or `0` in `haltsOpen` according to whether `c` halts on input `n` — is a
   perfectly well-defined *family* of valuations (`sharpReadout`). The theorem
   `sharpReadout_not_computable` says no computable predicate can implement it: deciding
   `sharpReadout n c haltsOpen = 1` *is* the halting problem (`ComputablePred.halting_problem`).
   The slack-carrying valuation is therefore not a defect the constructive theory should
   apologize for; it is the *price of a computable epistemic state*. Any axiom forcing classical
   collapse (`slack ≡ 0`) demands of its models an uncomputable readout.
-/
import ConstructiveProb.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Computability.Halting

open scoped ENNReal Topology
open TopologicalSpace MeasureTheory

namespace ConstructiveProb

/-! ### The frame of one semidecidable observation -/

theorem setOf_self_eq_singleton_true : {q : Prop | q} = ({True} : Set Prop) := by
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun hq => eq_true hq, fun hq => of_eq_true hq⟩

theorem isOpen_setOf_self : IsOpen {q : Prop | q} :=
  setOf_self_eq_singleton_true ▸ isOpen_singleton_true

theorem false_notMem_setOf_self : False ∉ {q : Prop | q} := fun h => h

theorem true_notMem_singleton_false : True ∉ ({False} : Set Prop) := fun h => h ▸ trivial

/-- **The halting open**: the truth-set `{q | q}` as an open of the Sierpiński space — the
verifiable outcome of one semi-decidable experiment. -/
def haltsOpen : Opens Prop := ⟨{q | q}, isOpen_setOf_self⟩

@[simp] theorem mem_haltsOpen {q : Prop} : q ∈ haltsOpen ↔ q := Iff.rfl

/-- Every nonempty open of Sierpiński space contains `True` — the opens are `∅`, `{True}`,
`univ`. (An open neighbourhood of `False` is already everything: `𝓝 False = ⊤`.) -/
theorem true_mem_of_isOpen {s : Set Prop} (hs : IsOpen s) (hne : s.Nonempty) : True ∈ s := by
  obtain ⟨x, hx⟩ := hne
  by_cases hxp : x
  · rwa [eq_true hxp] at hx
  · have hmem : s ∈ 𝓝 False := hs.mem_nhds (by rwa [eq_false hxp] at hx)
    rw [nhds_false, Filter.mem_top] at hmem
    rw [hmem]
    trivial

/-- **The Σ₁ asymmetry as a theorem**: the Heyting complement of the halting open is `⊥` — a
semidecidable proposition admits no partial refutation. Proof: the complement is an open disjoint
from `haltsOpen`; were it nonempty it would contain `True`, which lies in `haltsOpen`. -/
theorem haltsOpen_compl : haltsOpenᶜ = (⊥ : Opens Prop) := by
  by_contra hne
  have hne' : ((haltsOpenᶜ : Opens Prop) : Set Prop).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hne (SetLike.coe_injective (h.trans Opens.coe_bot.symm))
  have htrue : True ∈ ((haltsOpenᶜ : Opens Prop) : Set Prop) :=
    true_mem_of_isOpen (haltsOpenᶜ : Opens Prop).isOpen hne'
  have hbot : True ∈ ((haltsOpenᶜ ⊓ haltsOpen : Opens Prop) : Set Prop) := by
    rw [Opens.coe_inf]
    exact ⟨htrue, trivial⟩
  rw [inf_comm, inf_compl_eq_bot, Opens.coe_bot] at hbot
  exact hbot

/-! ### The two-point measure and its valuation -/

/-- The **coin measure**: `p·δ_True + (1−p)·δ_False` on the Sierpiński space. -/
noncomputable def coinMeasure (p : ℝ≥0∞) : Measure Prop :=
  p • Measure.dirac True + (1 - p) • Measure.dirac False

theorem coinMeasure_apply (p : ℝ≥0∞) (s : Set Prop) :
    coinMeasure p s = p * Measure.dirac True s + (1 - p) * Measure.dirac False s := by
  rw [coinMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul]

theorem coinMeasure_isProbability {p : ℝ≥0∞} (hp1 : p ≤ 1) :
    IsProbabilityMeasure (coinMeasure p) :=
  ⟨by rw [coinMeasure_apply, Measure.dirac_apply_of_mem (Set.mem_univ True),
      Measure.dirac_apply_of_mem (Set.mem_univ False), mul_one, mul_one,
      add_tsub_cancel_of_le hp1]⟩

/-- Every set of `Prop` is measurable (`MeasurableSpace Prop = ⊤`), so the Borel σ-algebra is
trivially contained. -/
instance : OpensMeasurableSpace Prop := ⟨le_top⟩

/-- **The Sierpiński valuation**: the coin measure read through the GMT bridge
(`Measure.toValuationOpens`) as an intuitionistic probability on the three-element frame
`Opens Prop`. -/
noncomputable def sierpinskiValuation {p : ℝ≥0∞} (hp1 : p ≤ 1) : Valuation (Opens Prop) :=
  letI := coinMeasure_isProbability hp1
  (coinMeasure p).toValuationOpens

@[simp] theorem sierpinskiValuation_apply {p : ℝ≥0∞} (hp1 : p ≤ 1) (U : Opens Prop) :
    sierpinskiValuation hp1 U = coinMeasure p (U : Set Prop) := rfl

theorem coinMeasure_setOf_self (p : ℝ≥0∞) : coinMeasure p {q : Prop | q} = p := by
  rw [coinMeasure_apply,
    Measure.dirac_apply_of_mem (show True ∈ {q : Prop | q} from trivial),
    Measure.dirac_apply' _ MeasurableSpace.measurableSet_top,
    Set.indicator_of_notMem false_notMem_setOf_self, mul_one, mul_zero, add_zero]

/-- The halting open carries exactly the halting weight: `v haltsOpen = p`. -/
theorem sierpinskiValuation_haltsOpen {p : ℝ≥0∞} (hp1 : p ≤ 1) :
    sierpinskiValuation hp1 haltsOpen = p :=
  coinMeasure_setOf_self p

/-! ### Slack = boundary mass: the GMT slogan computed end-to-end -/

/-- The slack at the halting open is `1 − p` — the measure of the undecided region. Matches
`Halting.lean`'s abstract `haltingValuation_slack` on the honest frame. -/
theorem sierpinskiValuation_slack {p : ℝ≥0∞} (hp1 : p ≤ 1) :
    (sierpinskiValuation hp1).slack haltsOpen = 1 - p := by
  rw [Valuation.slack, haltsOpen_compl, Valuation.map_bot, add_zero,
    sierpinskiValuation_haltsOpen]

/-- The truth-set is dense: its closure is everything (every nonempty open contains `True`). -/
theorem closure_setOf_self : closure {q : Prop | q} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  rw [mem_closure_iff]
  intro o ho hq
  exact ⟨True, true_mem_of_isOpen ho ⟨q, hq⟩, trivial⟩

/-- **The frontier of the halting event is the silent point**: `∂{q | q} = {False}`. -/
theorem frontier_setOf_self : frontier {q : Prop | q} = ({False} : Set Prop) := by
  rw [frontier, closure_setOf_self, isOpen_setOf_self.interior_eq,
    ← Set.compl_eq_univ_sdiff]
  ext q
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_singleton_iff, eq_iff_iff]
  by_cases hq : q <;> simp [hq]

theorem coinMeasure_frontier (p : ℝ≥0∞) :
    coinMeasure p (frontier {q : Prop | q}) = 1 - p := by
  rw [frontier_setOf_self, coinMeasure_apply,
    Measure.dirac_apply' _ MeasurableSpace.measurableSet_top,
    Set.indicator_of_notMem true_notMem_singleton_false,
    Measure.dirac_apply_of_mem (Set.mem_singleton False), mul_zero, mul_one, zero_add]

/-- **Slack is boundary mass, verbatim**: `slack haltsOpen = μ(∂{q | q})`. The Dempster–Shafer
"ignorance" at the semidecidable event is the measure of the point where the computation stays
silent forever — the concrete, end-to-end instance of the GMT reading `slack = μ(∂A)`. -/
theorem slack_eq_boundary {p : ℝ≥0∞} (hp1 : p ≤ 1) :
    (sierpinskiValuation hp1).slack haltsOpen = coinMeasure p (frontier {q : Prop | q}) := by
  rw [sierpinskiValuation_slack hp1, coinMeasure_frontier]

/-! ### The computability guard, grounded in `Nat.Partrec.Code` -/

open Nat.Partrec (Code)

open scoped Classical in
/-- The **halting weight** of code `c` on input `n`: the sharp `{0,1}`-valued classical answer to
"does `c` halt on `n`?". Well-defined (classically, in the meta-logic), but — see below — not
computably realizable. -/
noncomputable def haltingWeight (n : ℕ) (c : Code) : ℝ≥0∞ :=
  if (c.eval n).Dom then 1 else 0

theorem haltingWeight_le_one (n : ℕ) (c : Code) : haltingWeight n c ≤ 1 := by
  unfold haltingWeight
  split <;> simp

/-- The **sharp classical readout**: the family of slack-free Sierpiński valuations answering the
halting question with certainty, one per code. -/
noncomputable def sharpReadout (n : ℕ) (c : Code) : Valuation (Opens Prop) :=
  sierpinskiValuation (haltingWeight_le_one n c)

/-- **The computability guard, no longer "morally"**: deciding whether the sharp classical
readout assigns belief `1` to the halting event is exactly the halting problem, hence not
computable. A slack-free (classical) valuation family over the codes cannot be computably
realized; the slack of the constructive theory is the price of a computable epistemic state. -/
theorem sharpReadout_not_computable (n : ℕ) :
    ¬ComputablePred fun c : Code => sharpReadout n c haltsOpen = 1 := by
  intro h
  apply ComputablePred.halting_problem n
  apply h.of_eq
  intro c
  rw [sharpReadout, sierpinskiValuation_haltsOpen]
  unfold haltingWeight
  split <;> rename_i hdom <;> simp [hdom]

end ConstructiveProb
