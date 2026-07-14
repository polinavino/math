/-
# The halting valuation — a computability guard against classical collapse

This file builds the **intended non-classical model** of the theory: a valuation on the
value-chain `ℝ≥0∞` on which a distinguished *semi-decidable* proposition (morally "machine `n`
halts") receives a probability strictly between `0` and `1`, with positive slack.

The picture. A semi-decidable (`Σ₁`) proposition is an *open* in the Sierpiński/observational
topology: it can be confirmed by a finite computation but never refuted by one. Its
pseudo-complement is the interior of its set-complement, which for a genuinely undecidable
statement is `⊥` — you cannot even partially refute it. So on the three-element Sierpiński frame
`⊥ < h < ⊤` (the opens of Sierpiński space), the "halts" element `h` has `hᶜ = ⊥`. Assigning it
the halting probability `p ∈ (0,1)` — morally Chaitin's `Ω = Σ_{p halts} 2^{-|p|}`, a specific
uncomputable, Martin-Löf-random real — gives `v h + v hᶜ = p + 0 = p < 1`: genuine slack
`1 - p`, the measure of the undecidable region.

Why this matters for the axioms. The whole design constraint on a constructive Cox theorem is
that the axioms *guarantee* the representation result without *collapsing* to classical logic
(which would force `v a + v aᶜ = 1`, i.e. slack `≡ 0`). This model is a witness that the theory
stays constructive: any axiom set strong enough to force classical collapse is **refuted** by
the halting valuation, because computability theory forbids `p ∈ {0,1}`. It plays the role for
the sum rule that `nonempty_coxModel` plays for the product rule — a vacuity/collapse guard.

We realize the Sierpiński frame concretely as the sub-chain `{⊥, h, ⊤} ⊆ ℝ≥0∞` (taking
`h = 1`); on a complete chain modularity is automatic, so the construction is light.
-/
import ConstructiveProb.Basic

open scoped ENNReal

namespace ConstructiveProb

variable {α : Type*}

/-- **Every normalized monotone function on a complete chain is a valuation.** Modularity is
automatic: in a linear order `{a ⊔ b, a ⊓ b} = {a, b}` as a multiset, so
`v a + v b = v (a ⊔ b) + v (a ⊓ b)` for *any* map. Generalizes `chainVal`. -/
noncomputable def chainValuation [CompleteLinearOrder α]
    (f : α → ℝ≥0∞) (h0 : f ⊥ = 0) (h1 : f ⊤ = 1) (hf : Monotone f) : Valuation α where
  toFun := f
  map_bot' := h0
  map_top' := h1
  mono' := hf
  modular' a b := by
    rcases le_total a b with h | h
    · rw [sup_eq_right.mpr h, inf_eq_left.mpr h, add_comm]
    · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]

@[simp] theorem chainValuation_apply [CompleteLinearOrder α]
    (f : α → ℝ≥0∞) (h0 : f ⊥ = 0) (h1 : f ⊤ = 1) (hf : Monotone f) (x : α) :
    chainValuation f h0 h1 hf x = f x := rfl

/-! ### The Sierpiński readout function

`haltf p` is `1` at `⊤`, `0` at `⊥`, and the halting probability `p` on every strict interior
point — the three values of the Sierpiński readout. -/

/-- The Sierpiński readout: `⊤ ↦ 1`, `⊥ ↦ 0`, interior `↦ p`. -/
noncomputable def haltf (p : ℝ≥0∞) : ℝ≥0∞ → ℝ≥0∞ :=
  fun x => if x = ⊤ then 1 else if x = ⊥ then 0 else p

@[simp] theorem haltf_top (p : ℝ≥0∞) : haltf p ⊤ = 1 := by simp [haltf]

@[simp] theorem haltf_bot (p : ℝ≥0∞) : haltf p ⊥ = 0 := by
  have h : (⊥ : ℝ≥0∞) ≠ ⊤ := bot_ne_top
  simp [haltf, h]

theorem haltf_mid (p : ℝ≥0∞) {x : ℝ≥0∞} (h0 : x ≠ ⊥) (ht : x ≠ ⊤) : haltf p x = p := by
  simp only [haltf]
  rw [if_neg ht, if_neg h0]

theorem haltf_le_one {p : ℝ≥0∞} (hp1 : p ≤ 1) (x : ℝ≥0∞) : haltf p x ≤ 1 := by
  rcases eq_or_ne x ⊤ with h | h
  · rw [h]; exact (haltf_top p).le
  rcases eq_or_ne x ⊥ with h0 | h0
  · rw [h0, haltf_bot]; exact zero_le_one
  · rw [haltf_mid p h0 h]; exact hp1

theorem haltf_mono {p : ℝ≥0∞} (hp1 : p ≤ 1) : Monotone (haltf p) := by
  intro x y hxy
  rcases eq_or_ne y ⊤ with hy | hy
  · subst hy; rw [haltf_top]; exact haltf_le_one hp1 x
  rcases eq_or_ne x ⊥ with hx | hx
  · subst hx; rw [haltf_bot]; exact zero_le
  have hy0 : y ≠ ⊥ := fun hb => hx (le_bot_iff.mp (hb ▸ hxy))
  have hxt : x ≠ ⊤ := fun ht => hy (top_le_iff.mp (ht ▸ hxy))
  exact le_of_eq ((haltf_mid p hx hxt).trans (haltf_mid p hy0 hy).symm)

/-! ### The halting valuation and its slack -/

/-- **The halting valuation.** On the value-chain `ℝ≥0∞`, the Sierpiński readout `haltf p` is a
valuation; the semi-decidable element `h = 1` gets probability `p`. -/
noncomputable def haltingValuation {p : ℝ≥0∞} (hp1 : p ≤ 1) : Valuation ℝ≥0∞ :=
  chainValuation (haltf p) (haltf_bot p) (haltf_top p) (haltf_mono hp1)

@[simp] theorem haltingValuation_apply {p : ℝ≥0∞} (hp1 : p ≤ 1) (x : ℝ≥0∞) :
    haltingValuation hp1 x = haltf p x := rfl

/-- The "halts" element cannot be refuted: its pseudo-complement is `⊥`. This is the Sierpiński
`Σ₁` asymmetry made lattice-theoretic. -/
theorem compl_one_eq_bot : (1 : ℝ≥0∞)ᶜ = ⊥ := by
  have hinf := inf_compl_eq_bot (a := (1 : ℝ≥0∞))
  rwa [inf_eq_right.mpr (compl_le_self_of_ne_bot (one_ne_zero))] at hinf

/-- **The slack at the halting proposition is `1 - p`** — the measure of the undecidable region.
Positive exactly when `p < 1`, i.e. exactly when the proposition is genuinely undecided. -/
theorem haltingValuation_slack {p : ℝ≥0∞} (hp1 : p ≤ 1) :
    (haltingValuation hp1).slack 1 = 1 - p := by
  rw [(haltingValuation hp1).slack_eq_one_sub_sup,
    sup_eq_left.mpr (compl_le_self_of_ne_bot (one_ne_zero)),
    haltingValuation_apply, haltf_mid p one_ne_zero ENNReal.one_ne_top]

/-- **Non-collapse guard.** There is a valuation and a proposition `h` (the semi-decidable
"halts") with probability strictly in `(0,1)` and positive slack — the signature of genuinely
constructive, non-classical probability. Any axiom set forcing classical collapse (`slack ≡ 0`,
equivalently `v h + v hᶜ = 1`) is refuted by this model, since computability forbids `p ∈ {0,1}`.
-/
theorem exists_halting_slack :
    ∃ (v : Valuation ℝ≥0∞) (h : ℝ≥0∞), 0 < v h ∧ v h < 1 ∧ 0 < v.slack h := by
  have hp1 : (2⁻¹ : ℝ≥0∞) ≤ 1 := ENNReal.inv_le_one.mpr one_le_two
  have hval : haltingValuation hp1 1 = 2⁻¹ := by
    rw [haltingValuation_apply, haltf_mid _ one_ne_zero ENNReal.one_ne_top]
  have hlt1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.mpr ENNReal.one_lt_two
  refine ⟨haltingValuation hp1, 1, ?_, ?_, ?_⟩
  · rw [hval]; exact ENNReal.inv_pos.mpr (by simp)
  · rw [hval]; exact hlt1
  · rw [haltingValuation_slack, pos_iff_ne_zero]
    intro hz
    exact absurd (tsub_eq_zero_iff_le.mp hz) (not_le.mpr hlt1)

/-- **The halting valuation is not classical:** it violates `v a + v aᶜ = 1`. Whenever `p < 1`,
`HasClassicalNegation` fails, so no theorem forcing classical negation can hold of every
valuation — excluded middle is genuinely absent. -/
theorem haltingValuation_not_classical {p : ℝ≥0∞} (hp1 : p ≤ 1) (hp : p < 1) :
    ¬ (haltingValuation hp1).HasClassicalNegation := by
  intro hcn
  have h := hcn 1
  rw [haltingValuation_apply, haltingValuation_apply, compl_one_eq_bot,
    haltf_mid p one_ne_zero ENNReal.one_ne_top, haltf_bot, add_zero] at h
  exact absurd h (ne_of_lt hp)

end ConstructiveProb
