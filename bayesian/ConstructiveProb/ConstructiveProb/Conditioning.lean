/-
# The conditioning hinge: Bayes/geometric vs. Dempster, and where they split

`Basic.lean` proves that the localic posterior `v(a | b) = v(a ⊓ b) / v(b)` (`condVal`) satisfies
the product rule and Bayes symmetry. Under the Dempster–Shafer dictionary of `Belief.lean` this is
exactly **geometric conditioning** (Suppes–Zanotti): condition a belief function by renormalizing
the *belief* of the conjunction.

Dempster–Shafer theory has a second, inequivalent update: **Dempster's rule of conditioning**
(Shafer 1976), `Bel(a ‖ b) = (Bel(a ∨ ¬b) − Bel(¬b)) / (1 − Bel(¬b))` — renormalize by the
*plausibility* of `b` after discarding the mass that is incompatible with it. Classically the two
coincide. Constructively they split, and this file proves the split is governed by exactly one
number: the **slack at the conditioning event**.

**The gap quantity.** Define `emGap v a b := v a − v (a ⊓ (b ⊔ bᶜ))` — the mass of `a` stranded
outside `b`'s instance of excluded middle. The two decompositions

  `v (a ⊓ b) + v (a ⊓ bᶜ) + emGap v a b = v a`                    (`inf_add_inf_compl_add_emGap`)
  `v (a ⊔ bᶜ) = v bᶜ + (v (a ⊓ b) + emGap v a b)`                 (`sup_compl_decomp`)

show the Dempster numerator exceeds the geometric numerator by precisely `emGap`. Moreover
`slack v b = 0` forces `emGap v a b = 0` for *every* `a` (`emGap_eq_zero_of_slack_eq_zero`):
if `b ⊔ bᶜ` carries full measure, no mass can be stranded outside it.

**The hinge** (`dempsterCond_eq_condVal_iff_slack`): for `v b ≠ 0`,

  Dempster conditioning on `b` = geometric conditioning on `b` (at every `a`)  ⟺  `slack v b = 0`.

Forward: zero slack kills `emGap` (numerators agree) and makes `1 − v bᶜ = v b` (denominators
agree). Backward: at `a := b` geometric gives `v(b|b) = 1` while Dempster gives
`v b / (1 − v bᶜ)`, which is `1` only if `v b + v bᶜ = 1`. So **the two Dempster–Shafer update
rules are distinguished constructively by a single instance of excluded middle** — the conditional
companion to the R3 hinge: R3 locates classicality in the *statics* (`v aᶜ = 1 − v a` ⟺ EM),
this theorem locates it in the *dynamics* (Dempster = Bayes ⟺ zero slack at the evidence).

Both conditionals are themselves `Valuation`s (`condVal` in `Basic.lean`; `dempsterCond` here —
its modularity is the frame distributivity `(a ⊔ bᶜ) ⊓ (a' ⊔ bᶜ) = (a ⊓ a') ⊔ bᶜ`).
-/
import ConstructiveProb.Basic
import ConstructiveProb.Belief

open scoped ENNReal

namespace ConstructiveProb

variable {Ω : Type*} [Order.Frame Ω]

namespace Valuation

/-! ### The excluded-middle gap of `a` along `b` -/

/-- The **excluded-middle gap of `a` along `b`**: `emGap v a b = v a − v (a ⊓ (b ⊔ bᶜ))`, the mass
of `a` stranded outside `b`'s instance of excluded middle. Zero classically (`b ⊔ bᶜ = ⊤`), and
zero whenever `slack v b = 0`; in general it is the exact surplus of the Dempster conditional
over the Bayes/geometric conditional (see `sup_compl_decomp`). -/
noncomputable def emGap (v : Valuation Ω) (a b : Ω) : ℝ≥0∞ :=
  v a - v (a ⊓ (b ⊔ bᶜ))

/-- The meet with an excluded-middle instance splits disjointly:
`v (a ⊓ (b ⊔ bᶜ)) = v (a ⊓ b) + v (a ⊓ bᶜ)`. -/
theorem inf_sup_compl (v : Valuation Ω) (a b : Ω) :
    v (a ⊓ (b ⊔ bᶜ)) = v (a ⊓ b) + v (a ⊓ bᶜ) := by
  rw [inf_sup_left]
  refine v.additive_of_disjoint ?_
  rw [← inf_inf_distrib_left, inf_compl_eq_bot, inf_bot_eq]

/-- **The three-way decomposition of `v a` along `b`**:
`v (a ⊓ b) + v (a ⊓ bᶜ) + emGap v a b = v a` — the verified part, the refuted part, and the mass
stranded where excluded middle fails for `b`. -/
theorem inf_add_inf_compl_add_emGap (v : Valuation Ω) (a b : Ω) :
    v (a ⊓ b) + v (a ⊓ bᶜ) + v.emGap a b = v a := by
  rw [← v.inf_sup_compl a b, emGap]
  exact add_tsub_cancel_of_le (v.mono inf_le_left)

/-- If the slack at `b` vanishes, nothing can be stranded: `emGap v a b = 0` for **every** `a`.
(`v (b ⊔ bᶜ) = 1` and modularity force `v a ≤ v (a ⊓ (b ⊔ bᶜ))`.) -/
theorem emGap_eq_zero_of_slack_eq_zero (v : Valuation Ω) {b : Ω} (hb : v.slack b = 0)
    (a : Ω) : v.emGap a b = 0 := by
  have hsup : v (b ⊔ bᶜ) = 1 := by
    have h1 : (1 : ℝ≥0∞) ≤ v (b ⊔ bᶜ) := by
      rw [slack_eq_one_sub_sup, tsub_eq_zero_iff_le] at hb
      exact hb
    exact le_antisymm (v.le_one _) h1
  have hmod := v.modular a (b ⊔ bᶜ)
  rw [hsup] at hmod
  -- hmod : v a + 1 = v (a ⊔ (b ⊔ bᶜ)) + v (a ⊓ (b ⊔ bᶜ))
  have hle : (1 : ℝ≥0∞) + v a ≤ 1 + v (a ⊓ (b ⊔ bᶜ)) := by
    rw [add_comm (1 : ℝ≥0∞) (v a), hmod]
    exact add_le_add (v.le_one _) le_rfl
  rw [emGap, tsub_eq_zero_iff_le]
  exact ENNReal.le_of_add_le_add_left ENNReal.one_ne_top hle

/-! ### Dempster's rule of conditioning, as a valuation -/

/-- The plausibility of the conditioning event is positive whenever its belief is:
`v b ≠ 0 → 1 − v bᶜ ≠ 0`. -/
theorem one_sub_compl_ne_zero (v : Valuation Ω) {b : Ω} (hb : v b ≠ 0) :
    1 - v bᶜ ≠ 0 := by
  intro h
  have hle : v b ≤ 1 - v bᶜ :=
    ENNReal.le_sub_of_add_le_right (v.ne_top bᶜ) (v.add_compl_le_one b)
  rw [h] at hle
  exact hb (le_antisymm hle zero_le)

/-- **Dempster's rule of conditioning**, transported through the DS dictionary:
`v(a ‖ b) = (v (a ⊔ bᶜ) − v bᶜ) / (1 − v bᶜ)` — discard the mass incompatible with `b`,
renormalize by the *plausibility* `Pl b = 1 − v bᶜ`. It is again a valuation; modularity is the
frame distributivity `(a ⊔ bᶜ) ⊓ (a' ⊔ bᶜ) = (a ⊓ a') ⊔ bᶜ`. Contrast with `condVal`
(Bayes/geometric conditioning), which renormalizes the *belief* `v b`. -/
noncomputable def dempsterCond (v : Valuation Ω) (b : Ω) (hb : v b ≠ 0) : Valuation Ω where
  toFun a := (v (a ⊔ bᶜ) - v bᶜ) / (1 - v bᶜ)
  map_bot' := by rw [bot_sup_eq, tsub_self, ENNReal.zero_div]
  map_top' := by
    rw [top_sup_eq, v.map_top]
    exact ENNReal.div_self (v.one_sub_compl_ne_zero hb)
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  mono' a a' haa := by
    change (v (a ⊔ bᶜ) - v bᶜ) / (1 - v bᶜ) ≤ (v (a' ⊔ bᶜ) - v bᶜ) / (1 - v bᶜ)
    exact ENNReal.div_le_div_right
      (tsub_le_tsub_right (v.mono (sup_le_sup_right haa _)) _) _
  modular' a a' := by
    have hsplit : ∀ x y : Ω, bᶜ ≤ x → bᶜ ≤ y →
        (v x - v bᶜ) + (v y - v bᶜ) + (v bᶜ + v bᶜ) = v x + v y := by
      intro x y hx hy
      calc (v x - v bᶜ) + (v y - v bᶜ) + (v bᶜ + v bᶜ)
          = (v x - v bᶜ + v bᶜ) + (v y - v bᶜ + v bᶜ) := by ring
        _ = v x + v y := by
            rw [tsub_add_cancel_of_le (v.mono hx), tsub_add_cancel_of_le (v.mono hy)]
    have hnum : (v (a ⊔ bᶜ) - v bᶜ) + (v (a' ⊔ bᶜ) - v bᶜ)
        = (v ((a ⊔ a') ⊔ bᶜ) - v bᶜ) + (v ((a ⊓ a') ⊔ bᶜ) - v bᶜ) := by
      have hadd : ((v (a ⊔ bᶜ) - v bᶜ) + (v (a' ⊔ bᶜ) - v bᶜ)) + (v bᶜ + v bᶜ)
          = ((v ((a ⊔ a') ⊔ bᶜ) - v bᶜ) + (v ((a ⊓ a') ⊔ bᶜ) - v bᶜ)) + (v bᶜ + v bᶜ) := by
        rw [hsplit _ _ le_sup_right le_sup_right, hsplit _ _ le_sup_right le_sup_right]
        have hmod := v.modular (a ⊔ bᶜ) (a' ⊔ bᶜ)
        rwa [sup_sup_sup_comm, sup_idem, ← sup_inf_right] at hmod
      exact (ENNReal.add_left_inj (ENNReal.add_ne_top.mpr ⟨v.ne_top bᶜ, v.ne_top bᶜ⟩)).mp hadd
    change (v (a ⊔ bᶜ) - v bᶜ) / (1 - v bᶜ) + (v (a' ⊔ bᶜ) - v bᶜ) / (1 - v bᶜ)
      = (v ((a ⊔ a') ⊔ bᶜ) - v bᶜ) / (1 - v bᶜ) + (v ((a ⊓ a') ⊔ bᶜ) - v bᶜ) / (1 - v bᶜ)
    rw [← ENNReal.add_div, ← ENNReal.add_div, hnum]

@[simp] theorem dempsterCond_apply (v : Valuation Ω) (b : Ω) (hb : v b ≠ 0) (a : Ω) :
    v.dempsterCond b hb a = (v (a ⊔ bᶜ) - v bᶜ) / (1 - v bᶜ) := rfl

/-- **The Dempster numerator decomposes through the gap**:
`v (a ⊔ bᶜ) = v bᶜ + (v (a ⊓ b) + emGap v a b)`. The surplus of Dempster's numerator over the
Bayes/geometric numerator `v (a ⊓ b)` is exactly the excluded-middle gap. -/
theorem sup_compl_decomp (v : Valuation Ω) (a b : Ω) :
    v (a ⊔ bᶜ) = v bᶜ + (v (a ⊓ b) + v.emGap a b) := by
  have hmod := v.modular a bᶜ
  rw [← v.inf_add_inf_compl_add_emGap a b] at hmod
  -- hmod : (v (a ⊓ b) + v (a ⊓ bᶜ) + emGap) + v bᶜ = v (a ⊔ bᶜ) + v (a ⊓ bᶜ)
  have h : v (a ⊔ bᶜ) + v (a ⊓ bᶜ)
      = (v bᶜ + (v (a ⊓ b) + v.emGap a b)) + v (a ⊓ bᶜ) := by
    rw [← hmod]; ring
  exact (ENNReal.add_left_inj (v.ne_top _)).mp h

/-! ### The hinge -/

/-- Forward half: **zero slack at the evidence makes Dempster conditioning collapse to
Bayes/geometric conditioning.** Numerators: `emGap = 0`. Denominators: `1 − v bᶜ = v b`. -/
theorem dempsterCond_eq_condVal_of_slack_eq_zero (v : Valuation Ω) {b : Ω} (hb : v b ≠ 0)
    (hs : v.slack b = 0) (a : Ω) : v.dempsterCond b hb a = v.condVal b hb a := by
  have hsum : v b + v bᶜ = 1 := by
    rw [Valuation.slack, tsub_eq_zero_iff_le] at hs
    exact le_antisymm (v.add_compl_le_one b) hs
  have hden : 1 - v bᶜ = v b :=
    ENNReal.sub_eq_of_eq_add (v.ne_top _) (by rw [← hsum, add_comm])
  have hnum : v (a ⊔ bᶜ) - v bᶜ = v (a ⊓ b) := by
    rw [v.sup_compl_decomp a b, v.emGap_eq_zero_of_slack_eq_zero hs, add_zero,
      ENNReal.add_sub_cancel_left (v.ne_top _)]
  rw [dempsterCond_apply, condVal_apply, hnum, hden]

/-- Backward half: **if Dempster and Bayes/geometric conditioning agree even at the single test
proposition `a := b`, the slack at `b` vanishes.** Geometric certainty `v(b|b) = 1` forces
Dempster's `v b / (1 − v bᶜ)` to be `1`, i.e. `v b + v bᶜ = 1`. -/
theorem slack_eq_zero_of_dempsterCond_self_eq (v : Valuation Ω) {b : Ω} (hb : v b ≠ 0)
    (h : v.dempsterCond b hb b = v.condVal b hb b) : v.slack b = 0 := by
  have hden0 : 1 - v bᶜ ≠ 0 := v.one_sub_compl_ne_zero hb
  have hdent : 1 - v bᶜ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hgeo : v.condVal b hb b = 1 := by
    rw [condVal_apply, inf_idem]
    exact ENNReal.div_self hb (v.ne_top b)
  have hnum : v (b ⊔ bᶜ) - v bᶜ = v b := by
    rw [← v.add_compl_eq_sup b, ENNReal.add_sub_cancel_right (v.ne_top _)]
  rw [dempsterCond_apply, hnum, hgeo] at h
  -- h : v b / (1 - v bᶜ) = 1
  have hvb : v b = 1 - v bᶜ := by
    have := congrArg (· * (1 - v bᶜ)) h
    simpa [ENNReal.div_mul_cancel hden0 hdent] using this
  rw [Valuation.slack, hvb, tsub_add_cancel_of_le (v.le_one bᶜ), tsub_self]

/-- **The conditioning hinge.** For `v b ≠ 0`:

  Dempster conditioning on `b` agrees with Bayes/geometric conditioning on `b` at every `a`
  **iff** `slack v b = 0`.

The two Dempster–Shafer update rules — inequivalent in general — are separated constructively by
a single instance of excluded middle, the one at the evidence `b`. This is the *dynamic*
companion of the R3 hinge (`em_of_forall_hasClassicalNegation`): R3 locates classicality of the
*statics* in the complement rule; this theorem locates classicality of the *dynamics* in the
agreement of the two conditionings. -/
theorem dempsterCond_eq_condVal_iff_slack (v : Valuation Ω) {b : Ω} (hb : v b ≠ 0) :
    (∀ a, v.dempsterCond b hb a = v.condVal b hb a) ↔ v.slack b = 0 := by
  constructor
  · intro h
    exact v.slack_eq_zero_of_dempsterCond_self_eq hb (h b)
  · intro hs a
    exact v.dempsterCond_eq_condVal_of_slack_eq_zero hb hs a

/-- In the classical (Boolean) limit the hinge closes: Dempster's rule **is** Bayes conditioning,
for every valuation, every evidence, every proposition — the machine-checked form of "the two DS
updates are classically indistinguishable". -/
theorem dempsterCond_eq_condVal_boolean {Ω : Type*} [CompleteBooleanAlgebra Ω]
    (v : Valuation Ω) {b : Ω} (hb : v b ≠ 0) (a : Ω) :
    v.dempsterCond b hb a = v.condVal b hb a :=
  v.dempsterCond_eq_condVal_of_slack_eq_zero hb (classical_slack_zero v b) a

end Valuation

end ConstructiveProb
