/-
# The two parts of slack and the intermediate logics

Slack splits as `dnGap + deMorganGap` (`slack_eq_dnGap_add_deMorganGap`). Each part detects one
step of the chain of logics `IPC ⊂ KC ⊂ CPC`, where KC adds weak excluded middle
`¬a ∨ ¬¬a`:

* `deMorganGap_zero_iff`: the De Morgan part vanishes for every valuation iff the frame
  satisfies weak excluded middle;
* `dnGap_zero_iff`: the double-negation part vanishes for every valuation iff every element
  is regular, that is, iff the frame is Boolean.

The converse directions use the prime ideal theorem through `exists_sharp_separating`, so they
hold in a classical metatheory, as does the R3 characterization.
-/
import ConstructiveProb.Points

open scoped ENNReal

namespace ConstructiveProb

variable {Ω : Type*} [Order.Frame Ω]

/-- **The De Morgan part of slack detects weak excluded middle.** -/
theorem deMorganGap_zero_iff :
    (∀ (v : Valuation Ω) (a : Ω), v.deMorganGap a = 0) ↔ ∀ a : Ω, aᶜᶜ ⊔ aᶜ = ⊤ := by
  constructor
  · intro h a
    by_contra hne
    obtain ⟨v, -, hv1, hv0⟩ := exists_sharp_separating (a := (⊤ : Ω)) (b := aᶜᶜ ⊔ aᶜ)
      (fun hle => hne (top_le_iff.1 hle))
    have := h v a
    rw [Valuation.deMorganGap, v.add_compl_compl_eq_sup, hv0, tsub_zero] at this
    exact one_ne_zero this
  · intro h v a
    exact v.deMorganGap_eq_zero_of_sup_eq_top (h a)

/-- **The double-negation part of slack detects classical logic.** -/
theorem dnGap_zero_iff :
    (∀ (v : Valuation Ω) (a : Ω), v.dnGap a = 0) ↔ ∀ a : Ω, aᶜᶜ = a := by
  constructor
  · intro h a
    by_contra hne
    have hnle : ¬ aᶜᶜ ≤ a := fun hle => hne (le_antisymm hle le_compl_compl)
    obtain ⟨v, -, hv1, hv0⟩ := exists_sharp_separating hnle
    have := h v a
    rw [Valuation.dnGap, hv1, hv0, tsub_zero] at this
    exact one_ne_zero this
  · intro h v a
    exact v.dnGap_eq_zero_of_regular (h a)

/-- **A calculus that contains the certain states imposes the complement rule only where excluded
middle holds.** If every sharp valuation satisfies `v a + v aᶜ = 1`, then `a ⊔ aᶜ = ⊤`. -/
theorem em_of_sharp_compl (a : Ω) (h : ∀ v : Valuation Ω, v.IsSharp → v a + v aᶜ = 1) :
    a ⊔ aᶜ = ⊤ := by
  by_contra hne
  obtain ⟨v, hv, -, hv0⟩ := exists_sharp_separating (a := (⊤ : Ω)) (b := a ⊔ aᶜ)
    (fun hle => hne (top_le_iff.1 hle))
  have := h v hv
  rw [v.add_compl_eq_sup, hv0] at this
  exact zero_ne_one this

/-- If every sharp valuation has classical negation, the frame is Boolean. -/
theorem em_of_sharp_classicalNegation
    (h : ∀ v : Valuation Ω, v.IsSharp → v.HasClassicalNegation) : ∀ a : Ω, a ⊔ aᶜ = ⊤ :=
  fun a => em_of_sharp_compl a fun v hv => h v hv a

end ConstructiveProb
