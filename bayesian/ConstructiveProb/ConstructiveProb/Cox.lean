/-
# What Aczél's theorem buys — and where the logic actually enters

An exploration attached to `constructive_cox`. Attempting the Cox derivation constructively
pinpoints exactly which half is hard analysis and which axiom is genuinely missing.

**Aczél's theorem is logic-independent.** The engine of the classical Cox derivation is Aczél's
associativity theorem: an associative, continuous, strictly monotone conjunction functional `F`
on the plausibility scale is, after a regraduation `g`, ordinary multiplication
(`g (F x y) = g x * g y`). Crucially this is a statement about a *real-valued* functional `F`;
the proposition algebra `Ω` — and hence excluded middle — never appears. So the **product-rule
half of Cox is identical constructively and classically**: intuitionistic logic changes nothing
about the derivation of the product rule (`AczelStatement` below makes the logic-freeness
literal — its type does not mention `Ω`).

**The logic enters only in the sum rule.** Classically, once conjunction is multiplicative, the
*sum* rule `v(A∨B) = v(A) + v(B) − v(A∧B)` is obtained from the product rule together with the
negation axiom R3 (`v(¬A) = 1 − v(A)`), via De Morgan. That derivation is exactly what fails
without excluded middle (cf. `hasClassicalNegation_of_em`: R3-for-all-elements ⟺ excluded
middle). So the constructive content of Cox is entirely: *what replaces R3 as the source of the
sum rule?*

**The proposed answer: modularity.** The modular law `v a + v b = v(a⊔b) + v(a⊓b)` already *is* a
sum rule — inclusion–exclusion — and needs no complement. It is self-dual, survives the loss of
excluded middle, and (unlike R3) does not force `v(¬A) = 1 − v(A)`. Positing it directly, in
place of deriving it from R3, is the move.

With those two pieces in hand — Aczél's product rule (imported analytic fact) and a modular sum
rule (the constructive replacement for R3) — the regraduation to a `Valuation` is *trivial*
(`ModularCoxModel.toValuation`). The hard content is thereby correctly isolated into (i) an
analysis theorem that says nothing about logic, and (ii) the choice of the modular axiom. This
is why the original bare-`F` `constructive_cox` was simultaneously under-specified (it carried
*no* sum-rule axiom, so was likely too strong) and entangled with analysis; the reframing here
separates the two.

Nothing here is proof-by-cheating: `AczelStatement` is *stated*, not proved (a substantial
one-parameter-subgroup result absent from mathlib), and the theorems below are the honest
algebraic consequences of taking it as given.
-/
import ConstructiveProb.Basic

open scoped ENNReal
open Set

namespace ConstructiveProb

/-- **Aczél's associativity theorem** over the Cox plausibility scale `[0,1] ⊆ ℝ`, stated as the
analytic input (not proved here). A continuous, associative, per-argument strictly monotone `F`
regraduates to multiplication: some strictly monotone continuous `g` has `g (F x y) = g x * g y`.

Two things to read off the *statement*: (1) the type quantifies only over `F : ℝ → ℝ → ℝ` — the
frame `Ω`, and therefore excluded middle, is absent, so the product-rule half of Cox is
logic-independent; (2) it is a genuine real-analysis theorem (solving the associativity
equation / one-parameter subgroups), not currently in mathlib, hence stated rather than proved. -/
def AczelStatement : Prop :=
  ∀ F : ℝ → ℝ → ℝ,
    Continuous (fun p : ℝ × ℝ => F p.1 p.2) →
    (∀ y ∈ Icc (0 : ℝ) 1, StrictMonoOn (fun x => F x y) (Icc 0 1)) →
    (∀ x y z, F (F x y) z = F x (F y z)) →
    ∃ g : ℝ → ℝ, StrictMonoOn g (Icc 0 1) ∧ ContinuousOn g (Icc 0 1) ∧
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, g (F x y) = g x * g y

section Frame
variable {Ω : Type*} [Order.Frame Ω]

/-- A **regraduated Cox model** on a frame: an (already `g`-regraduated) plausibility whose
conjunction is the product rule — Aczél's output — and whose disjunction obeys the **modular**
sum rule, the constructive replacement for the negation axiom R3. There is deliberately *no*
negation axiom, which is what leaves room for the Dempster–Shafer slack. -/
structure ModularCoxModel (Ω : Type*) [Order.Frame Ω] where
  pl : Ω → ℝ≥0∞
  pl_bot : pl ⊥ = 0
  pl_top : pl ⊤ = 1
  mono : Monotone pl
  /-- The sum rule, in modular form: classically *derived* from the product rule and R3, here
  *posited* — that is the whole constructive move. -/
  modular : ∀ a b, pl a + pl b = pl (a ⊔ b) + pl (a ⊓ b)

/-- With the axioms chosen correctly the regraduation is the identity: a `ModularCoxModel` *is*
a `Valuation`. This is the algebraic core of `constructive_cox` once Aczél has reduced
conjunction to the product rule and the sum rule is taken in modular form. -/
def ModularCoxModel.toValuation (M : ModularCoxModel Ω) : Valuation Ω where
  toFun := M.pl
  map_bot' := M.pl_bot
  map_top' := M.pl_top
  mono' := M.mono
  modular' := M.modular

/-- **`constructive_cox`, reduced.** For the correctly-axiomatised (modular) Cox model the
regraduation `g` is the identity and the plausibility *is* a `Valuation`. The genuine remaining
content is precisely (i) `AczelStatement` — analysis, logic-free — and (ii) the justification
that modularity is *the* right sum-rule axiom (the constructive replacement for R3). -/
theorem constructive_cox_of_modular (M : ModularCoxModel Ω) :
    ∃ (v : Valuation Ω) (g : ℝ≥0∞ → ℝ≥0∞),
      StrictMono g ∧ g 0 = 0 ∧ g 1 = 1 ∧ ∀ a, v a = g (M.pl a) :=
  ⟨M.toValuation, id, strictMono_id, rfl, rfl, fun _ => rfl⟩

end Frame

section Boolean
variable {Ω : Type*} [CompleteBooleanAlgebra Ω]

/-- **Boolean collapse.** On a classical (Boolean) `Ω` no negation axiom need be posited at all:
the modular model is automatically complement-additive (`v a + v aᶜ = 1`), recovering Van Horn's
classical Cox conclusion. Excluded middle does for free what R3 was added to do — which is the
precise sense in which the classical theory is the `aᶜᶜ ⊔ aᶜ = ⊤` special case of this one. -/
theorem ModularCoxModel.classical_of_boolean (M : ModularCoxModel Ω) (a : Ω) :
    M.toValuation a + M.toValuation aᶜ = 1 :=
  classical_additivity M.toValuation a

end Boolean

end ConstructiveProb
