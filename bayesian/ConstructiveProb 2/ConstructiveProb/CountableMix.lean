/-
# Countable mixtures: Kleisli composition on countable data, with no space structure

The hard problem flagged in the paper's conclusion is that a probability *monad* for our
valuations needs the space of valuations to be an object of some category, and the known
presentations of that space use Scott continuity essentially.  The modern strategy around the
neighboring Jung–Tix obstructions is to carve out a well-behaved *fragment*: quasi-Borel
spaces on the measure-theoretic side, minimal/central valuation submonads on DCPO
(Jia–Lindenhovius–Mislove–Zamdzhiev, LICS 2021).

This file is the first formal step of that strategy in our discontinuous setting.  A
*countable mixture* of valuations is again a valuation (`Valuation.mixCountable`), and
mixtures of mixtures flatten to mixtures with product weights
(`Valuation.mixCountable_mixCountable`), with the unit index behaving as an identity
(`Valuation.mixCountable_unique`).  These are exactly the monad-multiplication and unit laws
*at the level of presented countable data*: composing countably-supported statistical kernels
needs no topology on the space of valuations, because `ℝ≥0∞`-sums are unconditionally
defined, commute with addition, and satisfy Fubini over sigma types.

What this does and does not show, stated carefully.  It shows that the countably-presented
fragment supports associative, unital kernel composition, machine-checked.  It does not
construct a monad: the presentations (weight functions on index types) are not canonical, and
we do not here quotient by "presents the same valuation."  The diffuse part of the
decomposition (`tsum_mass_le` in `RepresentationGeneral.lean`) is precisely what escapes all
countable presentations, so the obstruction identified in the paper is untouched, and
deliberately so.
-/
import ConstructiveProb.Basic

open scoped ENNReal

namespace ConstructiveProb

variable {Ω : Type*} [Order.Frame Ω]

/-- **A countable mixture of valuations is a valuation.**  For weights `w : ι → ℝ≥0∞` with
`∑' i, w i = 1` and valuations `v i`, the assignment `a ↦ ∑' i, w i * v i a` is a valuation.
Every axiom is inherited termwise, because `ℝ≥0∞`-sums commute with addition and preserve
order.  (The index type is arbitrary, but a weight function summing to `1` has countable
support, so this is the countably-atomic fragment.) -/
noncomputable def Valuation.mixCountable {ι : Type*} (w : ι → ℝ≥0∞)
    (hw : ∑' i, w i = 1) (v : ι → Valuation Ω) : Valuation Ω where
  toFun a := ∑' i, w i * v i a
  map_bot' := by simp
  map_top' := by
    simp only [Valuation.map_top, mul_one]
    exact hw
  mono' a b hab := ENNReal.tsum_le_tsum fun i => by
    gcongr
    exact (v i).mono hab
  modular' a b := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    congr 1
    funext i
    rw [← mul_add, ← mul_add, (v i).modular a b]

@[simp] theorem Valuation.mixCountable_apply {ι : Type*} (w : ι → ℝ≥0∞)
    (hw : ∑' i, w i = 1) (v : ι → Valuation Ω) (a : Ω) :
    Valuation.mixCountable w hw v a = ∑' i, w i * v i a := rfl

/-- The product weights of a mixture of mixtures sum to `1`. -/
theorem tsum_sigma_mul_eq_one {ι : Type*} {κ : ι → Type*}
    (w : ι → ℝ≥0∞) (hw : ∑' i, w i = 1)
    (u : ∀ i, κ i → ℝ≥0∞) (hu : ∀ i, ∑' j, u i j = 1) :
    ∑' p : Σ i, κ i, w p.1 * u p.1 p.2 = 1 := by
  rw [ENNReal.tsum_sigma']
  calc ∑' i, ∑' j, w i * u i j
      = ∑' i, w i * ∑' j, u i j := by
        congr 1; funext i; exact (ENNReal.tsum_mul_left).symm ▸ rfl
    _ = ∑' i, w i := by simp only [hu, mul_one]
    _ = 1 := hw

/-- **Flattening: a countable mixture of countable mixtures is a countable mixture with
product weights.**  This is the monad-multiplication law at the level of presented data
(discrete Chapman–Kolmogorov), and it holds with no space structure on valuations, by
Fubini for `ℝ≥0∞`-sums over sigma types. -/
theorem Valuation.mixCountable_mixCountable {ι : Type*} {κ : ι → Type*}
    (w : ι → ℝ≥0∞) (hw : ∑' i, w i = 1)
    (u : ∀ i, κ i → ℝ≥0∞) (hu : ∀ i, ∑' j, u i j = 1)
    (v : ∀ i, κ i → Valuation Ω) :
    Valuation.mixCountable w hw
        (fun i => Valuation.mixCountable (u i) (hu i) (v i))
      = Valuation.mixCountable (fun p : Σ i, κ i => w p.1 * u p.1 p.2)
          (tsum_sigma_mul_eq_one w hw u hu) (fun p => v p.1 p.2) := by
  ext a
  rw [Valuation.mixCountable_apply, Valuation.mixCountable_apply, ENNReal.tsum_sigma']
  congr 1
  funext i
  rw [Valuation.mixCountable_apply, ← ENNReal.tsum_mul_left]
  congr 1
  funext j
  rw [mul_assoc]

/-- **Fubini holds on the countable fragment:** iterated countable mixing is
order-independent, by the unconditional commutativity of `ℝ≥0∞` double sums.  Contrast
`fubini_fails_for_valuations` in `ProductFreedom.lean`: beyond countable presentations the
two iteration orders can genuinely disagree.  Commutative exactly where countable. -/
theorem Valuation.mixCountable_comm {ι κ : Type*}
    (w : ι → ℝ≥0∞) (hw : ∑' i, w i = 1) (u : κ → ℝ≥0∞) (hu : ∑' j, u j = 1)
    (v : ι → κ → Valuation Ω) :
    Valuation.mixCountable w hw (fun i => Valuation.mixCountable u hu (v i))
      = Valuation.mixCountable u hu
          (fun j => Valuation.mixCountable w hw (fun i => v i j)) := by
  ext a
  simp only [Valuation.mixCountable_apply]
  calc ∑' i, w i * ∑' j, u j * v i j a
      = ∑' i, ∑' j, w i * (u j * v i j a) := by
        congr 1
        funext i
        exact ENNReal.tsum_mul_left.symm
    _ = ∑' j, ∑' i, w i * (u j * v i j a) := ENNReal.tsum_comm
    _ = ∑' j, u j * ∑' i, w i * v i j a := by
        congr 1
        funext j
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext i
        ring

/-- **The unit law at the data level:** a mixture over a single index is that component. -/
theorem Valuation.mixCountable_unique (v : Valuation Ω) :
    Valuation.mixCountable (fun _ : PUnit => 1) (by simp) (fun _ => v) = v := by
  ext a
  rw [Valuation.mixCountable_apply, tsum_eq_single PUnit.unit (by intro b hb; cases b; simp at hb)]
  rw [one_mul]

end ConstructiveProb
