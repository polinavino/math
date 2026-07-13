/-
# A finite representation theorem for intuitionistic-probability valuations

Companion to `Basic.lean`. We prove the **converse** of the GMT bridge in the finite case:
every modular Heyting valuation on a finite frame is a *classical* probability on its points.

Every finite frame is `LowerSet P` for a finite poset `P` (Birkhoff duality — its
join-irreducibles; we cite this rather than formalize it). For a `Valuation (LowerSet P)` we
build a **mass function** `v.mass : P → ℝ≥0∞` by a discrete derivative and show
`v U = ∑_{p ∈ U} v.mass p` with `∑ p, v.mass p = 1`. So `v` is a genuine probability mass
function on the points, and — since lower sets are exactly the opens of the Alexandrov topology,
on which the interior operator is the identity — `v = μ ∘ □`, the finite instance of the
representation theorem.
-/
import ConstructiveProb.Basic
import Mathlib.Order.UpperLower.Principal
import Mathlib.Order.UpperLower.Closure
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

open scoped ENNReal BigOperators

namespace ConstructiveProb

variable {P : Type*} [PartialOrder P]

-- The finite frame is `LowerSet P`, and it is a `Order.Frame`.
example : Order.Frame (LowerSet P) := inferInstance

/-- The **mass** `v` puts on a point `p`: the discrete derivative `v(↓p) − v({q < p})`. It is
`≥ 0` because `Iio p ≤ Iic p` and `v` is monotone. -/
noncomputable def Valuation.mass (v : Valuation (LowerSet P)) (p : P) : ℝ≥0∞ :=
  v (LowerSet.Iic p) - v (LowerSet.Iio p)

/-- The inf half of the decomposition: erasing a point `p ∈ U` and meeting with `↓p` leaves the
strict lower set `Iio p`. (Only `p ∈ U` is needed, so that `q < p ⟹ q ∈ U`.) -/
theorem _root_.LowerSet.erase_inf_Iic {U : LowerSet P} {p : P} (hp : p ∈ U) :
    U.erase p ⊓ LowerSet.Iic p = LowerSet.Iio p := by
  apply SetLike.coe_injective
  ext q
  simp only [LowerSet.coe_inf, LowerSet.coe_erase, LowerSet.coe_Iic, LowerSet.coe_Iio,
    UpperSet.coe_Ici, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_Ici, Set.mem_Iic, Set.mem_Iio,
    SetLike.mem_coe]
  constructor
  · rintro ⟨⟨_, hpq⟩, hqp⟩
    exact lt_of_le_of_ne hqp (by rintro rfl; exact hpq le_rfl)
  · intro hqp
    exact ⟨⟨U.lower hqp.le hp, fun hpq => hqp.ne' (le_antisymm hpq hqp.le)⟩, hqp.le⟩

/-- **The maximal-element step.** For a maximal `p ∈ U`, `v` increments by exactly `mass p`
when `p` is added: `v U = v (U.erase p) + v.mass p`. Modularity plus the two decompositions
`U.erase p ⊔ Iic p = U` and `U.erase p ⊓ Iic p = Iio p`. -/
theorem Valuation.mass_step (v : Valuation (LowerSet P)) {U : LowerSet P} {p : P}
    (hp : p ∈ U) (hmax : ∀ b ∈ U, p ≤ b → b = p) :
    v U = v (U.erase p) + v.mass p := by
  have hsup : U.erase p ⊔ LowerSet.Iic p = U := LowerSet.erase_sup_Iic hp hmax
  have hinf : U.erase p ⊓ LowerSet.Iic p = LowerSet.Iio p := LowerSet.erase_inf_Iic hp
  have hle : LowerSet.Iio p ≤ LowerSet.Iic p := fun q hq => hq.le
  have hmod := v.modular (U.erase p) (LowerSet.Iic p)
  rw [hsup, hinf] at hmod
  -- hmod : v (U.erase p) + v (Iic p) = v U + v (Iio p)
  have hmass : v (LowerSet.Iio p) + v.mass p = v (LowerSet.Iic p) := by
    rw [Valuation.mass]; exact add_tsub_cancel_of_le (v.mono hle)
  rw [← hmass, add_comm (v (LowerSet.Iio p)) (v.mass p), ← add_assoc] at hmod
  exact ((ENNReal.add_left_inj (v.ne_top _)).mp hmod).symm

variable [Fintype P]

/-- The finite set of points of a lower set (no decidability needed; `P` is finite). -/
noncomputable def _root_.LowerSet.toFinset (U : LowerSet P) : Finset P :=
  (Set.toFinite (U : Set P)).toFinset

@[simp] theorem _root_.LowerSet.mem_toFinset {U : LowerSet P} {q : P} :
    q ∈ U.toFinset ↔ q ∈ U :=
  Set.Finite.mem_toFinset _

variable [DecidableEq P]

/-- For a **maximal** `p ∈ U`, erasing `p` as a lower set (`↑U \ Ici p`) coincides with removing
just the point `p`, so it matches `Finset.erase`. -/
theorem _root_.LowerSet.toFinset_erase_of_max {U : LowerSet P} {p : P}
    (hmax : ∀ b ∈ U, p ≤ b → b = p) : (U.erase p).toFinset = U.toFinset.erase p := by
  ext q
  simp only [LowerSet.mem_toFinset, Finset.mem_erase, LowerSet.coe_erase, Set.mem_sdiff,
    UpperSet.coe_Ici, Set.mem_Ici]
  constructor
  · rintro ⟨hq, hpq⟩
    exact ⟨fun h => hpq (h ▸ le_refl p), hq⟩
  · rintro ⟨hne, hq⟩
    exact ⟨hq, fun hpq => hne (hmax q hq hpq)⟩

/-- **Finite representation theorem.** Every valuation on `LowerSet P` is the point-measure of
its mass function: `v U = ∑_{p ∈ U} v.mass p`. Proof: strong induction on `|U|`, peeling off a
maximal point via `mass_step`. -/
theorem Valuation.eq_sum_mass (v : Valuation (LowerSet P)) (U : LowerSet P) :
    v U = ∑ p ∈ U.toFinset, v.mass p := by
  suffices h : ∀ n (U : LowerSet P), U.toFinset.card = n →
      v U = ∑ p ∈ U.toFinset, v.mass p from h _ U rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro U hcard
    rcases eq_or_ne U ⊥ with rfl | hUne
    · have hbot : (⊥ : LowerSet P).toFinset = ∅ := by simp [LowerSet.toFinset]
      rw [hbot, Finset.sum_empty, v.map_bot]
    · have hne : (↑U : Set P).Nonempty := Set.nonempty_iff_ne_empty.mpr fun h =>
        hUne (SetLike.coe_injective (h.trans LowerSet.coe_bot.symm))
      obtain ⟨p, hpmax⟩ := (↑U : Set P).toFinite.exists_maximal hne
      have hp : p ∈ U := hpmax.1
      have hmax : ∀ b ∈ U, p ≤ b → b = p := fun b hb hpb => le_antisymm (hpmax.2 hb hpb) hpb
      have hfin : (U.erase p).toFinset = U.toFinset.erase p := LowerSet.toFinset_erase_of_max hmax
      have hcard' : (U.erase p).toFinset.card < n := by
        rw [hfin, ← hcard]; exact Finset.card_erase_lt_of_mem (LowerSet.mem_toFinset.mpr hp)
      rw [v.mass_step hp hmax, IH _ hcard' (U.erase p) rfl, hfin]
      exact Finset.sum_erase_add U.toFinset v.mass (LowerSet.mem_toFinset.mpr hp)

/-- **The mass function is a probability**: `∑ p, v.mass p = 1`. Together with `eq_sum_mass`,
`v.mass` is a genuine probability mass function on the points `P`, and `v` is its point-measure.
Reading the lower sets as the opens of the Alexandrov topology (where the interior operator is
the identity), this says `v = μ ∘ □` — the finite representation theorem: **every
intuitionistic-probability valuation on a finite frame is a classical probability seen through
the interior operator.** -/
theorem Valuation.sum_mass (v : Valuation (LowerSet P)) : ∑ p, v.mass p = 1 := by
  have htop : (⊤ : LowerSet P).toFinset = Finset.univ := by
    ext q; simp [LowerSet.mem_toFinset]
  have h := v.eq_sum_mass ⊤
  rw [htop, v.map_top] at h
  exact h.symm

/-- **The valuation is literally a classical discrete probability distribution.** `v.mass`,
being nonnegative and summing to `1`, is a mathlib `PMF` (probability mass function) on the
points `P`. So a `Valuation (LowerSet P)` *is* a `PMF`, and `v` is that `PMF`'s point-measure
(`eq_sum_toPMF`). This is the finite representation theorem in its most literal classical form:
an intuitionistic-probability valuation on a finite frame is a classical probability. -/
noncomputable def Valuation.toPMF (v : Valuation (LowerSet P)) : PMF P :=
  ⟨v.mass, v.sum_mass ▸ hasSum_fintype v.mass⟩

@[simp] theorem Valuation.toPMF_apply (v : Valuation (LowerSet P)) (p : P) :
    v.toPMF p = v.mass p := rfl

/-- `v` is the point-measure of its `PMF`: `v U = ∑_{p ∈ U} v.toPMF p`. -/
theorem Valuation.eq_sum_toPMF (v : Valuation (LowerSet P)) (U : LowerSet P) :
    v U = ∑ p ∈ U.toFinset, v.toPMF p := v.eq_sum_mass U

-- Sanity: the theorem instantiates at a concrete finite poset (`Fin 2` with its order).
example (v : Valuation (LowerSet (Fin 2))) (U : LowerSet (Fin 2)) :
    v U = ∑ p ∈ U.toFinset, v.mass p := v.eq_sum_mass U

end ConstructiveProb
