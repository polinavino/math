/-
# The general structural theorem: atoms are a sub-probability

For an *arbitrary* frame `LowerSet P` (no finiteness, no Scott-continuity), the atomic part of
a valuation is always dominated by the valuation: `∑' p, v.mass p ≤ v ⊤`. Equivalently, the
"point masses" of any localic valuation sum to at most its total — a Lebesgue-decomposition
flavour, with the deficit `v ⊤ − ∑' p, v.mass p` being the *diffuse* (non-atomic) part.

This unifies the earlier results: on a finite frame (or on `ℕ` under Scott-continuity) the
inequality is an equality (`eq_sum_mass`, `eq_tsum_mass_of_scott`); the `topIndicator`
counterexample is the extreme opposite, where the atomic part is `0`. What it does **not** give
is a representation of the diffuse part — that is the genuinely open M3c (localic Riesz).
-/
import ConstructiveProb.Representation
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped ENNReal BigOperators

namespace ConstructiveProb

variable {P : Type*} [PartialOrder P] [DecidableEq P]

omit [DecidableEq P] in
/-- If `p ≰ q` then `↓p ⊓ ↓q ≤ {x < p}`: an `x ≤ p, ≤ q` cannot equal `p` (else `p ≤ q`). -/
theorem Iic_inf_Iic_le_Iio {p q : P} (h : ¬ p ≤ q) :
    LowerSet.Iic p ⊓ LowerSet.Iic q ≤ LowerSet.Iio p := by
  intro x hx
  obtain ⟨hxp, hxq⟩ := hx
  exact lt_of_le_of_ne hxp (by rintro rfl; exact h hxq)

/-- **The atomic part on a finite generating set is dominated.** For every finite `S`,
`∑ p ∈ S, v.mass p ≤ v (⨆ p ∈ S, ↓p)`. Proof: peel a maximal `p` of `S`; modularity plus
`↓p ⊓ (⨆_{S'} ↓q) ≤ {x < p}` gives `mass p + v(⨆_{S'} ↓q) ≤ v(↓p ⊔ ⨆_{S'} ↓q)`. -/
theorem finite_sum_mass_le (v : Valuation (LowerSet P)) (S : Finset P) :
    ∑ p ∈ S, v.mass p ≤ v (S.sup LowerSet.Iic) := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n IH =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨p, hpmax⟩ := (↑S : Set P).toFinite.exists_maximal (by simpa using hne)
      have hpS : p ∈ S := Finset.mem_coe.mp hpmax.1
      have hmax : ∀ q ∈ S, ¬ p ≤ q ∨ q = p := fun q hq => by
        by_cases hpq : p ≤ q
        · exact Or.inr (le_antisymm (hpmax.2 (Finset.mem_coe.mpr hq) hpq) hpq)
        · exact Or.inl hpq
      have hpS' : p ∉ S.erase p := fun hmem => (Finset.mem_erase.mp hmem).1 rfl
      -- decompositions of the sum and of the generated lower set
      have hsum : ∑ q ∈ S, v.mass q = v.mass p + ∑ q ∈ S.erase p, v.mass q :=
        (Finset.add_sum_erase S v.mass hpS).symm
      have hsup : S.sup LowerSet.Iic = LowerSet.Iic p ⊔ (S.erase p).sup LowerSet.Iic := by
        rw [← Finset.sup_insert, Finset.insert_erase hpS]
      -- the meet bound: `↓p ⊓ (⨆_{S'} ↓q) ≤ {x < p}` since `p` is maximal
      have hAB : LowerSet.Iic p ⊓ (S.erase p).sup LowerSet.Iic ≤ LowerSet.Iio p := by
        rw [Finset.sup_inf_distrib_left]
        refine Finset.sup_le fun q hq => Iic_inf_Iic_le_Iio ?_
        rcases hmax q (Finset.mem_of_mem_erase hq) with hnle | rfl
        · exact hnle
        · exact absurd hq hpS'
      -- induction hypothesis on the smaller set
      have hcard : (S.erase p).card < n := by
        rw [← hn]; exact Finset.card_erase_lt_of_mem hpS
      have hIH : ∑ q ∈ S.erase p, v.mass q ≤ v ((S.erase p).sup LowerSet.Iic) :=
        IH _ hcard (S.erase p) rfl
      -- arithmetic (A = ↓p, B = ⨆_{S'} ↓q)
      have hmod := v.modular (LowerSet.Iic p) ((S.erase p).sup LowerSet.Iic)
      have hIio_le : v (LowerSet.Iio p) ≤ v (LowerSet.Iic p) := v.mono (fun x hx => hx.le)
      have hInf_le : v (LowerSet.Iic p ⊓ (S.erase p).sup LowerSet.Iic) ≤ v (LowerSet.Iio p) :=
        v.mono hAB
      have hkey : v.mass p + v (LowerSet.Iic p ⊓ (S.erase p).sup LowerSet.Iic)
          ≤ v (LowerSet.Iic p) := by
        rw [Valuation.mass]
        calc v (LowerSet.Iic p) - v (LowerSet.Iio p)
                + v (LowerSet.Iic p ⊓ (S.erase p).sup LowerSet.Iic)
            ≤ v (LowerSet.Iic p) - v (LowerSet.Iio p) + v (LowerSet.Iio p) := by gcongr
          _ = v (LowerSet.Iic p) := tsub_add_cancel_of_le hIio_le
      rw [hsum, hsup]
      have h2 : v.mass p + v ((S.erase p).sup LowerSet.Iic)
              + v (LowerSet.Iic p ⊓ (S.erase p).sup LowerSet.Iic)
          ≤ v (LowerSet.Iic p ⊔ (S.erase p).sup LowerSet.Iic)
              + v (LowerSet.Iic p ⊓ (S.erase p).sup LowerSet.Iic) :=
        calc v.mass p + v ((S.erase p).sup LowerSet.Iic)
                + v (LowerSet.Iic p ⊓ (S.erase p).sup LowerSet.Iic)
            = v.mass p + v (LowerSet.Iic p ⊓ (S.erase p).sup LowerSet.Iic)
                + v ((S.erase p).sup LowerSet.Iic) := by rw [add_right_comm]
          _ ≤ v (LowerSet.Iic p) + v ((S.erase p).sup LowerSet.Iic) := by gcongr
          _ = v (LowerSet.Iic p ⊔ (S.erase p).sup LowerSet.Iic)
                + v (LowerSet.Iic p ⊓ (S.erase p).sup LowerSet.Iic) := hmod
      calc v.mass p + ∑ q ∈ S.erase p, v.mass q
          ≤ v.mass p + v ((S.erase p).sup LowerSet.Iic) := by gcongr
        _ ≤ v (LowerSet.Iic p ⊔ (S.erase p).sup LowerSet.Iic) :=
            (ENNReal.add_le_add_iff_right (v.ne_top _)).mp h2

/-- **The atoms are a sub-probability (general).** For an arbitrary frame `LowerSet P`,
`∑' p, v.mass p ≤ v ⊤`. The finite/Scott-continuous cases are equality; the deficit is the
diffuse part. -/
theorem tsum_mass_le (v : Valuation (LowerSet P)) : ∑' p, v.mass p ≤ v ⊤ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun S => (finite_sum_mass_le v S).trans (v.mono le_top)

/-- The point-masses of any localic valuation sum to at most `1`. -/
theorem tsum_mass_le_one (v : Valuation (LowerSet P)) : ∑' p, v.mass p ≤ 1 :=
  (tsum_mass_le v).trans (v.le_one ⊤)

/-- **Point-representable = purely atomic.** A valuation is recovered by its point-masses
exactly when it has no diffuse part; the general theorem `tsum_mass_le` says the diffuse part
`v ⊤ − ∑' p, v.mass p` is always `≥ 0`, and this predicate names the case where it is `0`. -/
def IsPurelyAtomic (v : Valuation (LowerSet P)) : Prop := ∑' p, v.mass p = v ⊤

end ConstructiveProb
