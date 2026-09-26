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
      -- no case split on the undecidable `p ≤ q`: for `q ∈ S.erase p` we have `q ≠ p`, and
      -- `p ≤ q` with maximality would force `q = p`, so `¬ p ≤ q` holds outright
      have hmax : ∀ q ∈ S.erase p, ¬ p ≤ q := fun q hq hpq =>
        (Finset.mem_erase.mp hq).1
          (le_antisymm (hpmax.2 (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hq)) hpq) hpq)
      -- decompositions of the sum and of the generated lower set
      have hsum : ∑ q ∈ S, v.mass q = v.mass p + ∑ q ∈ S.erase p, v.mass q :=
        (Finset.add_sum_erase S v.mass hpS).symm
      have hsup : S.sup LowerSet.Iic = LowerSet.Iic p ⊔ (S.erase p).sup LowerSet.Iic := by
        rw [← Finset.sup_insert, Finset.insert_erase hpS]
      -- the meet bound: `↓p ⊓ (⨆_{S'} ↓q) ≤ {x < p}` since `p` is maximal
      have hAB : LowerSet.Iic p ⊓ (S.erase p).sup LowerSet.Iic ≤ LowerSet.Iio p := by
        rw [Finset.sup_inf_distrib_left]
        exact Finset.sup_le fun q hq => Iic_inf_Iic_le_Iio (hmax q hq)
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

/-! ### When is the diffuse part zero? Scott-continuity, in general

`RepresentationInfinite.eq_tsum_mass_of_scott` proves that on the *chain* `ℕ` a valuation is purely
atomic exactly when it is Scott-continuous (compatible with directed suprema). The unit of mass can
only "escape to infinity" when Scott-continuity fails (`topIndicator`).

Here we generalize the positive direction to **any locally-finite-below poset** `P` (every
principal down-set `↓p` is finite): a Scott-continuous valuation on `LowerSet P` is purely atomic.
Intuitively, Scott-continuity says the whole is genuinely approached by its finite pieces, so no
mass can hide "at infinity" — and on the finite pieces the exact finite representation applies. The
full M3c problem (the *diffuse* part for non-spatial or non-Scott frames) remains open; this
closes the Scott-continuous case that was previously only established on `ℕ`. -/

/-- **Finite representation on a single finite lower set** (no `[Fintype P]`). For a lower set `U`
with finite carrier, `v U = ∑_{p ∈ U} v.mass p`. The same maximal-element peel as
`Valuation.eq_sum_mass`, but carried on `U`'s own finiteness, so it applies to finite pieces of an
infinite `P`. -/
theorem Valuation.eq_sum_mass_of_finite (v : Valuation (LowerSet P)) {U : LowerSet P}
    (hU : (U : Set P).Finite) : v U = ∑ p ∈ hU.toFinset, v.mass p := by
  classical
  suffices h : ∀ n (U : LowerSet P) (hU : (U : Set P).Finite),
      hU.toFinset.card = n → v U = ∑ p ∈ hU.toFinset, v.mass p from h _ U hU rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro U hU hcard
    rcases eq_or_ne U ⊥ with rfl | hUne
    · have hbot : hU.toFinset = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Set.Finite.mem_toFinset] at hp
        rw [LowerSet.coe_bot] at hp
        exact Set.notMem_empty p hp
      rw [hbot, Finset.sum_empty, v.map_bot]
    · have hne : (↑U : Set P).Nonempty := Set.nonempty_iff_ne_empty.mpr fun h =>
        hUne (SetLike.coe_injective (h.trans LowerSet.coe_bot.symm))
      obtain ⟨p, hpmax⟩ := hU.exists_maximal hne
      have hp : p ∈ U := hpmax.1
      have hmax : ∀ b ∈ U, p ≤ b → b = p := fun b hb hpb => le_antisymm (hpmax.2 hb hpb) hpb
      have hUe : ((U.erase p : LowerSet P) : Set P).Finite := hU.subset (fun x hx => hx.1)
      have hfin : hUe.toFinset = hU.toFinset.erase p := by
        ext q
        simp only [Set.Finite.mem_toFinset, Finset.mem_erase, LowerSet.coe_erase, Set.mem_sdiff,
          UpperSet.coe_Ici, Set.mem_Ici, SetLike.mem_coe]
        constructor
        · rintro ⟨hq, hpq⟩; exact ⟨fun h => hpq (le_of_eq h.symm), hq⟩
        · rintro ⟨hqp, hq⟩; exact ⟨hq, fun hpq => hqp (hmax q hq hpq)⟩
      have hcard' : hUe.toFinset.card < n := by
        rw [hfin, ← hcard]
        exact Finset.card_erase_lt_of_mem (Set.Finite.mem_toFinset _ |>.mpr hp)
      rw [v.mass_step hp hmax, IH _ hcard' (U.erase p) hUe rfl, hfin]
      exact Finset.sum_erase_add hU.toFinset v.mass (Set.Finite.mem_toFinset _ |>.mpr hp)

omit [DecidableEq P] in
/-- **`⊤` is the directed supremum of the finitely-generated lower sets.** `⊤ = ⨆_S ⨆_{p∈S} ↓p` —
the canonical directed family generating the top, against which Scott-continuity is tested. -/
theorem LowerSet.top_eq_iSup_finsetSup_Iic :
    (⊤ : LowerSet P) = ⨆ (S : Finset P), S.sup LowerSet.Iic := by
  apply le_antisymm _ le_top
  intro x _
  have h1 : x ∈ (({x} : Finset P).sup LowerSet.Iic) := by
    rw [Finset.sup_singleton]; exact LowerSet.mem_Iic_iff.mpr le_rfl
  exact le_iSup (fun S : Finset P => S.sup LowerSet.Iic) {x} h1

variable [∀ p : P, Finite (Set.Iic p)]

omit [DecidableEq P] in
/-- Under local finiteness below, a finitely-generated lower set `⨆_{p∈S} ↓p` has finite carrier
(a finite union of finite principal down-sets). -/
theorem LowerSet.finsetSup_Iic_finite (S : Finset P) :
    ((S.sup LowerSet.Iic : LowerSet P) : Set P).Finite := by
  classical
  refine Finset.induction_on S ?_ (fun a s _ ih => ?_)
  · simp only [Finset.sup_empty, LowerSet.coe_bot]; exact Set.finite_empty
  · rw [Finset.sup_insert, LowerSet.coe_sup, LowerSet.coe_Iic]
    exact (Set.toFinite (Set.Iic a)).union ih

/-- **Scott-continuity ⟹ purely atomic (general poset).** On any locally-finite-below `P`, if
`v ⊤ = ⨆_S v (⨆_{p∈S} ↓p)` — Scott-continuity along the directed family of
`top_eq_iSup_finsetSup_Iic` — then `v` has no diffuse part: `∑' p, v.mass p = v ⊤`. This generalizes
`eq_tsum_mass_of_scott` from the chain `ℕ` to arbitrary posets. The proof bounds `v` on each finite
piece by the exact finite representation (`eq_sum_mass_of_finite`), then passes to the supremum;
combined with the unconditional `tsum_mass_le` it forces equality. -/
theorem Valuation.isPurelyAtomic_of_scott (v : Valuation (LowerSet P))
    (hsc : v ⊤ = ⨆ (S : Finset P), v (S.sup LowerSet.Iic)) : IsPurelyAtomic v := by
  classical
  refine le_antisymm (tsum_mass_le v) ?_
  rw [hsc]
  refine iSup_le fun S => ?_
  have hfin := LowerSet.finsetSup_Iic_finite S
  rw [v.eq_sum_mass_of_finite hfin]
  exact ENNReal.sum_le_tsum _

end ConstructiveProb
