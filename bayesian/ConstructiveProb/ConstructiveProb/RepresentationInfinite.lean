/-
# The finite representation theorem is tight: the infinite obstruction

Companion to `Representation.lean`. The finite representation theorem
(`Valuation.eq_sum_mass`) says every valuation on a *finite* frame is the point-measure of its
mass function. Here we show the **finiteness hypothesis is necessary**: on the infinite frame
`LowerSet ℕ` (the chain `ω + 1`) there is a valuation whose entire mass "escapes to infinity" —
`v.mass n = 0` for every `n`, yet `v ⊤ = 1`, so `∑' n, v.mass n = 0 ≠ 1 = v ⊤`.

The valuation is the indicator of `⊤`. Its mass vanishes because every *proper* lower set of
`ℕ` is bounded (`= Iio m`), hence gets value `0`; the unit of mass sits on the completely-prime
filter `⊤`, a *point* of the locale `pt(LowerSet ℕ) = ℕ ∪ {∞}` that is **not** an element of
`ℕ`. This is precisely why a general representation must range over `pt(Ω)` (all points), not
over `P` — and why the correct general hypothesis is Scott-continuity (which this valuation
violates: `v ⊤ = 1` but `⨆ n, v (Iic n) = 0`).

*Note on `Classical`.* Deciding `U = ⊤` for a lower set of `ℕ` is not constructive (it is a
universal statement over `ℕ`), so the definition below uses classical logic. This is
legitimate here: it constructs a **counterexample** — classical meta-reasoning *about* the
theory — and does not enter the constructive positive development in `Basic`/`Representation`.
-/
import ConstructiveProb.Representation
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped ENNReal

namespace ConstructiveProb

example : Order.Frame (LowerSet ℕ) := inferInstance

/-- In `LowerSet ℕ`, `⊤` is join-irreducible: a proper lower set of `ℕ` is bounded (`= Iio m`),
and a union of two bounded lower sets is bounded, so cannot be all of `ℕ`. -/
theorem top_sup_irred {U V : LowerSet ℕ} (h : U ⊔ V = ⊤) : U = ⊤ ∨ V = ⊤ := by
  by_contra hcon
  obtain ⟨hU, hV⟩ := not_or.mp hcon
  have hUcoe : (↑U : Set ℕ) ≠ Set.univ := fun h' =>
    hU (SetLike.coe_injective (h'.trans LowerSet.coe_top.symm))
  have hVcoe : (↑V : Set ℕ) ≠ Set.univ := fun h' =>
    hV (SetLike.coe_injective (h'.trans LowerSet.coe_top.symm))
  obtain ⟨m, hm⟩ := (U.lower.eq_univ_or_Iio).resolve_left hUcoe
  obtain ⟨m', hm'⟩ := (V.lower.eq_univ_or_Iio).resolve_left hVcoe
  have huniv : (↑(U ⊔ V) : Set ℕ) = Set.univ := by rw [h]; exact LowerSet.coe_top
  rw [LowerSet.coe_sup, hm, hm'] at huniv
  have hmem : max m m' ∈ Set.Iio m ∪ Set.Iio m' := huniv ▸ Set.mem_univ _
  rcases hmem with h1 | h1
  · exact absurd h1 (not_lt.mpr (le_max_left m m'))
  · exact absurd h1 (not_lt.mpr (le_max_right m m'))

open Classical in
/-- The **indicator of `⊤`** on `LowerSet ℕ`: `1` at `⊤`, `0` on every proper lower set. A valid
valuation (modularity uses `top_sup_irred`). Classical, by the note above. -/
noncomputable def topIndicator : Valuation (LowerSet ℕ) where
  toFun U := if U = ⊤ then 1 else 0
  map_bot' := by
    have h : (⊥ : LowerSet ℕ) ≠ ⊤ := by
      intro heq
      have h1 : (0 : ℕ) ∈ (⊤ : LowerSet ℕ) := by simp
      rw [← heq] at h1
      simp at h1
    rw [if_neg h]
  map_top' := by rw [if_pos rfl]
  mono' U V h := by
    change (if U = ⊤ then (1 : ℝ≥0∞) else 0) ≤ if V = ⊤ then 1 else 0
    split_ifs with hU hV hV
    · exact le_rfl
    · exact absurd (top_le_iff.mp (hU ▸ h)) hV
    · exact zero_le
    · exact le_rfl
  modular' U V := by
    change (if U = ⊤ then (1 : ℝ≥0∞) else 0) + (if V = ⊤ then 1 else 0)
        = (if U ⊔ V = ⊤ then 1 else 0) + (if U ⊓ V = ⊤ then 1 else 0)
    by_cases hU : U = ⊤ <;> by_cases hV : V = ⊤
    · simp [hU, hV]
    · have hsup : U ⊔ V = ⊤ := by rw [hU, top_sup_eq]
      have hinf : ¬ (U ⊓ V = ⊤) := by rw [hU, top_inf_eq]; exact hV
      simp [hU, hV, hsup, hinf]
    · have hsup : U ⊔ V = ⊤ := by rw [hV, sup_top_eq]
      have hinf : ¬ (U ⊓ V = ⊤) := by rw [hV, inf_top_eq]; exact hU
      simp [hU, hV, hsup, hinf]
    · have hsup : ¬ (U ⊔ V = ⊤) := fun h => (top_sup_irred h).elim hU hV
      have hinf : ¬ (U ⊓ V = ⊤) := fun h => hU (top_le_iff.mp (h ▸ inf_le_left))
      simp [hU, hV, hsup, hinf]

@[simp] theorem topIndicator_apply (U : LowerSet ℕ) :
    topIndicator U = if U = ⊤ then 1 else 0 := rfl

/-- Every principal/strict lower set of `ℕ` is proper (`≠ ⊤`), because it misses a point. -/
theorem Iic_ne_top (n : ℕ) : (LowerSet.Iic n : LowerSet ℕ) ≠ ⊤ := fun heq => by
  have : (n + 1 : ℕ) ∈ LowerSet.Iic n := by simp [heq]
  exact absurd (LowerSet.mem_Iic_iff.mp this) (by omega)

theorem Iio_ne_top (n : ℕ) : (LowerSet.Iio n : LowerSet ℕ) ≠ ⊤ := fun heq => by
  have : (n : ℕ) ∈ LowerSet.Iio n := by simp [heq]
  exact absurd (LowerSet.mem_Iio_iff.mp this) (by omega)

/-- **All the mass vanishes**: `topIndicator.mass n = 0` for every `n`, since `Iic n` and
`Iio n` are proper lower sets (value `0`). -/
theorem topIndicator_mass (n : ℕ) : topIndicator.mass n = 0 := by
  rw [Valuation.mass, topIndicator_apply, topIndicator_apply, if_neg (Iic_ne_top n),
    if_neg (Iio_ne_top n), tsub_zero]

/-- **The finite representation theorem is tight.** On the infinite frame `LowerSet ℕ` there is
a valuation (`topIndicator`) whose point-masses sum to `0`, not to `v ⊤ = 1`: the unit of mass
escapes to the non-principal point `⊤`. So the finiteness hypothesis of `eq_sum_mass` cannot be
dropped, and a general representation must range over the points of the locale, not over `ℕ`. -/
theorem exists_valuation_not_point_representable :
    ∃ v : Valuation (LowerSet ℕ), ∑' p, v.mass p ≠ v ⊤ := by
  refine ⟨topIndicator, ?_⟩
  rw [show (∑' n, topIndicator.mass n) = 0 by simp [topIndicator_mass], topIndicator.map_top]
  exact zero_ne_one

/-! ### The positive direction: Scott-continuity suffices on the chain `ℕ`

The obstruction above is exactly a failure of Scott-continuity (`topIndicator ⊤ = 1` but
`⨆ n, topIndicator (Iic n) = 0`). Conversely, a **Scott-continuous** valuation on `LowerSet ℕ`
*is* recovered by its point-masses. So on `ℕ`, point-representability ⟺ Scott-continuity. -/

theorem LowerSet.Iio_succ (n : ℕ) : LowerSet.Iio (n + 1) = LowerSet.Iic n := by
  apply SetLike.coe_injective
  ext j
  simp [LowerSet.coe_Iio, LowerSet.coe_Iic, Nat.lt_succ_iff]

theorem LowerSet.Iio_zero : LowerSet.Iio (0 : ℕ) = (⊥ : LowerSet ℕ) := by
  apply SetLike.coe_injective
  simp [LowerSet.coe_Iio]

/-- Telescoping: the partial sums of the mass function recover `v` on the finite prefixes. -/
theorem partial_sum_mass (v : Valuation (LowerSet ℕ)) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), v.mass k = v (LowerSet.Iic n) := by
  induction n with
  | zero => rw [Finset.sum_range_one, Valuation.mass, LowerSet.Iio_zero, v.map_bot, tsub_zero]
  | succ n IH =>
    rw [Finset.sum_range_succ, IH, Valuation.mass, LowerSet.Iio_succ]
    exact add_tsub_cancel_of_le
      (v.mono (fun _ hx => LowerSet.mem_Iic_iff.mpr ((LowerSet.mem_Iic_iff.mp hx).trans n.le_succ)))

/-- **Scott-continuity suffices.** If `v ⊤ = ⨆ n, v (Iic n)` (Scott-continuity along the chain
`⊤ = ⨆ Iic n`), then `v` is the point-measure of its masses: `v ⊤ = ∑' n, v.mass n`. -/
theorem eq_tsum_mass_of_scott (v : Valuation (LowerSet ℕ))
    (hsc : v ⊤ = ⨆ n, v (LowerSet.Iic n)) : v ⊤ = ∑' n, v.mass n := by
  have hs : ∀ t : Finset ℕ, ∃ n, t ⊆ Finset.range (n + 1) := fun t =>
    let ⟨n, hn⟩ := Finset.exists_nat_subset_range t
    ⟨n, hn.trans (Finset.range_mono n.le_succ)⟩
  rw [hsc, ENNReal.tsum_eq_iSup_sum' (fun n => Finset.range (n + 1)) hs]
  exact iSup_congr fun n => (partial_sum_mass v n).symm

/-- The obstruction *is* a Scott-continuity failure: `⨆ n, topIndicator (Iic n) = 0 ≠ 1`, so
`topIndicator` violates the hypothesis of `eq_tsum_mass_of_scott`. The two results are
consistent, and together characterise point-representability on `ℕ` as Scott-continuity. -/
theorem topIndicator_not_scott :
    (⨆ n, topIndicator (LowerSet.Iic n)) ≠ topIndicator ⊤ := by
  have h0 : (⨆ n, topIndicator (LowerSet.Iic n)) = 0 := by
    simp only [topIndicator_apply, Iic_ne_top, if_false, iSup_const]
  rw [h0, topIndicator.map_top]
  exact zero_ne_one

end ConstructiveProb
