/-
# M5 — the sum rule is irreducible: modularity is not implied by disjoint additivity

`constructive_cox` posits modularity of the unconditional plausibility as an explicit
hypothesis, on the grounds that — unlike the product rule, which reduces to Aczél via
conditioning — the sum rule cannot be derived. This file makes that precise: it exhibits a
monotone, normalized plausibility on a (genuinely non-Boolean) frame that is **additive on
disjoint joins** yet **not modular**.

The witness frame is the lattice of lower sets of the three-element poset `V = {o, a, b}` with
`o` below two incomparable elements `a, b` (opens of a "V" shape). Its five lower sets are
`⊥ = ∅ ⊂ {o} ⊂ {o,a}, {o,b} ⊂ {o,a,b} = ⊤`, with `{o,a} ⊓ {o,b} = {o} ≠ ⊥` and
`{o,a} ⊔ {o,b} = ⊤`. Because every nonempty lower set contains the bottom point `o`, the only
disjoint pairs are the trivial ones `(⊥, ·)`, so disjoint additivity holds automatically — while
the value `q {o} = 1/2` in the "interior" breaks modularity at the incomparable pair `{o,a}`,
`{o,b}`: their marginals sum to `1`, but `q ⊤ + q {o} = 1 + 1/2 = 3/2`.

Interpretation: `q (x ⊔ y)` genuinely depends on `q (x ⊓ y)`, not just on `q x` and `q y`. A
Heyting frame has no complements with which to decompose a join into disjoint pieces, so there
is no functional route from the disjunction to inclusion–exclusion. Modularity must be posited;
it is the irreducible constructive content of the sum rule. (Meta-level classical reasoning is
used to decide membership in the counterexample; this is reasoning *about* the theory.)
-/
import ConstructiveProb.Basic

open scoped ENNReal
open Classical

namespace ConstructiveProb

/-- The three-element "V" poset: a bottom `o` below two incomparable elements `a`, `b`. -/
inductive V : Type
  | o | a | b
  deriving DecidableEq

namespace V

instance : PartialOrder V where
  le x y := x = y ∨ x = V.o
  le_refl _ := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with h | h
    · exact h ▸ hyz
    · exact Or.inr h
  le_antisymm x y hxy hyx := by
    rcases hxy with h | h
    · exact h
    · rcases hyx with h' | h'
      · exact h'.symm
      · exact h.trans h'.symm

/-- `o` is the bottom of `V`. -/
theorem o_le (x : V) : V.o ≤ x := Or.inr rfl

theorem not_b_le_a : ¬ V.b ≤ V.a := by rintro (h | h) <;> exact absurd h (by decide)
theorem not_a_le_b : ¬ V.a ≤ V.b := by rintro (h | h) <;> exact absurd h (by decide)

end V

/-! ### Membership helpers on `LowerSet V` -/

theorem mem_top_V (x : V) : x ∈ (⊤ : LowerSet V) := by
  rw [← SetLike.mem_coe, LowerSet.coe_top]; exact Set.mem_univ x

theorem not_mem_bot_V (x : V) : x ∉ (⊥ : LowerSet V) := by
  rw [← SetLike.mem_coe, LowerSet.coe_bot]; exact Set.notMem_empty x

theorem mem_sup_V {x : V} {s t : LowerSet V} : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t := by
  rw [← SetLike.mem_coe, LowerSet.coe_sup, Set.mem_union, SetLike.mem_coe, SetLike.mem_coe]

theorem mem_inf_V {x : V} {s t : LowerSet V} : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := by
  rw [← SetLike.mem_coe, LowerSet.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe]

theorem le_mem {S T : LowerSet V} (h : S ≤ T) {x : V} (hx : x ∈ S) : x ∈ T :=
  LowerSet.coe_subset_coe.2 h hx

/-- The counterexample plausibility on `LowerSet V`: `0` on `⊥`, `1` on `⊤`, `1/2` on the three
interior lower sets. Written via membership of the poset points (`o ∈ S` detects `S ≠ ⊥`; `a` and
`b` both in `S` detects `S = ⊤`), so it is manifestly a function of the lower set. -/
noncomputable def qV (S : LowerSet V) : ℝ≥0∞ :=
  if V.o ∈ S then (if V.a ∈ S ∧ V.b ∈ S then 1 else 2⁻¹) else 0

/-- Every nonempty lower set of `V` contains the bottom point `o`. -/
theorem o_mem_of_ne_bot {S : LowerSet V} (h : S ≠ ⊥) : V.o ∈ S := by
  by_contra ho
  apply h
  ext x
  refine ⟨fun hx => ?_, fun hx => absurd hx (not_mem_bot_V x)⟩
  exact absurd (S.lower' (V.o_le x) hx) ho

theorem qV_bot : qV ⊥ = 0 := by
  unfold qV; rw [if_neg (not_mem_bot_V V.o)]

theorem qV_top : qV ⊤ = 1 := by
  unfold qV
  rw [if_pos (mem_top_V V.o), if_pos ⟨mem_top_V V.a, mem_top_V V.b⟩]

theorem qV_mono : Monotone qV := by
  intro S T hST
  unfold qV
  by_cases hoS : V.o ∈ S
  · rw [if_pos hoS, if_pos (le_mem hST hoS)]
    by_cases hab : V.a ∈ S ∧ V.b ∈ S
    · rw [if_pos hab, if_pos ⟨le_mem hST hab.1, le_mem hST hab.2⟩]
    · rw [if_neg hab]
      split
      · exact ENNReal.inv_le_one.mpr one_le_two
      · exact le_refl _
  · rw [if_neg hoS]; exact zero_le

/-- **Disjoint additivity holds** — trivially, because the only disjoint pairs are `(⊥, ·)`: two
nonempty lower sets both contain `o`, so their meet is nonempty. -/
theorem qV_disjoint_additive (S T : LowerSet V) (h : S ⊓ T = ⊥) :
    qV (S ⊔ T) = qV S + qV T := by
  have key : S = ⊥ ∨ T = ⊥ := by
    by_contra hcon
    push_neg at hcon
    have : V.o ∈ S ⊓ T := mem_inf_V.mpr ⟨o_mem_of_ne_bot hcon.1, o_mem_of_ne_bot hcon.2⟩
    rw [h] at this
    exact not_mem_bot_V V.o this
  rcases key with h | h
  · rw [h, bot_sup_eq, qV_bot, zero_add]
  · rw [h, sup_bot_eq, qV_bot, add_zero]

/-! ### Values of `qV` on the two principal lower sets and their join/meet -/

theorem qV_Iic_a : qV (LowerSet.Iic V.a) = 2⁻¹ := by
  unfold qV
  rw [if_pos (LowerSet.mem_Iic_iff.mpr (V.o_le V.a)),
    if_neg (fun hab => V.not_b_le_a (LowerSet.mem_Iic_iff.mp hab.2))]

theorem qV_Iic_b : qV (LowerSet.Iic V.b) = 2⁻¹ := by
  unfold qV
  rw [if_pos (LowerSet.mem_Iic_iff.mpr (V.o_le V.b)),
    if_neg (fun hab => V.not_a_le_b (LowerSet.mem_Iic_iff.mp hab.1))]

theorem qV_Iic_a_sup_Iic_b : qV (LowerSet.Iic V.a ⊔ LowerSet.Iic V.b) = 1 := by
  unfold qV
  rw [if_pos (mem_sup_V.mpr (Or.inl (LowerSet.mem_Iic_iff.mpr (V.o_le V.a)))),
    if_pos ⟨mem_sup_V.mpr (Or.inl (LowerSet.mem_Iic_iff.mpr (le_refl V.a))),
      mem_sup_V.mpr (Or.inr (LowerSet.mem_Iic_iff.mpr (le_refl V.b)))⟩]

theorem qV_Iic_a_inf_Iic_b : qV (LowerSet.Iic V.a ⊓ LowerSet.Iic V.b) = 2⁻¹ := by
  unfold qV
  rw [if_pos (mem_inf_V.mpr ⟨LowerSet.mem_Iic_iff.mpr (V.o_le V.a),
      LowerSet.mem_Iic_iff.mpr (V.o_le V.b)⟩),
    if_neg (fun hab => V.not_a_le_b (LowerSet.mem_Iic_iff.mp (mem_inf_V.mp hab.1).2))]

/-- **Modularity fails** at the incomparable pair `{o,a}, {o,b}`: `½ + ½ = 1 ≠ 1 + ½`. -/
theorem qV_not_modular :
    ¬ (∀ S T : LowerSet V, qV S + qV T = qV (S ⊔ T) + qV (S ⊓ T)) := by
  intro hmod
  have h := hmod (LowerSet.Iic V.a) (LowerSet.Iic V.b)
  rw [qV_Iic_a, qV_Iic_b, qV_Iic_a_sup_Iic_b, qV_Iic_a_inf_Iic_b,
    ENNReal.inv_two_add_inv_two] at h
  -- h : 1 = 1 + 2⁻¹
  have h2 : (2 : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
  exact (ENNReal.lt_add_right ENNReal.one_ne_top h2).ne h

/-- **There is no disjunction functional.** Even the *weakest* possible sum rule — that
`q (x ⊔ y)` be some fixed function `S` of the marginals `q x` and `q y` — is impossible here:
`(↓a, ↓a)` and `(↓a, ↓b)` have identical marginals (`½, ½`) but joins `↓a` and `⊤` with different
values (`½` and `1`). So the disjunction is genuinely *not* a function of its marginals; this is
the sharp form of why modularity (a relation among four values, involving `q (x ⊓ y)`) cannot be
recovered from the disjunction data — strengthening `modularity_irreducible` from "not implied by
disjoint additivity" to "not implied by *any* binary functional of the marginals". -/
theorem no_disjunction_functional :
    ¬ ∃ S : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞, ∀ x y : LowerSet V, qV (x ⊔ y) = S (qV x) (qV y) := by
  rintro ⟨S, hS⟩
  -- pair (↓a, ↓a): join is ↓a, so S ½ ½ = ½
  have h1 := hS (LowerSet.Iic V.a) (LowerSet.Iic V.a)
  rw [qV_Iic_a, sup_idem, qV_Iic_a] at h1
  -- pair (↓a, ↓b): join is ⊤, so S ½ ½ = 1
  have h2 := hS (LowerSet.Iic V.a) (LowerSet.Iic V.b)
  rw [qV_Iic_a, qV_Iic_b, qV_Iic_a_sup_Iic_b] at h2
  -- h1 : ½ = S ½ ½, h2 : 1 = S ½ ½ ⟹ ½ = 1
  have : (2⁻¹ : ℝ≥0∞) = 1 := h1.trans h2.symm
  exact absurd this (ne_of_lt (ENNReal.inv_lt_one.mpr ENNReal.one_lt_two))

/-- **Modularity is irreducible.** There is a monotone, normalized plausibility on a (non-Boolean)
frame that is additive on disjoint joins yet not modular — so modularity cannot be derived from
the disjunction/sum data alone and must be posited (as it is in `constructive_cox`). The
companion `no_disjunction_functional` sharpens the obstruction: `q (x ⊔ y)` is not even a
function of `q x` and `q y`. -/
theorem modularity_irreducible :
    ∃ (Ω : Type) (_ : Order.Frame Ω) (q : Ω → ℝ≥0∞),
      Monotone q ∧ q ⊥ = 0 ∧ q ⊤ = 1 ∧
      (∀ x y : Ω, x ⊓ y = ⊥ → q (x ⊔ y) = q x + q y) ∧
      ¬ (∀ x y : Ω, q x + q y = q (x ⊔ y) + q (x ⊓ y)) :=
  ⟨LowerSet V, inferInstance, qV, qV_mono, qV_bot, qV_top, qV_disjoint_additive, qV_not_modular⟩

end ConstructiveProb
