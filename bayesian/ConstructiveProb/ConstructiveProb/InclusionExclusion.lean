/-
# Inclusion–exclusion and the ∞-monotone tower: the DS bridge completed

`Belief.lean` proves the 2-monotone (supermodular) inequality — the hallmark of a Dempster–Shafer
belief function — and flags the full `∞`-monotone tower as future work. This file closes that gap.

**The route is not Möbius inversion but a sharper observation.** A valuation is *modular*, and a
frame is a *distributive* lattice; together these give the full **inclusion–exclusion identity,
with equality, for the frame join** — for finite families, constructively, on *any* frame, with
no finiteness or spatiality hypothesis on the frame:

  `v (⋁ i ∈ s, a i) = ∑_{∅ ≠ T ⊆ s} (-1)^{|T|+1} v (⋀ i ∈ T, a i)`.

Because `ℝ≥0∞` has no subtraction worth trusting, we state it additively, splitting the signed sum
into its odd- and even-cardinality halves (`iesOdd`, `iesEven`):

  `v (s.sup a) + iesEven = iesOdd`.

**∞-monotonicity is then a one-liner** — the same one-liner as `two_monotone`: the Booleanization
join `(⋁ a i)ᶜᶜ` dominates the frame join, so

  `iesOdd ≤ v ((s.sup a)ᶜᶜ) + iesEven`,

which, read on the regular (`¬¬`-stable) elements — where `(·)ᶜᶜ ∘ ⊔` *is* the Boolean join and
`⊓` *is* the Boolean meet (meets of regulars are regular, à la Glivenko) — is verbatim **total
monotonicity**: `Bel(⋁ Aᵢ) ≥ ∑_{∅≠T} (-1)^{|T|+1} Bel(⋀_{i∈T} Aᵢ)`. Together with `two_monotone`
(the `n = 2` case) this upgrades the bridge of `Belief.lean`: **the restriction of a valuation to
its Booleanization is a bona fide Dempster–Shafer belief function**, not merely a 2-monotone
capacity.

**The conceptual payoff.** Inclusion–exclusion does *not* fail constructively — it holds on the
nose for the intuitionistic disjunction `⊔`. What total monotonicity records is the *shadow* of
that equality on the Boolean core: rounding the join up to its regular hull `(·)ᶜᶜ` can only add
plausibility, and the defect is exactly the double-negation gap `dnGap (s.sup a)` measured
elsewhere in the development. Additive probability does not "become" a belief function by losing
an axiom; it becomes one by being *read through* the double-negation nucleus.
-/
import ConstructiveProb.Basic
import ConstructiveProb.Belief
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

open scoped ENNReal BigOperators

namespace ConstructiveProb

variable {Ω : Type*} [Order.Frame Ω] {ι : Type*}

/-- Meets distribute over a constant: for a *nonempty* finite meet,
`⋀ j ∈ T, (A ⊓ a j) = A ⊓ ⋀ j ∈ T, a j`. (Nonemptiness is needed: the empty meet is `⊤`.) -/
theorem _root_.Finset.Nonempty.inf_const_inf {T : Finset ι} (hT : T.Nonempty) (A : Ω)
    (a : ι → Ω) : (T.inf fun j => A ⊓ a j) = A ⊓ T.inf a := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i T hi hT IH =>
    rw [Finset.inf_cons, Finset.inf_cons, IH, ← inf_inf_distrib_left]

namespace Valuation

/-- The **odd half of the inclusion–exclusion sum**: `∑_{T ⊆ s, |T| odd} v (⋀ i ∈ T, a i)`.
(Odd-cardinality subsets are automatically nonempty.) -/
noncomputable def iesOdd (v : Valuation Ω) (s : Finset ι) (a : ι → Ω) : ℝ≥0∞ :=
  ∑ T ∈ s.powerset, if Odd T.card then v (T.inf a) else 0

/-- The **even half of the inclusion–exclusion sum**, over *nonempty* subsets:
`∑_{∅ ≠ T ⊆ s, |T| even} v (⋀ i ∈ T, a i)`. -/
noncomputable def iesEven (v : Valuation Ω) (s : Finset ι) (a : ι → Ω) : ℝ≥0∞ :=
  ∑ T ∈ s.powerset, if T.Nonempty ∧ Even T.card then v (T.inf a) else 0

@[simp] theorem iesOdd_empty (v : Valuation Ω) (a : ι → Ω) : v.iesOdd ∅ a = 0 := by
  simp [iesOdd]

@[simp] theorem iesEven_empty (v : Valuation Ω) (a : ι → Ω) : v.iesEven ∅ a = 0 := by
  simp [iesEven]

variable [DecidableEq ι]

/-- Inserting a fresh index `i` into the odd sum: the new odd-cardinality subsets are
`insert i T` for even `T`, contributing the `T = ∅` term `v (a i)` plus the even sum of the
meet-shifted family `a i ⊓ a ·`. -/
theorem iesOdd_insert (v : Valuation Ω) {i : ι} {s : Finset ι} (hi : i ∉ s) (a : ι → Ω) :
    v.iesOdd (insert i s) a
      = v.iesOdd s a + (v (a i) + v.iesEven s fun j => a i ⊓ a j) := by
  rw [iesOdd, Finset.sum_powerset_insert hi]
  congr 1
  have hstep : ∀ T ∈ s.powerset,
      (if Odd (insert i T).card then v ((insert i T).inf a) else 0)
        = (if T = ∅ then v (a i) else 0)
          + (if T.Nonempty ∧ Even T.card then v (T.inf fun j => a i ⊓ a j) else 0) := by
    intro T hT
    have hiT : i ∉ T := fun h => hi (Finset.mem_powerset.mp hT h)
    simp only [Finset.card_insert_of_notMem hiT, Finset.inf_insert, Nat.odd_add_one,
      Nat.not_odd_iff_even]
    rcases eq_or_ne T ∅ with rfl | hne
    · simp
    · have hT' : T.Nonempty := Finset.nonempty_of_ne_empty hne
      rw [if_neg hne, hT'.inf_const_inf, zero_add]
      by_cases he : Even T.card
      · rw [if_pos he, if_pos ⟨hT', he⟩]
      · rw [if_neg he, if_neg fun h => he h.2]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_ite_eq' s.powerset ∅
    (fun _ => v (a i)), if_pos (Finset.empty_mem_powerset s)]
  rfl

/-- Inserting a fresh index `i` into the even sum: the new nonempty-even subsets are
`insert i T` for odd `T`, contributing the odd sum of the meet-shifted family `a i ⊓ a ·`. -/
theorem iesEven_insert (v : Valuation Ω) {i : ι} {s : Finset ι} (hi : i ∉ s) (a : ι → Ω) :
    v.iesEven (insert i s) a = v.iesEven s a + v.iesOdd s fun j => a i ⊓ a j := by
  rw [iesEven, Finset.sum_powerset_insert hi]
  congr 1
  refine Finset.sum_congr rfl fun T hT => ?_
  have hiT : i ∉ T := fun h => hi (Finset.mem_powerset.mp hT h)
  simp only [Finset.card_insert_of_notMem hiT, Finset.inf_insert, Nat.even_add_one,
    Nat.not_even_iff_odd]
  have hne : (insert i T).Nonempty := Finset.insert_nonempty i T
  by_cases ho : Odd T.card
  · have hT' : T.Nonempty := Finset.card_pos.mp ho.pos
    rw [if_pos ⟨hne, ho⟩, if_pos ho, hT'.inf_const_inf]
  · rw [if_neg fun h => ho h.2, if_neg ho]

/-- **Inclusion–exclusion for localic valuations** (ENNReal-safe form). On *any* frame, for any
finite family `a : ι → Ω`,

  `v (⋁ i ∈ s, a i) + ∑_{∅≠T⊆s, |T| even} v (⋀ T a) = ∑_{T⊆s, |T| odd} v (⋀ T a)`,

i.e. the classical identity `v (⋁ aᵢ) = ∑_{∅≠T} (-1)^{|T|+1} v (⋀_{i∈T} aᵢ)` with the signed sum
split into halves so that no subtraction occurs. **Inclusion–exclusion is constructively
innocent**: it needs modularity and frame distributivity, not excluded middle — the intuitionistic
join `⊔` satisfies it with equality. Proof: induction on `s`; the insert step is modularity at
`(a i, ⋁ s a)` plus distributivity `a i ⊓ ⋁ s a = ⋁ (a i ⊓ a ·)`, with the two inductive
hypotheses — for `a` and for the meet-shifted family `a i ⊓ a ·` — assembling the halves. -/
theorem inclusion_exclusion (v : Valuation Ω) (s : Finset ι) (a : ι → Ω) :
    v (s.sup a) + v.iesEven s a = v.iesOdd s a := by
  induction s using Finset.induction_on generalizing a with
  | empty => simp
  | insert i s hi IH =>
    rw [Finset.sup_insert, v.iesOdd_insert hi, v.iesEven_insert hi]
    have hdist : (s.sup fun j => a i ⊓ a j) = a i ⊓ s.sup a :=
      (Finset.sup_inf_distrib_left s a (a i)).symm
    have h1 := IH a
    have h2 := IH (fun j => a i ⊓ a j)
    rw [hdist] at h2
    calc v (a i ⊔ s.sup a) + (v.iesEven s a + v.iesOdd s fun j => a i ⊓ a j)
        = v (a i ⊔ s.sup a) + (v.iesEven s a
            + (v (a i ⊓ s.sup a) + v.iesEven s fun j => a i ⊓ a j)) := by rw [h2]
      _ = (v (a i ⊔ s.sup a) + v (a i ⊓ s.sup a))
            + (v.iesEven s a + v.iesEven s fun j => a i ⊓ a j) := by ring
      _ = (v (a i) + v (s.sup a))
            + (v.iesEven s a + v.iesEven s fun j => a i ⊓ a j) := by
              rw [← v.modular (a i) (s.sup a)]
      _ = (v (s.sup a) + v.iesEven s a)
            + (v (a i) + v.iesEven s fun j => a i ⊓ a j) := by ring
      _ = v.iesOdd s a + (v (a i) + v.iesEven s fun j => a i ⊓ a j) := by rw [h1]

/-- **∞-monotonicity (total monotonicity) — the DS bridge completed.** For every valuation, every
finite family `a : ι → Ω`, the odd inclusion–exclusion sum is dominated through the
*Booleanization* join `(⋁ a)ᶜᶜ`:

  `∑_{|T| odd} v (⋀ T a) ≤ v ((s.sup a)ᶜᶜ) + ∑_{∅≠T, |T| even} v (⋀ T a)`.

Read on the regular elements — where `(s.sup a)ᶜᶜ` *is* the Boolean join and `T.inf a` *is* the
Boolean meet — this is exactly the `n`-monotonicity tower for every `n`:
`Bel(⋁ Aᵢ) ≥ ∑_{∅≠T⊆[n]} (-1)^{|T|+1} Bel(⋀_{i∈T} Aᵢ)`. So the restriction of a valuation to its
Booleanization is a **totally monotone capacity — a bona fide Dempster–Shafer belief function** —
upgrading `two_monotone` (the case `n = 2`). The proof is the same one-liner: inclusion–exclusion
holds with *equality* at the frame join, and monotonicity lifts `s.sup a` to `(s.sup a)ᶜᶜ`; the
inequality's defect is precisely the double-negation gap `dnGap (s.sup a)`. -/
theorem infty_monotone (v : Valuation Ω) (s : Finset ι) (a : ι → Ω) :
    v.iesOdd s a ≤ v ((s.sup a)ᶜᶜ) + v.iesEven s a := by
  rw [← v.inclusion_exclusion s a]
  gcongr
  exact v.mono le_compl_compl

/-- In the classical (Boolean) limit the tower collapses back to an equality: `xᶜᶜ = x`, so
inclusion–exclusion holds with equality *through the Boolean join as well* — recovering the
Kolmogorov inclusion–exclusion formula. The strict-inequality room in `infty_monotone` is
therefore purely the non-classicality of the frame. -/
theorem inclusion_exclusion_boolean {Ω : Type*} [CompleteBooleanAlgebra Ω]
    (v : Valuation Ω) (s : Finset ι) (a : ι → Ω) :
    v ((s.sup a)ᶜᶜ) + v.iesEven s a = v.iesOdd s a := by
  rw [compl_compl]
  exact v.inclusion_exclusion s a

/-! ### Rigidity from a meet-closed generating family

The inclusion–exclusion identity has a uniqueness consequence: a valuation is determined on
every finite join of elements of a `⊓`-closed family by its values on that family.  This is
the abstract form of the product-rigidity theorem of `ProductRigidity.lean`, which is the
instance where the family is the rectangles of a chain product. -/

/-- A nonempty finite meet of members of a `⊓`-closed family stays in the family. -/
theorem inf_mem_of_inf_closed {ι : Type*} {T : Finset ι} (hT : T.Nonempty)
    {G : Set Ω} (hG : ∀ g ∈ G, ∀ g' ∈ G, g ⊓ g' ∈ G) (a : ι → Ω)
    (ha : ∀ i ∈ T, a i ∈ G) : T.inf a ∈ G := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton i => simpa using ha i (by simp)
  | cons i T hi hT IH =>
    rw [Finset.inf_cons]
    exact hG _ (ha i (Finset.mem_cons_self i T)) _
      (IH fun j hj => ha j (Finset.mem_cons_of_mem hj))

/-- **Rigidity from a meet-closed family.**  Two valuations that agree on a `⊓`-closed family
`G` agree on every finite join of members of `G`: by the inclusion–exclusion equality, such a
join's value is determined by values at nonempty meets of members, which lie in `G`. -/
theorem eq_on_finsetSup_of_eq_on {G : Set Ω}
    (hG : ∀ g ∈ G, ∀ g' ∈ G, g ⊓ g' ∈ G) (u u' : Valuation Ω)
    (h : ∀ g ∈ G, u g = u' g) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → Ω) (ha : ∀ i ∈ s, a i ∈ G) :
    u (s.sup a) = u' (s.sup a) := by
  have hodd : u.iesOdd s a = u'.iesOdd s a := by
    refine Finset.sum_congr rfl fun T hT => ?_
    by_cases hoddc : Odd T.card
    · have hTne : T.Nonempty := Finset.card_pos.mp hoddc.pos
      have hmem : T.inf a ∈ G := inf_mem_of_inf_closed hTne hG a
        fun i hi => ha i (Finset.mem_powerset.mp hT hi)
      rw [if_pos hoddc, if_pos hoddc, h _ hmem]
    · rw [if_neg hoddc, if_neg hoddc]
  have heven : u.iesEven s a = u'.iesEven s a := by
    refine Finset.sum_congr rfl fun T hT => ?_
    by_cases hne : T.Nonempty ∧ Even T.card
    · have hmem : T.inf a ∈ G := inf_mem_of_inf_closed hne.1 hG a
        fun i hi => ha i (Finset.mem_powerset.mp hT hi)
      rw [if_pos hne, if_pos hne, h _ hmem]
    · rw [if_neg hne, if_neg hne]
  have h1 := u.inclusion_exclusion s a
  have h2 := u'.inclusion_exclusion s a
  rw [heven, hodd] at h1
  have hfin : u'.iesEven s a ≠ ∞ := by
    refine (ENNReal.sum_lt_top.mpr fun T _ => ?_).ne
    split
    · exact lt_of_le_of_lt (u'.le_one _) ENNReal.one_lt_top
    · exact lt_of_le_of_lt zero_le_one ENNReal.one_lt_top
  exact (ENNReal.add_left_inj hfin).mp (h1.trans h2.symm)

end Valuation

/-- Sanity check: at `s = {0, 1}` the tower's `n = 2` instance is literally the 2-monotone
inequality of `Belief.lean`, `v x + v y ≤ v (x ⊔ y)ᶜᶜ + v (x ⊓ y)`. -/
example (v : Valuation Ω) (x y : Ω) :
    v x + v y ≤ v (x ⊔ y)ᶜᶜ + v (x ⊓ y) := v.two_monotone x y

end ConstructiveProb
