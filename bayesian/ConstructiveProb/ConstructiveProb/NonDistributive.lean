/-
# A lattice with no sharp valuation at all

`GeneralValuation.lean` shows that the sharp/point correspondence for `LValuation` survives
dropping frame completeness, provided the underlying lattice stays distributive: the proof
factors through `DistribLattice.prime_ideal_of_disjoint_filter_ideal`, a genuinely
distributivity-dependent separation theorem. This file shows distributivity is not a technical
artifact of that proof but the real dividing line, by exhibiting the smallest non-distributive
lattice, `M3` (the "diamond": bottom, three pairwise-incomparable atoms, top), and showing it
admits *no* sharp valuation whatsoever -- not merely a failure of separation, but the collapse
of condition (1) ("the all-or-nothing valuations reconstruct the underlying event logic")
entirely, since there are no all-or-nothing valuations to reconstruct anything with.
-/
import ConstructiveProb.GeneralValuation

noncomputable section

open scoped ENNReal

/-- The **diamond lattice** `M3`: a bottom `z`, three pairwise-incomparable atoms `a, b, c`
(any two join to the top and meet to the bottom), and a top `o`. The smallest non-distributive
(in fact, non-modular-in-the-order-theoretic sense here we care about differently: M3 *is*
order-modular but not distributive) bounded lattice. -/
inductive M3 : Type
  | z | a | b | c | o
  deriving DecidableEq, Repr

namespace M3

instance : Fintype M3 where
  elems := {z, a, b, c, o}
  complete x := by cases x <;> decide

/-- The Boolean-valued order table: `z` below everything, `o` above everything, each atom only
below itself and `o`. -/
def leb : M3 → M3 → Bool
  | z, _ => true
  | _, o => true
  | a, a => true
  | b, b => true
  | c, c => true
  | _, _ => false

/-- The join table: atoms pairwise join to the top. -/
def sup : M3 → M3 → M3
  | z, y => y
  | o, _ => o
  | a, z => a
  | a, o => o
  | a, a => a
  | a, b => o
  | a, c => o
  | b, z => b
  | b, o => o
  | b, a => o
  | b, b => b
  | b, c => o
  | c, z => c
  | c, o => o
  | c, a => o
  | c, b => o
  | c, c => c

/-- The meet table: atoms pairwise meet to the bottom. -/
def inf : M3 → M3 → M3
  | o, y => y
  | z, _ => z
  | a, z => z
  | a, o => a
  | a, a => a
  | a, b => z
  | a, c => z
  | b, z => z
  | b, o => b
  | b, a => z
  | b, b => b
  | b, c => z
  | c, z => z
  | c, o => c
  | c, a => z
  | c, b => z
  | c, c => c

instance : Lattice M3 where
  le x y := leb x y = true
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  sup := sup
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf := inf
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance decLe : DecidableRel ((· ≤ ·) : M3 → M3 → Prop) := fun x y => decEq (leb x y) true

instance : BoundedOrder M3 where
  top := o
  bot := z
  le_top := by decide
  bot_le := by decide

/-- **`M3` is not distributive.** The witness `a ⊓ (b ⊔ c) = a` but `(a ⊓ b) ⊔ (a ⊓ c) = z`. -/
theorem not_distributive : ¬ ∀ x y w : M3, x ⊓ (y ⊔ w) = (x ⊓ y) ⊔ (x ⊓ w) := by decide

/-- **No valuation on `M3` is sharp.** Modularity applied to each pair of atoms forces
`v x + v y = 1` for every two distinct atoms `x, y` (their join is `⊤`, their meet is `⊥`).
If `v` were sharp, `v a, v b, v c ∈ {0, 1}` would have to satisfy all three pairwise sum-to-one
equations simultaneously, which a 2-element codomain cannot support: whichever of `0, 1` is
assigned first forces the second, which forces the third to contradict the first equation
again. This is the collapse, on the smallest non-distributive lattice, of condition (1) --
the all-or-nothing valuations no longer reconstruct anything, because there are none. -/
theorem no_sharp_valuation (v : LValuation M3) : ¬ v.IsSharp := by
  intro hv
  have hab : v a + v b = 1 := by
    have h := v.modular a b
    rw [show a ⊔ b = (⊤ : M3) from rfl, show a ⊓ b = (⊥ : M3) from rfl, v.map_top, v.map_bot,
      add_zero] at h
    exact h
  have hbc : v b + v c = 1 := by
    have h := v.modular b c
    rw [show b ⊔ c = (⊤ : M3) from rfl, show b ⊓ c = (⊥ : M3) from rfl, v.map_top, v.map_bot,
      add_zero] at h
    exact h
  have hac : v a + v c = 1 := by
    have h := v.modular a c
    rw [show a ⊔ c = (⊤ : M3) from rfl, show a ⊓ c = (⊥ : M3) from rfl, v.map_top, v.map_bot,
      add_zero] at h
    exact h
  rcases hv a with ha | ha <;> rcases hv b with hb | hb <;> rcases hv c with hc | hc <;>
    rw [ha, hb] at hab <;> rw [hb, hc] at hbc <;> rw [ha, hc] at hac <;>
    simp_all

theorem exists_lattice_no_sharp_valuation :
    ∃ (Ω : Type) (_ : Lattice Ω) (_ : BoundedOrder Ω), ∀ v : LValuation Ω, ¬ v.IsSharp :=
  ⟨M3, inferInstance, inferInstance, no_sharp_valuation⟩

end M3

end
