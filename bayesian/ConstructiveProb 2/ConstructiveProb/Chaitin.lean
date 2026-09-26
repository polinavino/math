/-
# Cantor space cylinders: the measure-theoretic core of Chaitin's Ω

`sec-bridges.tex` describes Chaitin's halting probability Ω as a further instance of the
GMT bridge (`Measure.toValuationOpens`): fix a universal prefix-free machine `U`, equip
`2^ω` (here `ℕ → Bool`) with the fair-coin product measure, and read the halting set
`H = ⋃_{p halts} [p]` (a union of cylinders over the halting programs) through the bridge.
This file mechanizes the measure-theoretic content of that instance: it does **not** build a
universal prefix-free machine (that is genuine computability theory, out of scope here), but it
does mechanize, on the honest infinite Cantor space with `mathlib`'s own infinite product
measure (`Measure.infinitePi`), the two facts the paragraph asserts about the *event* `H`:

1. **A basic cylinder is clopen and has the expected measure.** For a finite word
   `w : List Bool`, the cylinder `wordCylinder w` (sequences extending `w`) is open, and
   `cantorMeasure (wordCylinder w) = 2⁻¹ ^ w.length` — this is `μ([p]) = 2^{-|p|}` for a single
   halting program `p`.
2. **Prefix-free ⇒ disjoint.** Distinct cylinders of a prefix-free (antichain) set of words are
   disjoint, and for a *finite* prefix-free set `F`, the measure of their union is the sum
   `∑_{w ∈ F} 2⁻¹ ^ w.length` — this is Kraft's-inequality-style content, mechanized for finite
   antichains. (The full Ω is a sum over the *infinite* set of halting programs of an actual
   universal machine; extending the finite sum here to a countable one, and exhibiting such a
   machine, is future work.)
-/
import ConstructiveProb.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory unitInterval

namespace ConstructiveProb

/-! ### The fair coin and the Cantor space measure -/

/-- The fair-coin point of the unit interval, `1/2`. -/
noncomputable def halfI : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

theorem toNNReal_halfI : unitInterval.toNNReal halfI = (1 / 2 : ℝ≥0) := by
  rfl

@[simp] theorem symm_halfI : σ halfI = halfI := by
  ext
  change (1 : ℝ) - 1 / 2 = 1 / 2
  norm_num

/-- One fair coin flip: `Ber(true, false, 1/2)` on `Bool`. -/
noncomputable def fairCoin : Measure Bool := Ber(true, false, halfI)

instance : IsProbabilityMeasure fairCoin := by
  unfold fairCoin; infer_instance

theorem fairCoin_apply_true : fairCoin ({true} : Set Bool) = 1 / 2 := by
  have h := bernoulliMeasure_apply_of_mem_of_notMem (x := true) (y := false)
    halfI (s := ({true} : Set Bool)) (by measurability) (by simp) (by simp)
  simp only [fairCoin]
  rw [h, toNNReal_halfI]
  norm_num

theorem fairCoin_apply_false : fairCoin ({false} : Set Bool) = 1 / 2 := by
  have h := bernoulliMeasure_apply_of_notMem_of_mem (x := true) (y := false)
    halfI (s := ({false} : Set Bool)) (by measurability) (by simp) (by simp)
  simp only [fairCoin]
  rw [h, symm_halfI, toNNReal_halfI]
  norm_num

theorem fairCoin_apply_singleton (b : Bool) : fairCoin ({b} : Set Bool) = 1 / 2 := by
  cases b
  · exact fairCoin_apply_false
  · exact fairCoin_apply_true

/-- The Cantor space `ℕ → Bool`, equipped with the fair-coin infinite product measure. -/
noncomputable def cantorMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => fairCoin)

instance : IsProbabilityMeasure cantorMeasure := by
  unfold cantorMeasure; infer_instance

/-! ### Basic cylinders: the events "extends the finite word `w`" -/

/-- The set of coordinate-restrictions imposed by a finite word `w`: fixed to `w[i]` for
`i < w.length`, unconstrained elsewhere. -/
noncomputable def wordRestriction (w : List Bool) : ℕ → Set Bool :=
  fun i => if h : i < w.length then {w[i]} else Set.univ

/-- **The basic cylinder of a finite word.** The set of infinite bit strings that extend the
finite word `w` in their first `w.length` coordinates. -/
def wordCylinder (w : List Bool) : Set (ℕ → Bool) :=
  Set.pi (Finset.range w.length : Set ℕ) (wordRestriction w)

theorem mem_wordCylinder {w : List Bool} {x : ℕ → Bool} :
    x ∈ wordCylinder w ↔ ∀ i, (h : i < w.length) → x i = w[i] := by
  simp only [wordCylinder, Set.mem_pi, Finset.coe_range, Set.mem_Iio, wordRestriction]
  constructor
  · intro hx i h
    have := hx i h
    rwa [dif_pos h, Set.mem_singleton_iff] at this
  · intro hx i h
    rw [dif_pos h, Set.mem_singleton_iff]
    exact hx i h

/-- **A basic cylinder is open.** It restricts finitely many coordinates of a discrete space. -/
theorem isOpen_wordCylinder (w : List Bool) : IsOpen (wordCylinder w) := by
  apply isOpen_set_pi (Finset.range w.length).finite_toSet
  intro i _
  exact isOpen_discrete _

/-- **A basic cylinder has the expected measure**, `μ([w]) = 2^{-|w|}`: the measure bridge's
half-life, one halting program at a time. -/
theorem cantorMeasure_wordCylinder (w : List Bool) :
    cantorMeasure (wordCylinder w) = (1 / 2) ^ w.length := by
  have hmt : ∀ i ∈ (Finset.range w.length), MeasurableSet (wordRestriction w i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    simp [wordRestriction, dif_pos hi]
  have hprod := Measure.infinitePi_pi (μ := fun _ : ℕ => fairCoin) (s := Finset.range w.length)
    (t := wordRestriction w) hmt
  have hpt : ∀ i ∈ Finset.range w.length, fairCoin (wordRestriction w i) = 1 / 2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [wordRestriction, dif_pos hi]
    exact fairCoin_apply_singleton _
  unfold cantorMeasure wordCylinder
  rw [hprod, Finset.prod_congr rfl hpt]
  simp

/-! ### Prefix-free antichains: disjointness and the finite Kraft sum -/

theorem eq_take_of_forall_getElem_eq {v w : List Bool} (hlen : v.length ≤ w.length)
    (h : ∀ i, (hi : i < v.length) → v[i] = w[i]) : v = w.take v.length := by
  apply List.ext_getElem
  · rw [List.length_take, min_eq_left hlen]
  · intro i h1 h2
    rw [List.getElem_take]
    exact h i h1

/-- **Prefix-free ⇒ disjoint.** Two words neither of which is a prefix of the other name
disjoint cylinders. -/
theorem disjoint_wordCylinder_of_not_prefix {v w : List Bool}
    (hv : ¬ v <+: w) (hw : ¬ w <+: v) : Disjoint (wordCylinder v) (wordCylinder w) := by
  rw [Set.disjoint_left]
  intro x hxv hxw
  rcases le_total v.length w.length with hlen | hlen
  · exact hv <| List.prefix_iff_eq_take.mpr <| eq_take_of_forall_getElem_eq hlen fun i hi =>
      ((mem_wordCylinder.mp hxv) i hi).symm.trans ((mem_wordCylinder.mp hxw) i (hi.trans_le hlen))
  · exact hw <| List.prefix_iff_eq_take.mpr <| eq_take_of_forall_getElem_eq hlen fun i hi =>
      ((mem_wordCylinder.mp hxw) i hi).symm.trans ((mem_wordCylinder.mp hxv) i (hi.trans_le hlen))

/-- A finite set of words is **prefix-free** if no member is a prefix of a distinct member. -/
def PrefixFree (F : Finset (List Bool)) : Prop :=
  ∀ v ∈ F, ∀ w ∈ F, v ≠ w → ¬ v <+: w

/-- **The finite Kraft sum.** For a finite prefix-free set of words `F`, the measure of the
union of their cylinders is `∑_{w ∈ F} 2^{-|w|}`: Kraft's-inequality-style content, mechanized
for finite antichains. (Chaitin's actual $\Omega$ sums over the *infinite* set of halting
programs of a universal machine; extending this to a countable sum, and exhibiting such a
machine, is future work.) -/
theorem cantorMeasure_biUnion_wordCylinder {F : Finset (List Bool)} (hF : PrefixFree F) :
    cantorMeasure (⋃ w ∈ F, wordCylinder w) = ∑ w ∈ F, (1 / 2 : ℝ≥0∞) ^ w.length := by
  rw [measure_biUnion_finset
    (fun v hv w hw hvw => disjoint_wordCylinder_of_not_prefix (hF v hv w hw hvw)
      (hF w hw v hv (Ne.symm hvw)))
    (fun w _ => (isOpen_wordCylinder w).measurableSet)]
  exact Finset.sum_congr rfl fun w _ => cantorMeasure_wordCylinder w

end ConstructiveProb
