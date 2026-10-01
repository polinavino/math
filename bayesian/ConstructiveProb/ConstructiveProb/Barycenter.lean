/-
# The measure version: the calculus is the set of barycenters

For an arbitrary set `Ev` of events and a set `S` of certain states, a vector `x` satisfies every
finitely supported affine law valid on `S` iff it is the barycenter of a probability measure on
the space of truth assignments `Ev → Bool` that is concentrated on the certain states window by
window (`laws_iff_barycenter`):

  `x e = μ {σ | σ e = true}` for every event `e`, and `μ(bad F) = 0` for every finite window `F`,

where `bad F` is the set of assignments whose restriction to `F` is the restriction of no certain
state. (For countably many events this says `μ` is concentrated on the closure of the certain
states.) The existence direction is a compactness argument: the window mixtures of
`laws_iff_local_Mix` are probability measures on the compact space `Ev → Bool`, and a cluster
point along the directed set of windows has the right marginals.
-/
import ConstructiveProb.Recipe

open scoped ENNReal NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology

namespace ConstructiveProb

/-- Truth assignments, with the product topology and its Borel σ-algebra. -/
def Cfg (Ev : Type) := Ev → Bool

namespace Cfg

variable {Ev : Type}

instance : TopologicalSpace (Cfg Ev) := inferInstanceAs (TopologicalSpace (Ev → Bool))
instance : CompactSpace (Cfg Ev) := inferInstanceAs (CompactSpace (Ev → Bool))
instance : T2Space (Cfg Ev) := inferInstanceAs (T2Space (Ev → Bool))
instance : MeasurableSpace (Cfg Ev) := borel _
instance : BorelSpace (Cfg Ev) := ⟨rfl⟩

/-- The `{0,1}`-vector of an assignment. -/
noncomputable def vec (σ : Cfg Ev) : Ev → ℝ≥0∞ := fun e => if σ e then 1 else 0

/-- The assignment of a certain state. -/
noncomputable def ofVec (s : Ev → ℝ≥0∞) : Cfg Ev := fun e => decide (s e = 1)

theorem vec_ofVec {s : Ev → ℝ≥0∞} (hs : IsSharpVec s) : vec (ofVec s) = s := by
  funext e; simp only [vec, ofVec]; rcases hs e with h | h <;> simp [h]

theorem continuous_apply' (e : Ev) : Continuous fun σ : Cfg Ev => σ e :=
  (_root_.continuous_apply e : Continuous fun σ : Ev → Bool => σ e)

/-- Sets depending only on a finite window are clopen. -/
theorem isClopen_window (F : Finset Ev) (P : (F → Bool) → Prop) :
    IsClopen {σ : Cfg Ev | P (fun e => σ e.1)} := by
  have hc : Continuous fun σ : Cfg Ev => (fun e : F => σ e.1) :=
    continuous_pi fun e => continuous_apply' e.1
  exact (isClopen_discrete {g | P g}).preimage hc

/-- `σ` agrees on the window `F` with some certain state. -/
def Good (S : Set (Ev → ℝ≥0∞)) (F : Finset Ev) (σ : Cfg Ev) : Prop :=
  ∃ s ∈ S, ∀ e : F, s e.1 = vec σ e.1

/-- Assignments that on the window `F` look like no certain state. -/
def bad (S : Set (Ev → ℝ≥0∞)) (F : Finset Ev) : Set (Cfg Ev) := {σ | ¬ Good S F σ}

theorem isClopen_bad (S : Set (Ev → ℝ≥0∞)) (F : Finset Ev) : IsClopen (bad S F) :=
  isClopen_window F (fun g => ¬ ∃ s ∈ S, ∀ e : F, s e.1 = if g e then 1 else 0)

/-- The event `e` as a set of assignments. -/
def atom (e : Ev) : Set (Cfg Ev) := {σ | σ e = true}

theorem isClopen_atom (e : Ev) : IsClopen (atom (Ev := Ev) e) :=
  (isClopen_discrete {true}).preimage (continuous_apply' e)

open Classical in
/-- The test function `𝟙_U` of a clopen set. -/
noncomputable def testFn {U : Set (Cfg Ev)} (hU : IsClopen U) : Cfg Ev →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun σ => if σ ∈ U then 1 else 0, by
      have h1 : (fun σ => if σ ∈ U then (1 : ℝ≥0) else 0)
          = (fun b : Bool => if b then (1 : ℝ≥0) else 0) ∘ U.boolIndicator := by
        funext σ; by_cases h : σ ∈ U <;> simp [h, Set.boolIndicator]
      rw [h1]
      exact continuous_of_discreteTopology.comp ((continuous_boolIndicator_iff_isClopen U).2 hU)⟩

/-- `ν ↦ ν(U)` is continuous on probability measures for clopen `U`. -/
theorem continuous_eval_clopen {U : Set (Cfg Ev)} (hU : IsClopen U) :
    Continuous fun ν : ProbabilityMeasure (Cfg Ev) => ν.toFiniteMeasure.testAgainstNN (testFn hU) :=
  ProbabilityMeasure.continuous_testAgainstNN_eval _

open Classical in
theorem testFn_eq {U : Set (Cfg Ev)} (hU : IsClopen U) (ν : ProbabilityMeasure (Cfg Ev)) :
    ((ν.toFiniteMeasure.testAgainstNN (testFn hU) : ℝ≥0) : ℝ≥0∞) = (ν : Measure (Cfg Ev)) U := by
  rw [FiniteMeasure.testAgainstNN_coe_eq]
  have : (fun σ => ((testFn hU σ : ℝ≥0) : ℝ≥0∞)) = U.indicator 1 := by
    funext σ
    simp only [testFn, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
      Set.indicator]
    split_ifs <;> simp
  rw [this, lintegral_indicator_one hU.isOpen.measurableSet]
  rfl

end Cfg

open Cfg

variable {Ev : Type}

theorem atom_mem_measurableSet (e : Ev) : MeasurableSet (atom (Ev := Ev) e) :=
  (isClopen_atom e).isOpen.measurableSet

theorem lintegral_vec (μ : Measure (Cfg Ev)) (e : Ev) :
    ∫⁻ σ, vec σ e ∂μ = μ (atom e) := by
  have : (fun σ : Cfg Ev => vec σ e) = (atom e).indicator 1 := by
    funext σ; simp only [vec, atom, Set.indicator, Set.mem_setOf_eq]; split_ifs <;> simp
  rw [this, lintegral_indicator_one (atom_mem_measurableSet e)]

/-- **The measure version of completeness.** -/
theorem laws_iff_barycenter {S : Set (Ev → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s)
    (x : Ev → ℝ≥0∞) :
    (∀ L : FinLaw Ev, (∀ s ∈ S, L.Holds s) → L.Holds x) ↔
      ∃ μ : ProbabilityMeasure (Cfg Ev), (∀ F, (μ : Measure (Cfg Ev)) (bad S F) = 0) ∧
        ∀ e, x e = (μ : Measure (Cfg Ev)) (atom e) := by
  classical
  constructor
  · intro hx
    have hloc := (laws_iff_local_Mix hS x).1 hx
    -- `x e ≤ 1`
    have hle : ∀ e, x e ≤ 1 := by
      intro e
      have := hx ⟨{e}, fun _ => 1, fun _ => 0, 0, 1⟩ (fun s hs => by
        simp only [FinLaw.Holds, Finset.sum_singleton, one_mul, zero_mul, add_zero, zero_add]
        rcases hS s hs e with h | h <;> simp [h])
      simpa [FinLaw.Holds] using this
    -- the window mixtures as probability measures
    have win : ∀ F : Finset Ev, ∃ ν : ProbabilityMeasure (Cfg Ev),
        (∀ G, (ν : Measure (Cfg Ev)) (bad S G) = 0) ∧
        ∀ e ∈ F, (ν : Measure (Cfg Ev)) (atom e) = x e := by
      intro F
      obtain ⟨n, w, r, hr, hw, heq⟩ := hloc F
      choose t ht htr using hr
      let m : Measure (Cfg Ev) := ∑ i, w i • Measure.dirac (ofVec (t i))
      have hm : IsProbabilityMeasure m := ⟨by simp [m, hw]⟩
      have happ : ∀ U : Set (Cfg Ev), MeasurableSet U →
          m U = ∑ i, w i * U.indicator 1 (ofVec (t i)) := by
        intro U hU
        simp [m, Measure.dirac_apply' _ hU]
      refine ⟨⟨m, hm⟩, fun G => ?_, fun e he => ?_⟩
      · change m (bad S G) = 0
        rw [happ _ (isClopen_bad S G).isOpen.measurableSet]
        refine Finset.sum_eq_zero fun i _ => ?_
        have : ofVec (t i) ∉ bad S G := fun hb =>
          hb ⟨t i, ht i, fun e => by rw [vec_ofVec (hS _ (ht i))]⟩
        simp [Set.indicator_of_notMem this]
      · change m (atom e) = x e
        rw [happ _ (atom_mem_measurableSet e)]
        have hxe := congrFun heq ⟨e, he⟩
        simp only [restr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← htr] at hxe
        rw [hxe]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        simp only [atom, Set.indicator, Set.mem_setOf_eq, ofVec, decide_eq_true_eq, Pi.one_apply]
        rcases hS _ (ht i) e with h | h <;> simp [h]
    choose ν hνbad hνat using win
    -- a cluster point along the directed set of windows
    let 𝓕 := Filter.map ν atTop
    haveI : 𝓕.NeBot := Filter.map_neBot
    obtain ⟨μ, -, hμ⟩ := isCompact_univ.exists_clusterPt (f := 𝓕) (le_principal_iff.2 univ_mem)
    refine ⟨μ, fun G => ?_, fun e => ?_⟩
    · let s := {ρ : ProbabilityMeasure (Cfg Ev) |
        ρ.toFiniteMeasure.testAgainstNN (testFn (isClopen_bad S G)) = 0}
      have hs : IsClosed s := isClosed_eq (continuous_eval_clopen (isClopen_bad S G)) continuous_const
      have hmem : s ∈ 𝓕 := Filter.mem_map.2 (Filter.Eventually.of_forall fun F => by
        show _ = _
        have := testFn_eq (isClopen_bad S G) (ν F)
        rw [hνbad F G] at this
        exact_mod_cast this)
      have := hs.closure_eq ▸ hμ.mem_closure_of_mem s hmem
      have h2 := testFn_eq (isClopen_bad S G) μ
      rw [show μ.toFiniteMeasure.testAgainstNN (testFn (isClopen_bad S G)) = 0 from this] at h2
      exact_mod_cast h2.symm
    · let s := {ρ : ProbabilityMeasure (Cfg Ev) |
        ρ.toFiniteMeasure.testAgainstNN (testFn (isClopen_atom e)) = (x e).toNNReal}
      have hs : IsClosed s := isClosed_eq (continuous_eval_clopen (isClopen_atom e)) continuous_const
      have hmem : s ∈ 𝓕 := Filter.mem_map.2 (Filter.mem_atTop_sets.2 ⟨{e}, fun F hF => by
        show _ = _
        have := testFn_eq (isClopen_atom e) (ν F)
        rw [hνat F e (hF (Finset.mem_singleton_self e))] at this
        rw [← ENNReal.coe_inj, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top
          (hle e))]
        exact this⟩)
      have := hs.closure_eq ▸ hμ.mem_closure_of_mem s hmem
      have h2 := testFn_eq (isClopen_atom e) μ
      rw [show μ.toFiniteMeasure.testAgainstNN (testFn (isClopen_atom e)) = (x e).toNNReal
        from this, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hle e))] at h2
      exact h2
  · rintro ⟨μ, hbad, hat⟩ L hL
    -- integrate the law against `μ`
    have hint : ∀ c : Ev → ℝ≥0∞, ∀ k : ℝ≥0∞,
        ∑ e ∈ L.F, c e * x e + k = ∫⁻ σ, (∑ e ∈ L.F, c e * vec σ e + k) ∂(μ : Measure (Cfg Ev)) := by
      intro c k
      have hmeas : ∀ e, Measurable fun σ : Cfg Ev => vec σ e := fun e => by
        have : (fun σ : Cfg Ev => vec σ e) = (atom e).indicator 1 := by
          funext σ; simp only [vec, atom, Set.indicator, Set.mem_setOf_eq]; split_ifs <;> simp
        rw [this]; exact measurable_one.indicator (atom_mem_measurableSet e)
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_finset_sum _ fun e _ => (hmeas e).const_mul _]
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [lintegral_const_mul _ (hmeas e), lintegral_vec, hat]
    unfold FinLaw.Holds
    rw [hint, hint]
    refine lintegral_mono_ae ?_
    have : ∀ᵐ σ ∂(μ : Measure (Cfg Ev)), σ ∉ bad S L.F := measure_eq_zero_iff_ae_notMem.1 (hbad _)
    filter_upwards [this] with σ hσ
    simp only [bad, Set.mem_setOf_eq, not_not] at hσ
    obtain ⟨s, hs, hsσ⟩ := hσ
    have key : ∀ c : Ev → ℝ≥0∞, ∑ e ∈ L.F, c e * vec σ e = ∑ e ∈ L.F, c e * s e := by
      intro c
      rw [← Finset.sum_attach L.F, ← Finset.sum_attach L.F]
      exact Finset.sum_congr rfl fun e _ => by rw [hsσ e]
    rw [key, key]
    exact hL s hs

end ConstructiveProb
