/-
# The ravens in the verification topology

A world assigns to each object `i : I` a kind in `O`. Observations are finite: a verifiable
property is open in the product topology on `I → O`. Some kinds are `bad` (a non-black raven).
The law "no object is bad" is `H`, and its refutation is the counterexample event
`cex bad = {x | ∃ i, x i ∈ bad}`.

* `isOpen_cex`: the counterexample event is verifiable.
* `interior_compl_cex`: over infinitely many objects no finite observation excludes a
  counterexample, so the law has empty interior, and its intuitionistic counterpart
  `¬ cex = ⊥` (`compl_cexOpens`).
* `valuation_compl_cex`, `slack_cex`: every valuation gives the law credence `0`, and the
  slack at the counterexample event is all the remaining mass.
* `classical_law_eq_slack`, `classical_posterior_law`: the classical credence in the law is
  that slack, and its classical posterior given any verifiable evidence is the conditional
  frontier mass, the mass the evidence leaves unrefuted and unverified.
* `posterior_cex_select`: the evidence bears on the law through the counterexample event only.
  If object `j` is known to have a kind in `A` (a raven, or a non-black thing), learning its
  full kind lowers the credence in a counterexample by the conditional prior that `j` was the
  counterexample times the credence that no other object is one. For a selected raven the
  first factor is the frequency of non-black ravens, and for a selected non-black thing it is
  the frequency of ravens among non-black things.
-/
import ConstructiveProb.Overconfidence

open scoped ENNReal
open MeasureTheory TopologicalSpace

namespace ConstructiveProb

namespace Ravens

variable {I O : Type*} [TopologicalSpace O]

/-- The counterexample event: some object has a bad kind. -/
def cex (bad : Set O) : Set (I → O) := {x | ∃ i, x i ∈ bad}

/-- A counterexample among the objects other than `j`. -/
def cexExcept (bad : Set O) (j : I) : Set (I → O) := {x | ∃ i, i ≠ j ∧ x i ∈ bad}

/-- The event that object `j` has a kind in `A`. -/
def obs (j : I) (A : Set O) : Set (I → O) := {x | x j ∈ A}

theorem isOpen_obs (j : I) {A : Set O} (hA : IsOpen A) : IsOpen (obs j A) :=
  hA.preimage (continuous_apply j)

theorem isOpen_cex {bad : Set O} (hbad : IsOpen bad) : IsOpen (cex (I := I) bad) := by
  have : cex (I := I) bad = ⋃ i, obs i bad := by ext; simp [cex, obs]
  rw [this]
  exact isOpen_iUnion fun i => isOpen_obs i hbad

theorem isOpen_cexExcept {bad : Set O} (hbad : IsOpen bad) (j : I) :
    IsOpen (cexExcept bad j) := by
  have : cexExcept bad j = ⋃ i, ⋃ (_ : i ≠ j), obs i bad := by ext; simp [cexExcept, obs]
  rw [this]
  exact isOpen_iUnion fun i => isOpen_iUnion fun _ => isOpen_obs i hbad

/-- **No finite observation verifies a universal law.** Over infinitely many objects, every
neighbourhood of every world contains a world with a counterexample. -/
theorem interior_compl_cex [Infinite I] {bad : Set O} (hne : bad.Nonempty) :
    interior (cex (I := I) bad)ᶜ = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_interior_iff_mem_nhds, nhds_pi, Filter.mem_pi] at hx
  obtain ⟨J, hJ, u, hu, hsub⟩ := hx
  obtain ⟨j, hj⟩ := hJ.exists_notMem
  obtain ⟨o, ho⟩ := hne
  have hy : Function.update x j o ∈ J.pi u := by
    intro i hi
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    rw [Function.update_of_ne hij]
    exact mem_of_mem_nhds (hu i)
  exact hsub hy ⟨j, by simpa using ho⟩

/-- The counterexample event is dense. -/
theorem dense_cex [Infinite I] {bad : Set O} (hne : bad.Nonempty) :
    Dense (cex (I := I) bad) := by
  rw [dense_iff_closure_eq, ← compl_compl (closure _), ← interior_compl,
    interior_compl_cex hne, Set.compl_empty]

/-- The frontier of the counterexample event is the law itself. -/
theorem frontier_cex [Infinite I] {bad : Set O} (hbad : IsOpen bad) (hne : bad.Nonempty) :
    frontier (cex (I := I) bad) = (cex bad)ᶜ := by
  rw [frontier, (isOpen_cex hbad).interior_eq, (dense_cex hne).closure_eq, Set.compl_eq_univ_sdiff]

/-- The counterexample event as a verifiable proposition. -/
def cexOpens {bad : Set O} (hbad : IsOpen bad) : Opens (I → O) := ⟨cex bad, isOpen_cex hbad⟩

/-- **The intuitionistic law is `⊥`.** The pseudocomplement of the counterexample event, the
part of the law some finite observation verifies, is empty. -/
theorem compl_cexOpens [Infinite I] {bad : Set O} (hbad : IsOpen bad) (hne : bad.Nonempty) :
    (cexOpens (I := I) hbad)ᶜ = ⊥ := by
  apply SetLike.coe_injective
  rw [Opens.coe_compl_eq_interior_compl, Opens.coe_bot]
  exact interior_compl_cex hne

/-- Every valuation gives the law credence `0`. -/
theorem valuation_compl_cex [Infinite I] {bad : Set O} (hbad : IsOpen bad)
    (hne : bad.Nonempty) (v : Valuation (Opens (I → O))) :
    v (cexOpens hbad)ᶜ = 0 := by
  rw [compl_cexOpens hbad hne, v.map_bot]

/-- The slack at the counterexample event is everything a valuation does not give to it. -/
theorem slack_cex [Infinite I] {bad : Set O} (hbad : IsOpen bad) (hne : bad.Nonempty)
    (v : Valuation (Opens (I → O))) :
    v.slack (cexOpens hbad) = 1 - v (cexOpens hbad) := by
  rw [Valuation.slack, valuation_compl_cex hbad hne, add_zero]

/-- No verifiable evidence raises the credence in the law above `0`. -/
theorem condVal_compl_cex [Infinite I] {bad : Set O} (hbad : IsOpen bad) (hne : bad.Nonempty)
    (v : Valuation (Opens (I → O))) (e : Opens (I → O)) (he : v e ≠ 0) :
    v.condVal e he (cexOpens hbad)ᶜ = 0 :=
  valuation_compl_cex hbad hne _

section Measure

variable [MeasurableSpace (I → O)] [OpensMeasurableSpace (I → O)]

/-- **The classical credence in the law is slack.** -/
theorem classical_law_eq_slack [Infinite I] {bad : Set O} (hbad : IsOpen bad)
    (hne : bad.Nonempty) (μ : Measure (I → O)) [IsProbabilityMeasure μ] :
    μ (cex bad)ᶜ = μ.toValuationOpens.slack (cexOpens hbad) := by
  rw [toValuationOpens_slack_eq_frontier]
  exact congrArg μ (frontier_cex hbad hne).symm

/-- **The classical posterior of the law is all undecided mass.** Given verifiable evidence `e`,
the classical posterior of the law is the constructive posterior of its intuitionistic
counterpart, which is `0`, plus the conditional frontier mass of the counterexample event. -/
theorem classical_posterior_law [Infinite I] {bad : Set O} (hbad : IsOpen bad)
    (hne : bad.Nonempty) (μ : Measure (I → O)) [IsProbabilityMeasure μ] (e : Opens (I → O))
    (he : μ.toValuationOpens e ≠ 0) :
    μ.toValuationOpens.condVal e he (cexOpens hbad)ᶜ = 0 ∧
      μ ((cex bad)ᶜ ∩ e) / μ e = μ (frontier (cex (I := I) bad) ∩ e) / μ e := by
  refine ⟨condVal_compl_cex hbad hne _ e he, ?_⟩
  have := classical_posterior_compl_eq μ (cexOpens hbad) e he
  rwa [condVal_compl_cex hbad hne _ e he, zero_add] at this

omit [TopologicalSpace O] [MeasurableSpace (I → O)] [OpensMeasurableSpace (I → O)] in
/-- Splitting the counterexample event at object `j`. -/
theorem cex_inter_obs (bad A : Set O) (j : I) :
    cex bad ∩ obs j A
      = (cexExcept bad j ∩ obs j A) ∪ ((cexExcept bad j)ᶜ ∩ obs j (A ∩ bad)) := by
  ext x
  simp only [cex, cexExcept, obs, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
    Set.mem_setOf_eq, not_exists, not_and]
  constructor
  · rintro ⟨⟨i, hi⟩, hA⟩
    by_cases hij : i = j
    · subst hij
      by_cases h : ∃ k, k ≠ i ∧ x k ∈ bad
      · exact Or.inl ⟨h, hA⟩
      · push Not at h
        exact Or.inr ⟨fun k hk => (h k hk), hA, hi⟩
    · exact Or.inl ⟨⟨i, hij, hi⟩, hA⟩
  · rintro (⟨⟨i, -, hi⟩, hA⟩ | ⟨-, hA, hb⟩)
    · exact ⟨⟨i, hi⟩, hA⟩
    · exact ⟨⟨j, hb⟩, hA⟩

/-- **Selection and confirmation.** Suppose object `j` is known to have a kind in `A`, and the
kind of `j` is independent of whether some other object is a counterexample. Then the credence
in a counterexample given that selection is the credence that another object is one, plus the
conditional prior that `j` is the counterexample times the credence that no other object is. -/
theorem posterior_cex_select {bad A : Set O} (hbad : IsOpen bad) (hA : IsOpen A) (j : I)
    (μ : Measure (I → O)) [IsProbabilityMeasure μ] (hsel : μ (obs j A) ≠ 0)
    (hind : ∀ B ∈ ({A, A ∩ bad} : Set (Set O)),
      μ (cexExcept bad j ∩ obs j B) = μ (cexExcept bad j) * μ (obs j B)) :
    μ (cex bad ∩ obs j A) / μ (obs j A)
      = μ (cexExcept bad j)
        + μ (obs j (A ∩ bad)) / μ (obs j A) * μ (cexExcept bad j)ᶜ := by
  have hK : MeasurableSet (cexExcept bad j) := (isOpen_cexExcept hbad j).measurableSet
  have hE : ∀ {B : Set O}, IsOpen B → MeasurableSet (obs j B) :=
    fun hB => (isOpen_obs j hB).measurableSet
  have hAb : IsOpen (A ∩ bad) := hA.inter hbad
  -- independence passes to the complement of `cexExcept`
  have hindc : μ ((cexExcept bad j)ᶜ ∩ obs j (A ∩ bad))
      = μ (cexExcept bad j)ᶜ * μ (obs j (A ∩ bad)) := by
    have h1 := measure_inter_add_sdiff (obs j (A ∩ bad)) hK (μ := μ)
    rw [Set.inter_comm (obs j (A ∩ bad)), hind _ (by simp), Set.sdiff_eq_compl_inter] at h1
    have h2 : μ (obs j (A ∩ bad))
        = μ (cexExcept bad j) * μ (obs j (A ∩ bad))
          + μ (cexExcept bad j)ᶜ * μ (obs j (A ∩ bad)) := by
      rw [← add_mul, measure_add_measure_compl hK, measure_univ, one_mul]
    have hfin : μ (cexExcept bad j) * μ (obs j (A ∩ bad)) ≠ ∞ :=
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
    exact (ENNReal.add_right_inj hfin).1 (h1.trans h2)
  have hdisj : Disjoint (cexExcept bad j ∩ obs j A) ((cexExcept bad j)ᶜ ∩ obs j (A ∩ bad)) :=
    Set.disjoint_left.2 fun x hx hy => hy.1 hx.1
  rw [cex_inter_obs, measure_union hdisj (hK.compl.inter (hE hAb)), hind _ (by simp), hindc,
    ENNReal.add_div, ENNReal.mul_div_cancel_right hsel (measure_ne_top _ _), mul_comm,
    ENNReal.mul_div_right_comm]

end Measure

end Ravens

end ConstructiveProb
