import ConstructiveProb.Basic

open scoped ENNReal
open MeasureTheory TopologicalSpace

namespace ConstructiveProb

section Overconfidence

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- The Boolean complement of an open splits into its verifiable part (the Heyting
complement `interior aᶜ`) and the frontier. -/
theorem compl_eq_interior_union_frontier (a : Opens X) :
    (a : Set X)ᶜ = interior (a : Set X)ᶜ ∪ frontier (a : Set X) := by
  rw [a.isOpen.frontier_eq, interior_compl]
  ext x
  by_cases hc : x ∈ closure (a : Set X) <;> by_cases ha : x ∈ (a : Set X) <;>
    first | exact absurd (subset_closure ha) hc | simp [hc, ha]

/-- **Classical overconfidence in refutation, joint form.** Given evidence `b`, the classical
mass on the Boolean refutation `aᶜ ∩ b` exceeds the verifiable mass `v (aᶜ ⊓ b)` by exactly
the frontier mass `μ (∂a ∩ b)`. The confirmation side agrees: `v (a ⊓ b) = μ (a ∩ b)`. -/
theorem classical_compl_inter_eq (μ : Measure X) [IsProbabilityMeasure μ] (a b : Opens X) :
    μ ((a : Set X)ᶜ ∩ b) = μ.toValuationOpens (aᶜ ⊓ b) + μ (frontier (a : Set X) ∩ b) := by
  have hdisj : Disjoint (interior (a : Set X)ᶜ ∩ b) (frontier (a : Set X) ∩ b) := by
    refine Disjoint.mono Set.inter_subset_left Set.inter_subset_left ?_
    rw [← frontier_compl]
    exact disjoint_interior_frontier
  rw [Measure.toValuationOpens_apply, Opens.coe_inf, Opens.coe_compl_eq_interior_compl,
    ← measure_union hdisj (isClosed_frontier.measurableSet.inter b.isOpen.measurableSet),
    ← Set.union_inter_distrib_right, ← compl_eq_interior_union_frontier]

/-- **Classical overconfidence in refutation, posterior form.** Conditioning on evidence `b`,
the classical posterior of the refutation `aᶜ` is the constructive posterior of `¬a` plus the
conditional frontier mass `μ (∂a ∩ b) / μ b`: the mass that the evidence leaves neither
confirmed nor refuted, which the classical posterior credits wholly to refutation. -/
theorem classical_posterior_compl_eq (μ : Measure X) [IsProbabilityMeasure μ] (a b : Opens X)
    (hb : μ.toValuationOpens b ≠ 0) :
    μ ((a : Set X)ᶜ ∩ b) / μ b
      = μ.toValuationOpens.condVal b hb aᶜ + μ (frontier (a : Set X) ∩ b) / μ b := by
  change μ ((a : Set X)ᶜ ∩ b) / μ b
    = μ ((aᶜ ⊓ b : Opens X) : Set X) / μ b + μ (frontier (a : Set X) ∩ b) / μ b
  rw [← ENNReal.add_div, classical_compl_inter_eq, Measure.toValuationOpens_apply]

/-- On the confirmation side the classical and constructive posteriors coincide. -/
theorem classical_posterior_eq (μ : Measure X) [IsProbabilityMeasure μ] (a b : Opens X)
    (hb : μ.toValuationOpens b ≠ 0) :
    μ ((a : Set X) ∩ b) / μ b = μ.toValuationOpens.condVal b hb a := by
  change _ = μ ((a ⊓ b : Opens X) : Set X) / μ b
  rw [Opens.coe_inf]

end Overconfidence

end ConstructiveProb
