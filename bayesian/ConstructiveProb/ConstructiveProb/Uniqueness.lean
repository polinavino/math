/-
# Uniqueness of the calculus

Criteria (1) and (2) do not single out `Mix S`: a convex set can have the same `{0,1}`-valued
elements and be strictly larger (the PCS `!Bool`). A third criterion does: every affine law that
holds on all certain states holds on the whole calculus, Boole's "conditions of possible
experience" relative to the logic. Any convex set containing the certain states and satisfying
these laws is `Mix S` (`calculus_unique`): convexity bounds it from below and the laws, by
completeness (`Mix_eq_laws'`), from above.
-/
import ConstructiveProb.Recipe

open scoped ENNReal

namespace ConstructiveProb

variable {E : Type*} [Fintype E]

/-- **Uniqueness of the calculus.** If `C` contains the certain states `S`, is closed under finite
mixtures, and satisfies every affine law valid on `S`, then `C = Mix S`. -/
theorem calculus_unique {S C : Set (E → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s) (hSC : S ⊆ C)
    (hconv : Mix C ⊆ C)
    (hlaws : ∀ L : AffineLaw E, (∀ s ∈ S, L.Holds s) → ∀ x ∈ C, L.Holds x) :
    C = Mix S := by
  apply le_antisymm
  · intro x hx
    rw [Mix_eq_laws' hS]
    exact fun L hL => hlaws L hL x hx
  · rintro x ⟨n, w, s, hs, hw, rfl⟩
    exact hconv ⟨n, w, s, fun i => hSC (hs i), hw, rfl⟩

/-- **The calculus obeys exactly the laws of the certain states.** A set containing the certain
states satisfies no affine law that some certain state violates, so it imposes no law the logic
does not have. The third criterion is the converse. -/
theorem calculus_laws_iff {S C : Set (E → ℝ≥0∞)} (hSC : S ⊆ C)
    (hlaws : ∀ L : AffineLaw E, (∀ s ∈ S, L.Holds s) → ∀ x ∈ C, L.Holds x) (L : AffineLaw E) :
    (∀ x ∈ C, L.Holds x) ↔ ∀ s ∈ S, L.Holds s :=
  ⟨fun h s hs => h s (hSC hs), hlaws L⟩

/-- The calculus `Mix S` itself satisfies the three conditions. -/
theorem calculus_conditions {S : Set (E → ℝ≥0∞)} :
    S ⊆ Mix S ∧ Mix (Mix S) ⊆ Mix S ∧
      ∀ L : AffineLaw E, (∀ s ∈ S, L.Holds s) → ∀ x ∈ Mix S, L.Holds x := by
  refine ⟨fun s hs => ?_, (Mix_Mix S).le, fun L hL x hx => L.holds_of_Mix hL hx⟩
  have := mem_Mix_of_fintype (S := S) (fun _ : Unit => (1 : ℝ≥0∞)) (fun _ => s) (fun _ => hs)
    (by simp)
  simpa using this

/-! ### Arbitrarily many events -/

section Infinite

variable {E : Type*}

/-- A state that is a mixture of certain states on every finite window is a limit of mixtures,
in the product topology. -/
theorem localMix_subset_closure {S : Set (E → ℝ≥0∞)} {x : E → ℝ≥0∞}
    (hx : ∀ F : Finset E, restr F x ∈ Mix (restr F '' S)) : x ∈ closure (Mix S) := by
  classical
  rw [mem_closure_iff_nhds]
  intro t ht
  rw [nhds_pi, Filter.mem_pi] at ht
  obtain ⟨I, hI, u, hu, hsub⟩ := ht
  obtain ⟨n, w, s', hs', hw, heq⟩ := hx hI.toFinset
  have hs'' : ∀ i, ∃ a, a ∈ S ∧ restr hI.toFinset a = s' i := fun i => hs' i
  choose s hs hss using hs''
  refine ⟨∑ i, w i • s i, hsub (Set.mem_pi.2 fun e he => ?_), ⟨n, w, s, hs, hw, rfl⟩⟩
  have hmem : e ∈ hI.toFinset := hI.mem_toFinset.2 he
  have hxe : x e = (∑ i, w i • s i) e := by
    have h1 := congrFun heq ⟨e, hmem⟩
    simp only [restr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hss i]
    rfl
  rw [← hxe]
  exact mem_of_mem_nhds (hu e)

/-- **Uniqueness for arbitrarily many events.** If `C` contains the certain states, is closed
under finite mixtures and in the product topology, and satisfies every finitely supported affine
law valid on the certain states, then `C` is the closure of `Mix S`, which is also the set of all
functions satisfying those laws. -/
theorem calculus_unique_closed {S C : Set (E → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s)
    (hSC : S ⊆ C) (hconv : Mix C ⊆ C) (hclosed : IsClosed C)
    (hlaws : ∀ L : FinLaw E, (∀ s ∈ S, L.Holds s) → ∀ x ∈ C, L.Holds x) :
    C = closure (Mix S) ∧
      C = {x | ∀ L : FinLaw E, (∀ s ∈ S, L.Holds s) → L.Holds x} := by
  have hMC : Mix S ⊆ C := by
    rintro x ⟨n, w, s, hs, hw, rfl⟩
    exact hconv ⟨n, w, s, fun i => hSC (hs i), hw, rfl⟩
  have h1 : closure (Mix S) ⊆ C := closure_minimal hMC hclosed
  have h2 : C ⊆ {x | ∀ L : FinLaw E, (∀ s ∈ S, L.Holds s) → L.Holds x} :=
    fun x hx L hL => hlaws L hL x hx
  have h3 : {x | ∀ L : FinLaw E, (∀ s ∈ S, L.Holds s) → L.Holds x} ⊆ closure (Mix S) :=
    fun x hx => localMix_subset_closure ((laws_iff_local_Mix hS x).1 hx)
  exact ⟨le_antisymm (h2.trans h3) h1, le_antisymm h2 (h3.trans h1)⟩

end Infinite

end ConstructiveProb
