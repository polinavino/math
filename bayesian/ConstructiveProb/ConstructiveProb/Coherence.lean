/-
# The certain states are Girard's coherence spaces

Coherence spaces (Girard) are the qualitative model of linear logic: a web with a reflexive,
symmetric coherence relation, and the points of a type are its *cliques*. Here the constructions
are written out on webs (`flatC`, `dualC`, `tensC`, `arrowC`), and the certain (`{0,1}`-valued)
elements of the probabilistic coherence spaces used so far are shown to be exactly the cliques of
the corresponding coherence spaces:

* `sharp_lin_iff_clique`: first order, `flat X ⊸ flat Y`;
* `sharp_tensDual_iff_clique`: second order, `((Bool ⊸ Bool) ⊗ (Bool ⊸ Bool))^⊥`.

So at these types the recipe's calculus is "mixtures of cliques of the coherence space": equal to
the probabilistic coherence space at first order, strictly smaller at second order.
-/
import ConstructiveProb.Recipe

open scoped ENNReal
open Finset

namespace ConstructiveProb.PCS

/-- Coherence (reflexive, `≍`) of a flat space: only equal points cohere. -/
def flatC (X : Type*) : X → X → Prop := fun x y => x = y

/-- Linear negation: `x ≍ y` in `A^⊥` iff `x = y` or `x ≭ y` in `A`. -/
def dualC {X : Type*} (c : X → X → Prop) : X → X → Prop := fun x y => x = y ∨ ¬ c x y

/-- Tensor: componentwise coherence. -/
def tensC {X Y : Type*} (c : X → X → Prop) (d : Y → Y → Prop) : X × Y → X × Y → Prop :=
  fun p q => c p.1 q.1 ∧ d p.2 q.2

/-- Linear implication `A ⊸ B = (A ⊗ B^⊥)^⊥`. -/
def arrowC {X Y : Type*} (c : X → X → Prop) (d : Y → Y → Prop) : X × Y → X × Y → Prop :=
  dualC (tensC c (dualC d))

/-- A clique: pairwise coherent. -/
def IsClique {X : Type*} (c : X → X → Prop) (B : X → Prop) : Prop := ∀ x y, B x → B y → c x y

/-- In `flat X ⊸ flat Y`, two points cohere iff they are equal or have different inputs. -/
theorem arrowC_flat {X Y : Type*} (p q : X × Y) :
    arrowC (flatC X) (flatC Y) p q ↔ p = q ∨ p.1 ≠ q.1 := by
  simp only [arrowC, dualC, tensC, flatC]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr fun h1 => h ⟨h1, by tauto⟩
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr fun h1 => h h1.1

/-- The coherence of `Bool ⊸ Bool` is `compat`. -/
theorem arrowC_bool (p q : W) : arrowC (flatC Bool) (flatC Bool) p q ↔ compat p q :=
  arrowC_flat p q

/-- The coherence of `((Bool ⊸ Bool) ⊗ (Bool ⊸ Bool))^⊥`. -/
def secondC : W × W → W × W → Prop :=
  dualC (tensC (arrowC (flatC Bool) (flatC Bool)) (arrowC (flatC Bool) (flatC Bool)))

theorem secondC_iff (s t : W × W) : secondC s t ↔ s = t ∨ ¬ compat2 s t := by
  simp only [secondC, dualC, tensC, arrowC_bool, compat2]

theorem sum_sharp_le_one {ι : Type*} {s : Finset ι} {z : ι → ℝ≥0∞}
    (h01 : ∀ i, z i = 0 ∨ z i = 1) (h : ∀ i ∈ s, ∀ j ∈ s, z i = 1 → z j = 1 → i = j) :
    ∑ i ∈ s, z i ≤ 1 := by
  classical
  have : ∑ i ∈ s, z i = ((s.filter (z · = 1)).card : ℝ≥0∞) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases h01 i with h' | h' <;> simp [h']
  rw [this]
  have hc : (s.filter (z · = 1)).card ≤ 1 := Finset.card_le_one.2 fun i hi j hj => by
    simp only [Finset.mem_filter] at hi hj; exact h i hi.1 j hj.1 hi.2 hj.2
  exact_mod_cast hc

/-- **First order.** A `{0,1}`-valued `t` is an element of `flat X ⊸ flat Y` iff its support is a
clique of the coherence space `flat X ⊸ flat Y`. -/
theorem sharp_lin_iff_clique {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {t : X × Y → ℝ≥0∞} (h01 : ∀ p, t p = 0 ∨ t p = 1) :
    t ∈ lin X Y ↔ IsClique (arrowC (flatC X) (flatC Y)) (t · = 1) := by
  rw [mem_lin_iff]
  constructor
  · intro h p q hp hq
    rw [arrowC_flat]
    by_cases hpq : p.1 = q.1
    · left
      by_contra hne
      have hb : p.2 ≠ q.2 := fun hb => hne (Prod.ext hpq hb)
      have := h p.1
      have h2 : t (p.1, p.2) + t (p.1, q.2) ≤ ∑ b, t (p.1, b) := by
        rw [← Finset.sum_pair (f := fun b => t (p.1, b)) hb]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [show (p.1, p.2) = p from rfl, show (p.1, q.2) = q from Prod.ext hpq rfl, hp, hq] at h2
      have := h2.trans this; norm_num at this
    · exact Or.inr hpq
  · intro h a
    refine sum_sharp_le_one (fun b => h01 (a, b)) fun b _ b' _ hb hb' => ?_
    rcases (arrowC_flat _ _).1 (h _ _ hb hb') with h' | h'
    · exact (Prod.ext_iff.1 h').2
    · exact absurd rfl h'

/-- **Second order.** A `{0,1}`-valued `z` is an element of the PCS
`((Bool ⊸ Bool) ⊗ (Bool ⊸ Bool))^⊥` iff its support is a clique of the coherence space of the
same type. -/
theorem sharp_tensDual_iff_clique {z : W × W → ℝ≥0∞} (h01 : ∀ pq, z pq = 0 ∨ z pq = 1) :
    z ∈ tensDual ↔ IsClique secondC (z · = 1) := by
  constructor
  · intro hz s t hs ht
    rw [secondC_iff]
    by_cases hst : s = t
    · exact Or.inl hst
    · exact Or.inr (sharp_excl hz hs ht hst)
  · intro h
    refine mem_tensDual_of_det _ fun f g => ?_
    rw [pair_det]
    refine sum_sharp_le_one h01 fun s hs t ht hzs hzt => ?_
    rcases (secondC_iff s t).1 (h s t hzs hzt) with h' | h'
    · exact h'
    · exact absurd (compat2_of_covers (Finset.mem_filter.1 hs).2 (Finset.mem_filter.1 ht).2) h'

/-! ### The PCS is the clique relaxation, the recipe is the stable-set polytope

Call two web points of `((Bool ⊸ Bool) ⊗ (Bool ⊸ Bool))^⊥` *exclusive* when they are distinct and
`compat2` (some deterministic pair covers both). The PCS is exactly `QSTAB`: total weight at most
`1` on every set of pairwise-compatible points. Its certain elements are the indicators of
pairwise-exclusive-free sets (`sharp_tensDual_iff_clique`), so the recipe is `STAB`. The gap is
the gap between `QSTAB` and `STAB` of this graph, which contains the pentagon. -/

/-- A deterministic program through every point of a pairwise-compatible family. -/
noncomputable def throughAll (C : Finset W) : Bool → Option Bool := fun a =>
  if h : ∃ p ∈ C, p.1 = a then some (Classical.choose h).2 else none

theorem throughAll_spec {C : Finset W} (hC : ∀ p ∈ C, ∀ q ∈ C, compat p q) {p : W}
    (hp : p ∈ C) : throughAll C p.1 = some p.2 := by
  have hex : ∃ q ∈ C, q.1 = p.1 := ⟨p, hp, rfl⟩
  simp only [throughAll, dif_pos hex]
  obtain ⟨hq, hq1⟩ := Classical.choose_spec hex
  rcases hC _ hq p hp with h | h
  · rw [h]
  · exact absurd hq1 h

/-- **Every pairwise-compatible set is covered by one deterministic pair.** -/
theorem covers_of_pairwise {C : Finset (W × W)} (hC : ∀ s ∈ C, ∀ t ∈ C, compat2 s t) :
    ∃ f g : Bool → Option Bool, ∀ s ∈ C, covers f g s := by
  classical
  refine ⟨throughAll (C.image Prod.fst), throughAll (C.image Prod.snd), fun s hs => ⟨?_, ?_⟩⟩
  · refine throughAll_spec ?_ (Finset.mem_image_of_mem _ hs)
    intro p hp q hq
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hq
    exact (hC _ hs' _ ht').1
  · refine throughAll_spec ?_ (Finset.mem_image_of_mem _ hs)
    intro p hp q hq
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hq
    exact (hC _ hs' _ ht').2

/-- **The PCS is `QSTAB` of the exclusivity graph.** -/
theorem tensDual_iff_qstab (t : W × W → ℝ≥0∞) :
    t ∈ tensDual ↔ ∀ C : Finset (W × W), (∀ s ∈ C, ∀ u ∈ C, compat2 s u) → ∑ s ∈ C, t s ≤ 1 := by
  constructor
  · intro ht C hC
    obtain ⟨f, g, hfg⟩ := covers_of_pairwise hC
    have h1 := ht _ (det_mem_lin f) _ (det_mem_lin g)
    rw [pair_det] at h1
    refine le_trans (Finset.sum_le_sum_of_subset fun s hs => ?_) h1
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hfg s hs⟩
  · intro h
    refine mem_tensDual_of_det _ fun f g => ?_
    rw [pair_det]
    exact h _ fun s hs u hu =>
      compat2_of_covers (Finset.mem_filter.1 hs).2 (Finset.mem_filter.1 hu).2

/-- **The recipe is `STAB`.** The recipe's calculus is the set of mixtures of indicators of
sets containing no exclusive pair. -/
theorem recipe_eq_stab :
    Mix {z | z ∈ tensDual ∧ ∀ pq, z pq = 0 ∨ z pq = 1}
      = Mix {z | (∀ pq, z pq = 0 ∨ z pq = 1) ∧ IsClique secondC (z · = 1)} := by
  congr 1
  ext z
  exact ⟨fun ⟨hz, h01⟩ => ⟨h01, (sharp_tensDual_iff_clique h01).1 hz⟩,
    fun ⟨h01, hc⟩ => ⟨(sharp_tensDual_iff_clique h01).2 hc, h01⟩⟩

end ConstructiveProb.PCS
