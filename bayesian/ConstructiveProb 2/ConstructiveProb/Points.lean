/-
# Completely prime points and the valuation functor

Companion to `Basic.lean`. Two upgrades promised in prose by the paper draft and left
unformalized there:

1. **The Scott refinement of `sharp_iff_point`.** `sharp_iff_point` identifies the sharp
   (`{0,1}`-valued) valuations with the complement-indicators of *prime* ideals — the
   *finitely* prime points. The paper remarks that the **completely prime** points (the
   points of the locale in the standard, spatial sense) "would correspond to sharp
   valuations that are also Scott-continuous, a refinement we note but do not formalize."
   Here it is formalized: `sharp_scott_iff_completelyPrimePoint`. A sharp valuation is
   Scott-continuous iff its zero-set ideal is closed under arbitrary suprema of its
   subsets, i.e. iff its complement filter is completely prime.

2. **The functor part of `Val`.** The conclusion of the paper states that pushforward
   along frame homomorphisms preserves all four valuation axioms, "a routine verification
   that we state but have not mechanized." Mechanized here: `Valuation.comap` with the
   functor laws `comap_id` and `comap_comp`. In locale terms a frame homomorphism
   `f : Γ → Ω` is a continuous map of locales `pt Ω → pt Γ`, and `comap f` is the
   pushforward of valuations along that map, so `Val(−)` is a functor on locales.

3. **Birkhoff transport.** The finite representation theorem (`Representation.lean`) is
   stated on `LowerSet P`; the reduction of an abstract finite frame to `LowerSet P` was
   cited (Birkhoff duality) rather than mechanized. mathlib now has the duality
   (`OrderIso.lowerSetSupIrred`), so the citation can be discharged: transporting a
   valuation along the isomorphism (`Valuation.mapEquiv`) turns `eq_sum_mass`/`sum_mass`
   into `eq_sum_birkhoffMass`/`sum_birkhoffMass` — *every* valuation on *any* finite frame
   is a probability mass function on its sup-irreducible elements, with no lower-set
   presentation assumed.
-/
import ConstructiveProb.Basic
import ConstructiveProb.Representation
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.Birkhoff

open scoped ENNReal BigOperators

namespace ConstructiveProb

variable {Ω : Type*} [Order.Frame Ω]

/-! ### Valuations are determined by their values -/

namespace Valuation

/-- Finite sub-additivity, the inequality half of modularity: dropping the meet term can
only lose mass. -/
theorem sup_le_add (v : Valuation Ω) (a b : Ω) : v (a ⊔ b) ≤ v a + v b :=
  (v.modular a b).symm.le.trans' le_self_add

/-! ### Scott continuity -/

/-- A valuation is **Scott-continuous** when it sends directed suprema to suprema of
values. This is the continuity axiom the localic-valuation literature builds in and the
present development deliberately omits; here it is a property a valuation may or may not
have (`topIndicator`, in `RepresentationInfinite.lean`, does not). -/
def ScottContinuous (v : Valuation Ω) : Prop :=
  ∀ S : Set Ω, S.Nonempty → DirectedOn (· ≤ ·) S → v (sSup S) = ⨆ a ∈ S, v a

/-- A Scott-continuous valuation vanishes on the supremum of *any* family it vanishes on
(no directedness assumed): close the family under finite joins, where sub-additivity keeps
the value at zero, and let Scott continuity pass to the limit. This says exactly that the
zero-set ideal of a Scott-continuous valuation is closed under arbitrary suprema. -/
theorem sSup_eq_zero_of_scott (v : Valuation Ω) (hv : v.ScottContinuous)
    {S : Set Ω} (hS : ∀ x ∈ S, v x = 0) : v (sSup S) = 0 := by
  classical
  set D : Set Ω := (fun F : Finset Ω => F.sup id) '' {F : Finset Ω | ↑F ⊆ S} with hD
  have hDne : D.Nonempty := ⟨⊥, ∅, by simp, by simp⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨F₁, hF₁, rfl⟩ _ ⟨F₂, hF₂, rfl⟩
    exact ⟨(F₁ ∪ F₂).sup id,
      ⟨F₁ ∪ F₂, by
        simp only [Set.mem_setOf_eq, Finset.coe_union, Set.union_subset_iff]
        exact ⟨hF₁, hF₂⟩, rfl⟩,
      Finset.sup_mono Finset.subset_union_left,
      Finset.sup_mono Finset.subset_union_right⟩
  have hDsup : sSup D = sSup S := by
    refine le_antisymm (sSup_le ?_) (sSup_le fun x hx => ?_)
    · rintro _ ⟨F, hF, rfl⟩
      exact Finset.sup_le fun x hx => le_sSup (hF hx)
    · refine le_sSup_of_le ⟨{x}, ?_, rfl⟩ (by simp)
      simp only [Set.mem_setOf_eq, Finset.coe_singleton, Set.singleton_subset_iff]
      exact hx
  have hzero : ∀ F : Finset Ω, ↑F ⊆ S → v (F.sup id) = 0 := by
    intro F
    induction F using Finset.cons_induction with
    | empty => intro _; simp
    | cons a F ha IH =>
      intro hsub
      rw [Finset.coe_cons, Set.insert_subset_iff] at hsub
      rw [Finset.sup_cons]
      refine le_antisymm ?_ zero_le
      calc v (id a ⊔ F.sup id) ≤ v (id a) + v (F.sup id) := v.sup_le_add _ _
      _ = 0 := by rw [id, hS a hsub.1, IH hsub.2, add_zero]
  rw [← hDsup, hv D hDne hdir]
  refine le_antisymm (iSup₂_le ?_) zero_le
  rintro _ ⟨F, hF, rfl⟩
  exact (hzero F hF).le

end Valuation

/-! ### Completely prime ideals: the points of the locale -/

/-- An ideal is **completely prime** when it is prime and closed under arbitrary suprema
of its subsets. Its complement is then a completely prime filter — a *point* of the locale
in the standard, spatial sense, refining the finitely prime points of `sharp_iff_point`. -/
def Ideal.IsCompletelyPrime (J : Order.Ideal Ω) : Prop :=
  J.IsPrime ∧ ∀ S : Set Ω, (∀ x ∈ S, x ∈ J) → sSup S ∈ J

/-- The complement-indicator of a completely prime ideal is Scott-continuous. Together with
`Ideal.toValuation_isSharp` this is the easy half of the correspondence between completely
prime points and sharp Scott-continuous valuations. -/
theorem Ideal.toValuation_scottContinuous (J : Order.Ideal Ω) (hJ : Ideal.IsCompletelyPrime J)
    (htop : ⊤ ∉ J) : (Ideal.toValuation J hJ.1 htop).ScottContinuous := by
  intro S hne hdir
  by_cases hsup : sSup S ∈ J
  · have hall : ∀ a ∈ S, a ∈ J := fun a ha => J.lower (le_sSup ha) hsup
    rw [Ideal.toValuation_apply, if_pos hsup]
    refine (iSup₂_le fun a ha => ?_).antisymm' zero_le
    rw [Ideal.toValuation_apply, if_pos (hall a ha)]
  · obtain ⟨a, ha, haJ⟩ : ∃ a ∈ S, a ∉ J := by
      by_contra hc
      exact hsup (hJ.2 S fun x hx => not_not.mp fun hxJ => hc ⟨x, hx, hxJ⟩)
    rw [Ideal.toValuation_apply, if_neg hsup]
    refine le_antisymm (le_iSup₂_of_le a ha ?_) (iSup₂_le fun b _ => Valuation.le_one _ b)
    rw [Ideal.toValuation_apply, if_neg haJ]

/-- **Scott continuity of a sharp valuation is complete primeness of its zero-set.** The
finitely prime half (`zeroIdeal_isPrime`) needs only sharpness; the completely prime
surplus is exactly Scott continuity. -/
theorem Valuation.scottContinuous_iff_zeroIdeal_completelyPrime (v : Valuation Ω)
    (hv : v.IsSharp) :
    v.ScottContinuous ↔ Ideal.IsCompletelyPrime v.zeroIdeal := by
  constructor
  · intro hsc
    exact ⟨v.zeroIdeal_isPrime hv, fun S hS => v.sSup_eq_zero_of_scott hsc hS⟩
  · intro hcp S hne hdir
    rcases hv (sSup S) with h0 | h1
    · rw [h0]
      refine ((iSup₂_le fun a ha => ?_).antisymm zero_le).symm
      exact (v.mono (le_sSup ha)).trans h0.le
    · rw [h1]
      obtain ⟨a, ha, hva⟩ : ∃ a ∈ S, v a = 1 := by
        by_contra hc
        have hall : ∀ x ∈ S, v x = 0 := fun x hx =>
          (hv x).resolve_right fun h1x => hc ⟨x, hx, h1x⟩
        exact one_ne_zero (h1.symm.trans (hcp.2 S hall))
      exact le_antisymm (le_iSup₂_of_le a ha hva.ge) (iSup₂_le fun b _ => v.le_one b)

/-- **Sharp Scott-continuous valuations are the completely prime points (proved).** The
refinement of `sharp_iff_point` the paper had noted without formalizing: the certainty
limit of the probability theory recovers the finitely prime points, and imposing Scott
continuity cuts those down to the completely prime ones, the points of the locale in the
spatial sense. -/
theorem sharp_scott_iff_completelyPrimePoint (v : Valuation Ω) :
    v.IsSharp ∧ v.ScottContinuous ↔
      ∃ (J : Order.Ideal Ω) (hJ : Ideal.IsCompletelyPrime J) (htop : ⊤ ∉ J),
        v = Ideal.toValuation J hJ.1 htop := by
  constructor
  · rintro ⟨hv, hsc⟩
    exact ⟨v.zeroIdeal, (v.scottContinuous_iff_zeroIdeal_completelyPrime hv).mp hsc,
      v.zeroIdeal_top_not_mem, (v.toValuation_zeroIdeal hv).symm⟩
  · rintro ⟨J, hJ, htop, rfl⟩
    exact ⟨Ideal.toValuation_isSharp J hJ.1 htop, Ideal.toValuation_scottContinuous J hJ htop⟩

/-! ### The functor part of `Val` -/

namespace Valuation

variable {Γ Δ : Type*} [Order.Frame Γ] [Order.Frame Δ]

/-- Composition with a frame homomorphism preserves all four valuation axioms. In locale
terms `f : FrameHom Γ Ω` is a continuous map `pt Ω → pt Γ`, and `v.comap f` is the
**pushforward** of `v` along it, so `Val(−)` is a functor on locales. Monotonicity and
modularity are inherited because `f` preserves `⊥`, `⊤`, `⊔`, `⊓`. -/
def comap (f : FrameHom Γ Ω) (v : Valuation Ω) : Valuation Γ where
  toFun a := v (f a)
  map_bot' := by simp
  map_top' := by simp
  mono' _ _ h := v.mono (OrderHomClass.mono f h)
  modular' a b := by
    simpa only [map_sup, map_inf] using v.modular (f a) (f b)

@[simp] theorem comap_apply (f : FrameHom Γ Ω) (v : Valuation Ω) (a : Γ) :
    v.comap f a = v (f a) := rfl

@[simp] theorem comap_id (v : Valuation Ω) : v.comap (FrameHom.id Ω) = v :=
  Valuation.ext (funext fun _ => rfl)

theorem comap_comp (f : FrameHom Γ Ω) (g : FrameHom Δ Γ) (v : Valuation Ω) :
    v.comap (f.comp g) = (v.comap f).comap g :=
  Valuation.ext (funext fun _ => rfl)

/-- Transport of a valuation along an order isomorphism of frames (an order isomorphism
between complete lattices preserves all the structure a valuation sees). -/
def mapEquiv (e : Ω ≃o Γ) (v : Valuation Ω) : Valuation Γ where
  toFun b := v (e.symm b)
  map_bot' := by rw [OrderIso.map_bot, v.map_bot]
  map_top' := by rw [OrderIso.map_top, v.map_top]
  mono' _ _ h := v.mono (e.symm.monotone h)
  modular' a b := by
    simpa only [map_sup, map_inf] using v.modular (e.symm a) (e.symm b)

@[simp] theorem mapEquiv_apply (e : Ω ≃o Γ) (v : Valuation Ω) (b : Γ) :
    v.mapEquiv e b = v (e.symm b) := rfl

@[simp] theorem mapEquiv_apply_map (e : Ω ≃o Γ) (v : Valuation Ω) (a : Ω) :
    v.mapEquiv e (e a) = v a := by rw [mapEquiv_apply, e.symm_apply_apply]

end Valuation

/-! ### Birkhoff transport: the finite representation on abstract finite frames

`Representation.lean` proves `eq_sum_mass`/`sum_mass` on `LowerSet P` and cites Birkhoff
duality for the reduction of an arbitrary finite frame to that shape. mathlib's
`OrderIso.lowerSetSupIrred` is that duality, so the citation can now be discharged: the
mass function lives on the sup-irreducible elements, and every valuation on a finite frame
is its point-measure. -/

section Birkhoff

universe u

/-- **Representation along any lower-set presentation.** If a frame is presented as the
lower sets of a finite poset `P` by an order isomorphism, every valuation on it is the
point-measure of the transported mass function. This is `eq_sum_mass` freed from the
requirement that the frame *be* `LowerSet P` on the nose. -/
theorem Valuation.eq_sum_mass_of_orderIso {P : Type*} [PartialOrder P] [Fintype P]
    [DecidableEq P] (e : Ω ≃o LowerSet P) (v : Valuation Ω) (a : Ω) :
    v a = ∑ p ∈ (e a).toFinset, (v.mapEquiv e).mass p := by
  have h := (v.mapEquiv e).eq_sum_mass (e a)
  rwa [v.mapEquiv_apply_map] at h

/-- The transported mass along any lower-set presentation is a probability. -/
theorem Valuation.sum_mass_of_orderIso {P : Type*} [PartialOrder P] [Fintype P]
    [DecidableEq P] (e : Ω ≃o LowerSet P) (v : Valuation Ω) :
    ∑ p, (v.mapEquiv e).mass p = 1 :=
  (v.mapEquiv e).sum_mass

set_option maxHeartbeats 1000000 in
-- unifying the statement's instance stack on `{a : Ω // SupIrred a}` with the one in
-- `OrderIso.lowerSetSupIrred`'s signature unfolds `DistribLattice.ofInfSupLe`
/-- **Birkhoff duality, packaged.** Every finite frame is the lower-set lattice of a
finite poset, namely its sup-irreducible elements (mathlib's
`OrderIso.lowerSetSupIrred`). This is the duality the paper cited informally; stating it
with the poset existentially quantified lets the representation theorems below apply to
an abstract finite frame without ever re-elaborating the sup-irreducible subtype. -/
theorem exists_lowerSet_presentation (Ω : Type u) [Order.Frame Ω] [Finite Ω] :
    ∃ (P : Type u) (_ : PartialOrder P) (_ : Fintype P) (_ : DecidableEq P),
      Nonempty (Ω ≃o LowerSet P) := by
  classical
  cases nonempty_fintype Ω
  exact ⟨{a : Ω // SupIrred a}, inferInstance, inferInstance,
    fun _ _ => Classical.propDecidable _, ⟨OrderIso.lowerSetSupIrred⟩⟩

set_option maxHeartbeats 1000000 in
-- composing the presentation with the transport lemmas re-checks the presentation's
-- instance stack once more
/-- **Finite representation, on an abstract finite frame (proved).** Some finite poset
presents `Ω` as its lower sets, and along that presentation every valuation is a
classical probability mass function on the points: `eq_sum_mass`/`sum_mass` with the
lower-set presentation hypothesis discharged by Birkhoff duality rather than cited. -/
theorem Valuation.exists_pmf_presentation {Θ : Type u} [Order.Frame Θ] [Finite Θ]
    (v : Valuation Θ) :
    ∃ (P : Type u) (_ : PartialOrder P) (_ : Fintype P) (_ : DecidableEq P)
      (e : Θ ≃o LowerSet P),
      (∀ a, v a = ∑ p ∈ (e a).toFinset, (v.mapEquiv e).mass p) ∧
        ∑ p, (v.mapEquiv e).mass p = 1 := by
  obtain ⟨P, _, _, _, ⟨e⟩⟩ := exists_lowerSet_presentation Θ
  exact ⟨P, ‹_›, ‹_›, ‹_›, e, fun a => v.eq_sum_mass_of_orderIso e a,
    v.sum_mass_of_orderIso e⟩

end Birkhoff

end ConstructiveProb
