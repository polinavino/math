import ConstructiveProb.Basic
import Mathlib.Topology.ExtremallyDisconnected

/-!
# Weak excluded middle as a global frame condition, and its topological instance

`slack_eq_dnGap_add_deMorganGap` (`Basic.lean`) splits slack into two *pointwise* independent
obstructions. This file asks what happens if one obstruction is killed *everywhere at once*,
without going all the way to classical logic.

**Global weak excluded middle** (`Order.Frame.IsDeMorgan`): `∀ a, aᶜᶜ ⊔ aᶜ = ⊤`. This is strictly
between plain intuitionistic logic and Boolean logic: it says nothing about `a ⊔ aᶜ` itself, only
about the regularized pair `(aᶜᶜ, aᶜ)`. Under it, `deMorganGap` vanishes identically and slack
collapses to the single remaining obstruction, `dnGap`.

For the motivating model `Ω = Opens X`, this is not an abstract fencepost: `IsDeMorgan (Opens X)`
is *equivalent* to `X` being **extremally disconnected** (closure of every open is open) — the
class of Stonean spaces, e.g. Stone–Čech remainders and Stone spaces of complete Boolean algebras.
This is a parallel development to the paper's main line (which stays fully constructive): a
concrete, well-studied intermediate regime, not needed for any other result. -/

noncomputable section

namespace Order.Frame

/-- A frame satisfies **weak excluded middle** (equivalently, the **De Morgan law**) if the
regularized pair `(aᶜᶜ, aᶜ)` is a partition of `⊤`, not merely disjoint, at every element. -/
def IsDeMorgan (Ω : Type*) [Order.Frame Ω] : Prop := ∀ a : Ω, aᶜᶜ ⊔ aᶜ = ⊤

end Order.Frame

open ConstructiveProb

variable {Ω : Type*} [Order.Frame Ω]

/-- **Under global weak excluded middle, slack is pure double-negation instability.** The De
Morgan gap vanishes for every valuation and every element, so `slack a = dnGap a` throughout —
the intermediate regime between plain intuitionistic logic (both gaps can be positive) and
classical logic (both gaps vanish, `Classical.classical_slack_zero`). -/
theorem ConstructiveProb.Valuation.slack_eq_dnGap_of_isDeMorgan
    (hΩ : Order.Frame.IsDeMorgan Ω) (v : Valuation Ω) (a : Ω) :
    v.slack a = v.dnGap a := by
  rw [v.slack_eq_dnGap_add_deMorganGap, v.deMorganGap_eq_zero_of_sup_eq_top (hΩ a), add_zero]

section Topology
open TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- The Heyting complement of an open, as a set, is the complement of its *closure* — the same
fact as `Opens.coe_compl_eq_interior_compl` composed with `interior_compl`, stated in the form
this section needs. -/
theorem Opens.coe_compl_eq_compl_closure (U : Opens X) :
    ↑(Uᶜ) = (closure (U : Set X))ᶜ := by
  rw [Opens.coe_compl_eq_interior_compl, interior_compl]

/-- The double complement of an open, as a set, is the interior of its closure. -/
theorem Opens.coe_compl_compl_eq_interior_closure (U : Opens X) :
    ↑(Uᶜᶜ) = interior (closure (U : Set X)) := by
  rw [Opens.coe_compl_eq_interior_compl, Opens.coe_compl_eq_compl_closure, compl_compl]

/-- **De Morgan frames of opens are exactly extremally disconnected spaces.** Weak excluded
middle for every open `U` says every point of `X` is either in the interior of `closure U` or
outside `closure U` entirely; that forces `closure U` to already be open, and conversely. -/
theorem isDeMorgan_opens_iff_extremallyDisconnected :
    Order.Frame.IsDeMorgan (Opens X) ↔ ExtremallyDisconnected X := by
  constructor
  · intro h
    refine ⟨fun S hS => ?_⟩
    have hU : (⟨S, hS⟩ : Opens X)ᶜᶜ ⊔ (⟨S, hS⟩ : Opens X)ᶜ = (⊤ : Opens X) :=
      h ⟨S, hS⟩
    have hcoe : interior (closure S) ∪ (closure S)ᶜ = (Set.univ : Set X) := by
      have h1 : ↑((⟨S, hS⟩ : Opens X)ᶜᶜ ⊔ (⟨S, hS⟩ : Opens X)ᶜ) = (Set.univ : Set X) := by
        rw [hU, Opens.coe_top]
      rwa [Opens.coe_sup, Opens.coe_compl_compl_eq_interior_closure,
        Opens.coe_compl_eq_compl_closure, Opens.coe_mk] at h1
    have hsub : closure S ⊆ interior (closure S) := by
      intro x hx
      rcases (Set.eq_univ_iff_forall.mp hcoe x) with h' | h'
      · exact h'
      · exact absurd hx h'
    have : closure S = interior (closure S) := Set.Subset.antisymm hsub interior_subset
    rw [this]
    exact isOpen_interior
  · intro hX U
    have hop : IsOpen (closure (U : Set X)) := hX.open_closure _ U.isOpen
    have hcc : ↑(Uᶜᶜ) = closure (U : Set X) := by
      rw [Opens.coe_compl_compl_eq_interior_closure, hop.interior_eq]
    have hcoe : ↑(Uᶜᶜ ⊔ Uᶜ) = (Set.univ : Set X) := by
      rw [Opens.coe_sup, hcc, Opens.coe_compl_eq_compl_closure, Set.union_compl_self]
    apply Opens.ext
    rw [Opens.coe_top]
    exact hcoe

/-- **Corollary, restricted to compact Hausdorff spaces.** Compactness and Hausdorff-ness play no
role in the equivalence itself — they only make `ExtremallyDisconnected X` the classical notion of
`X` being **Stonean** (equivalently, the Stone space of a complete Boolean algebra). -/
theorem isDeMorgan_opens_iff_stonean [CompactSpace X] [T2Space X] :
    Order.Frame.IsDeMorgan (Opens X) ↔ ExtremallyDisconnected X :=
  isDeMorgan_opens_iff_extremallyDisconnected

end Topology

end
