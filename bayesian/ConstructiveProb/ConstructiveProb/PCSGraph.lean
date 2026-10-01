/-
# Second-order PCS as graph polytopes

For `T = ((X ⊸ Y) ⊗ (X' ⊸ Y'))^⊥`, let two distinct web points be *exclusive* when one
deterministic pair covers both. Then `T = QSTAB` of the exclusivity graph (`tD_eq_QSTAB`), the
recipe's calculus is `STAB` of it (`recipe_eq_STAB`), and so the recipe agrees with the PCS only
if the exclusivity graph is Berge (`berge_of_recipe_eq_pcs`).
-/
import ConstructiveProb.General
import ConstructiveProb.PerfectGraph

open scoped ENNReal
open Finset

namespace ConstructiveProb.PCS.General

open ConstructiveProb.Graph

variable {X Y X' Y' : Type} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
  [DecidableEq X] [DecidableEq Y] [DecidableEq X'] [DecidableEq Y']

/-- Exclusivity: distinct and jointly coverable. -/
def excl (s t : (X × Y) × (X' × Y')) : Prop := s ≠ t ∧ cp2 s t

theorem cp2_refl (s : (X × Y) × (X' × Y')) : cp2 s s := ⟨Or.inl rfl, Or.inl rfl⟩

theorem clique_excl_iff (C : Finset ((X × Y) × (X' × Y'))) :
    IsCliqueG excl C ↔ ∀ s ∈ C, ∀ u ∈ C, cp2 s u := by
  constructor
  · intro h s hs u hu
    by_cases e : s = u
    · subst e; exact cp2_refl s
    · exact (h s hs u hu e).2
  · intro h s hs u hu e; exact ⟨e, h s hs u hu⟩

/-- **`T` is `QSTAB` of its exclusivity graph.** -/
theorem tD_eq_QSTAB : tD X Y X' Y' = QSTAB (excl (X := X) (Y := Y) (X' := X') (Y' := Y')) := by
  ext x
  rw [tD_iff_qstab]
  exact ⟨fun h C hC => h C ((clique_excl_iff C).1 hC), fun h C hC => h C ((clique_excl_iff C).2 hC)⟩

/-- **The recipe is `STAB` of the exclusivity graph.** -/
theorem recipe_eq_STAB :
    Mix {z | z ∈ tD X Y X' Y' ∧ ∀ u, z u = 0 ∨ z u = 1}
      = STAB (excl (X := X) (Y := Y) (X' := X') (Y' := Y')) := by
  classical
  unfold STAB
  congr 1
  ext z
  constructor
  · rintro ⟨hz, h01⟩
    refine ⟨univ.filter (z · = 1), fun s hs t ht hst => ?_, ?_⟩
    · exact sharp_excl' hz (Finset.mem_filter.1 hs).2 (Finset.mem_filter.1 ht).2 hst.1 hst.2
    · funext u; simp only [ind, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases h01 u with h | h <;> simp [h]
  · rintro ⟨I, hI, rfl⟩
    refine ⟨?_, fun u => by simp only [ind]; split_ifs <;> simp⟩
    rw [tD_iff_qstab]
    intro C hC
    rw [sum_ind]
    have : (C ∩ I).card ≤ 1 := Finset.card_le_one.2 fun s hs t ht => by
      by_contra e
      exact hI s (Finset.mem_inter.1 hs).2 t (Finset.mem_inter.1 ht).2
        ⟨e, hC s (Finset.mem_inter.1 hs).1 t (Finset.mem_inter.1 ht).1⟩
    exact_mod_cast this

/-- **If the recipe equals the PCS, the exclusivity graph is Berge.** -/
theorem berge_of_recipe_eq_pcs
    (heq : Mix {z | z ∈ tD X Y X' Y' ∧ ∀ u, z u = 0 ∨ z u = 1} = tD X Y X' Y')
    (k : ℕ) (hk : 2 ≤ k) [NeZero (2 * k + 1)] :
    IsEmpty (Hole (excl (X := X) (Y := Y) (X' := X') (Y' := Y')) (2 * k + 1)) ∧
      IsEmpty (Antihole (excl (X := X) (Y := Y) (X' := X') (Y' := Y')) (2 * k + 1)) := by
  rw [recipe_eq_STAB, tD_eq_QSTAB] at heq
  exact berge_of_stab_eq_qstab heq k hk

end ConstructiveProb.PCS.General
