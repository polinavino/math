/-
# Separation and the hinge on finite lattices, without choice

`Points.exists_sharp_separating`, `LValuation.exists_sharp_separating` and
`em_of_forall_hasClassicalNegation` use the prime ideal theorem
(`DistribLattice.prime_ideal_of_disjoint_filter_ideal`), a choice principle. For a finite
distributive lattice with decidable order the needed prime filter can be found by search: a
minimal element below `a` and not below `b` is join-prime, and its principal filter is prime.
This file proves the finite statements this way, with `{0,1}`-valued, `ℕ`-valued valuations.
`#print axioms` reports no use of `Classical.choice` for `exists_sharp_separating_fin` and
`em_of_sharp_complement_fin`.
-/
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Card

namespace ConstructiveProb.FiniteConstructive

variable {α : Type} [DistribLattice α] [Fintype α] [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)]

/-- `j` is join-prime. -/
def JoinPrime (j : α) : Prop := ∀ x y : α, j ≤ x ⊔ y → j ≤ x ∨ j ≤ y

/-- The elements below `a`. -/
def below (a : α) : Finset α := Finset.univ.filter (· ≤ a)

theorem below_card_lt {c a : α} (hca : c ≤ a) (hne : ¬ a ≤ c) :
    (below c).card < (below a).card := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [below, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact le_trans hx hca
  · have : a ∈ below c := h (by simp [below])
    simp only [below, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hne this

/-- **Finite prime filter by search.** If `a ≰ b`, some join-prime `j ≤ a` has `j ≰ b`. -/
theorem exists_joinPrime_aux : ∀ (n : ℕ) (a b : α), (below a).card = n → ¬ a ≤ b →
    ∃ j, j ≤ a ∧ ¬ j ≤ b ∧ JoinPrime j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab
    by_cases hp : ∀ x y : α, a ≤ x ⊔ y → a ≤ x ∨ a ≤ y
    · exact ⟨a, le_refl a, hab, hp⟩
    · -- `a` is not join-prime: split it
      have hex : ∃ x : α, ∃ y : α, a ≤ x ⊔ y ∧ ¬ a ≤ x ∧ ¬ a ≤ y := by
        apply Decidable.byContradiction
        intro hne
        apply hp
        intro x y hxy
        apply Decidable.byContradiction
        intro hc
        exact hne ⟨x, y, hxy, fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩
      obtain ⟨x, y, hxy, hx, hy⟩ := hex
      have hsplit : a = (a ⊓ x) ⊔ (a ⊓ y) := by
        rw [← inf_sup_left]; exact (inf_eq_left.2 hxy).symm
      by_cases h1 : a ⊓ x ≤ b
      · by_cases h2 : a ⊓ y ≤ b
        · exact absurd (hsplit ▸ sup_le h1 h2) hab
        · obtain ⟨j, hj, hjb, hjp⟩ := ih _ (hn ▸ below_card_lt inf_le_left
            (fun h => hy (le_trans h inf_le_right))) (a ⊓ y) b rfl h2
          exact ⟨j, le_trans hj inf_le_left, hjb, hjp⟩
      · obtain ⟨j, hj, hjb, hjp⟩ := ih _ (hn ▸ below_card_lt inf_le_left
          (fun h => hx (le_trans h inf_le_right))) (a ⊓ x) b rfl h1
        exact ⟨j, le_trans hj inf_le_left, hjb, hjp⟩

/-- The indicator of the principal filter of `j`. -/
def ind (j x : α) : ℕ := if j ≤ x then 1 else 0

theorem ind_modular {j : α} (hj : JoinPrime j) (x y : α) :
    ind j x + ind j y = ind j (x ⊔ y) + ind j (x ⊓ y) := by
  unfold ind
  by_cases hx : j ≤ x <;> by_cases hy : j ≤ y
  · rw [if_pos hx, if_pos hy, if_pos (le_trans hx le_sup_left), if_pos (le_inf hx hy)]
  · rw [if_pos hx, if_neg hy, if_pos (le_trans hx le_sup_left),
      if_neg (fun h => hy (le_trans h inf_le_right))]
  · rw [if_neg hx, if_pos hy, if_pos (le_trans hy le_sup_right),
      if_neg (fun h => hx (le_trans h inf_le_left))]
  · rw [if_neg hx, if_neg hy, if_neg (fun h => (hj x y h).elim hx hy),
      if_neg (fun h => hx (le_trans h inf_le_left))]

/-- **Sharp valuations separate points of a finite distributive lattice, without choice.**
For `a ≰ b` there is a monotone, modular, `{0,1}`-valued `v` with `v ⊥ = 0`, `v ⊤ = 1`,
`v a = 1` and `v b = 0`. -/
theorem exists_sharp_separating_fin [BoundedOrder α] {a b : α} (hab : ¬ a ≤ b) :
    ∃ v : α → ℕ, (∀ x, v x = 0 ∨ v x = 1) ∧ Monotone v ∧ v ⊥ = 0 ∧ v ⊤ = 1 ∧
      (∀ x y, v x + v y = v (x ⊔ y) + v (x ⊓ y)) ∧ v a = 1 ∧ v b = 0 := by
  obtain ⟨j, hja, hjb, hjp⟩ := exists_joinPrime_aux _ a b rfl hab
  refine ⟨ind j, fun x => ?_, fun x y hxy => ?_, ?_, ?_, ind_modular hjp, ?_, ?_⟩
  · unfold ind; by_cases h : j ≤ x
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  · unfold ind; by_cases h : j ≤ x
    · rw [if_pos h, if_pos (le_trans h hxy)]
    · rw [if_neg h]; exact Nat.zero_le _
  · unfold ind; exact if_neg (fun h => hjb (le_trans h bot_le))
  · unfold ind; exact if_pos le_top
  · unfold ind; exact if_pos hja
  · unfold ind; exact if_neg hjb

/-- **The hinge on a finite distributive lattice, without choice.** If every `{0,1}`-valued
modular valuation gives `a` and `c` total `1`, then `a ⊔ c = ⊤`. With `c = aᶜ` this is the
direction of the hinge that uses the prime ideal theorem in general. -/
theorem em_of_sharp_complement_fin [BoundedOrder α] (a c : α)
    (h : ∀ v : α → ℕ, (∀ x, v x = 0 ∨ v x = 1) → Monotone v → v ⊥ = 0 → v ⊤ = 1 →
      (∀ x y, v x + v y = v (x ⊔ y) + v (x ⊓ y)) → v a + v c = 1) :
    a ⊔ c = ⊤ := by
  apply Decidable.byContradiction
  intro hne
  have hnle : ¬ (⊤ : α) ≤ a ⊔ c := fun hle => hne (top_le_iff.1 hle)
  obtain ⟨v, h01, hmono, hbot, htop, hmod, -, hb⟩ := exists_sharp_separating_fin hnle
  have ha : v a = 0 := Nat.le_zero.1 (hb ▸ hmono le_sup_left)
  have hc : v c = 0 := Nat.le_zero.1 (hb ▸ hmono le_sup_right)
  have := h v h01 hmono hbot htop hmod
  rw [ha, hc] at this
  exact absurd this (by decide)

end ConstructiveProb.FiniteConstructive
