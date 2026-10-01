/-
# Quantum event logic: no certain states

Events are the 18 rays of Cabello's Kochen–Specker set in `ℝ⁴` (Cabello, Estebaranz,
García-Alcaine 1996), and the contexts are 9 orthogonal bases formed from them, each ray lying in
exactly two bases (`basis_orth`, `occ_two`). A certain state is a `{0,1}`-valued assignment that
gives exactly one ray of every basis the value `1`.

* `no_certain_state`: there is none (parity: `9` bases, each ray counted twice).
* `Mix_certain_empty`: so the calculus of `Recipe.lean` is empty.
* `born_mem`: every Born-rule assignment `x_v = (ψ·v)² / (v·v)` of a unit vector `ψ` sums to `1`
  on every basis, so quantum states exist and are not mixtures of certain states
  (`born_not_mix`).
-/
import ConstructiveProb.Recipe

open scoped ENNReal
open Finset

namespace ConstructiveProb.Quantum

/-- The 18 rays. -/
def vec : Fin 18 → Fin 4 → ℤ := ![
  ![-1, 1, 1, 1], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1],
  ![0, 1, 0, 0], ![1, -1, -1, 1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1],
  ![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 1, -1, 1], ![1, 1, 0, 0], ![1, 1, 1, -1], ![1, 1, 1, 1]]

/-- The 9 orthogonal bases, as indices into `vec`. -/
def bas : Fin 9 → Fin 4 → Fin 18 := ![
  ![1, 2, 15, 8], ![1, 6, 13, 10], ![9, 7, 15, 3], ![9, 17, 10, 5], ![2, 6, 12, 11],
  ![7, 17, 11, 4], ![14, 16, 8, 3], ![14, 0, 13, 5], ![16, 0, 12, 4]]

def dot (u v : Fin 4 → ℤ) : ℤ := ∑ k, u k * v k

/-- Each context is an orthogonal basis. -/
theorem basis_orth : ∀ b : Fin 9, ∀ i j : Fin 4, i ≠ j → dot (vec (bas b i)) (vec (bas b j)) = 0 := by
  decide

/-- Each ray lies in exactly two contexts. -/
theorem occ_two : ∀ v : Fin 18,
    (univ.filter (fun p : Fin 9 × Fin 4 => bas p.1 p.2 = v)).card = 2 := by
  decide

/-- **Kochen–Specker for Cabello's set.** No `{0,1}` assignment gives exactly one ray of every
basis the value `1`. -/
theorem no_ks : ¬ ∃ f : Fin 18 → Bool, ∀ b, (univ.filter (fun i => f (bas b i))).card = 1 := by
  rintro ⟨f, hf⟩
  let g : Fin 18 → ℕ := fun v => if f v then 1 else 0
  have h1 : ∑ b : Fin 9, ∑ i : Fin 4, g (bas b i) = 9 := by
    have : ∀ b, ∑ i : Fin 4, g (bas b i) = 1 := fun b => by
      rw [← hf b, Finset.card_filter]
    simp [this]
  have h2 : ∑ b : Fin 9, ∑ i : Fin 4, g (bas b i) = ∑ v, 2 * g v := by
    rw [← Fintype.sum_prod_type' (fun b i => g (bas b i)),
      ← Finset.sum_fiberwise univ (fun p : Fin 9 × Fin 4 => bas p.1 p.2)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2], Finset.sum_const,
      occ_two, smul_eq_mul]
  rw [h2, ← Finset.mul_sum] at h1
  omega

/-- The certain states: `{0,1}`-valued, normalized on every context. -/
def certain : Set (Fin 18 → ℝ≥0∞) :=
  {s | IsSharpVec s ∧ ∀ b, ∑ i, s (bas b i) = 1}

theorem no_certain_state : certain = ∅ := by
  classical
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨h01, hs⟩
  apply no_ks
  refine ⟨fun v => decide (s v = 1), fun b => ?_⟩
  have : ∑ i, s (bas b i) = ((univ.filter (fun i => decide (s (bas b i) = 1))).card : ℝ≥0∞) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases h01 (bas b i) with h | h <;> simp [h]
  rw [hs b] at this
  exact_mod_cast this.symm

/-- **The calculus of quantum event logic is empty.** -/
theorem Mix_certain_empty : Mix certain = ∅ := by
  rw [no_certain_state]
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨n, w, s, hs, hw, -⟩
  cases n with
  | zero => simp at hw
  | succ n => exact hs 0

/-- The quantum states of this event logic: assignments normalized on every context. -/
def states : Set (Fin 18 → ℝ≥0∞) := {x | ∀ b, ∑ i, x (bas b i) = 1}

/-- The Born-rule assignment of `ψ`. -/
noncomputable def born (ψ : Fin 4 → ℝ) : Fin 18 → ℝ≥0∞ := fun v =>
  ENNReal.ofReal ((∑ k, ψ k * vec v k) ^ 2 / ∑ k, ((vec v k : ℝ)) ^ 2)

/-- Parseval on each context. -/
theorem parseval (ψ : Fin 4 → ℝ) (b : Fin 9) :
    ∑ i, (∑ k, ψ k * vec (bas b i) k) ^ 2 / ∑ k, ((vec (bas b i) k : ℝ)) ^ 2 = ∑ k, ψ k ^ 2 := by
  fin_cases b <;>
    simp [vec, bas, Fin.sum_univ_four] <;> ring

/-- **Born-rule assignments of unit vectors are quantum states.** -/
theorem born_mem {ψ : Fin 4 → ℝ} (hψ : ∑ k, ψ k ^ 2 = 1) : born ψ ∈ states := by
  intro b
  simp only [born]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, parseval, hψ, ENNReal.ofReal_one]

/-- **Quantum states are not mixtures of certain states.** -/
theorem born_not_mix {ψ : Fin 4 → ℝ} (hψ : ∑ k, ψ k ^ 2 = 1) :
    born ψ ∈ states ∧ born ψ ∉ Mix certain := by
  refine ⟨born_mem hψ, ?_⟩
  rw [Mix_certain_empty]; exact id

end ConstructiveProb.Quantum
