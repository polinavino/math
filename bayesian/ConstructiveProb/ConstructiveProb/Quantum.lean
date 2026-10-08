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

/-! ### Sub-normalized certain states: a stable-set bound

Allowing the missing mass to diverge, as in the probabilistic coherence spaces, the certain states
are the `{0,1}`-valued assignments with at most one ray of value `1` in each basis, the indicators
of the stable sets of the graph whose edges join rays in a common basis. They exist (the zero
assignment), but every mixture of them has total weight at most `4`, while every quantum state
has total weight `9/2`. -/

/-- Sub-normalized certain states. -/
def partialCertain : Set (Fin 18 → ℝ≥0∞) :=
  {s | IsSharpVec s ∧ ∀ b, ∑ i, s (bas b i) ≤ 1}

/-- Summing over the nine bases counts every ray twice. -/
theorem sum_bases (f : Fin 18 → ℝ≥0∞) :
    ∑ b : Fin 9, ∑ i : Fin 4, f (bas b i) = 2 * ∑ v, f v := by
  rw [← Fintype.sum_prod_type' (fun b i => f (bas b i)),
    ← Finset.sum_fiberwise univ (fun p : Fin 9 × Fin 4 => bas p.1 p.2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2], Finset.sum_const,
    occ_two, nsmul_eq_mul]
  norm_num

/-- A sub-normalized certain state has total weight at most `4`. -/
theorem partial_sum_le_four {s : Fin 18 → ℝ≥0∞} (hs : s ∈ partialCertain) : ∑ v, s v ≤ 4 := by
  classical
  have h9 : ∑ b : Fin 9, ∑ i, s (bas b i) ≤ 9 := by
    calc ∑ b : Fin 9, ∑ i, s (bas b i) ≤ ∑ _b : Fin 9, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun b _ => hs.2 b
      _ = 9 := by simp
  rw [sum_bases] at h9
  have hnat : ∑ v, s v = ((univ.filter (fun v => s v = 1)).card : ℝ≥0∞) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    rcases hs.1 v with h | h <;> simp [h]
  rw [hnat] at h9 ⊢
  have h2 : 2 * (univ.filter (fun v => s v = 1)).card ≤ 9 := by exact_mod_cast h9
  have h4 : (univ.filter (fun v => s v = 1)).card ≤ 4 := by omega
  exact_mod_cast h4

/-- **Every mixture of sub-normalized certain states has total weight at most `4`.** -/
theorem mix_sum_le_four {x : Fin 18 → ℝ≥0∞} (hx : x ∈ Mix partialCertain) : ∑ v, x v ≤ 4 := by
  obtain ⟨n, w, s, hs, hw, rfl⟩ := hx
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  calc ∑ i, ∑ v, w i * s i v = ∑ i, w i * ∑ v, s i v := by simp [Finset.mul_sum]
    _ ≤ ∑ i, w i * 4 := Finset.sum_le_sum fun i _ => mul_le_mul_left' (partial_sum_le_four (hs i)) _
    _ = 4 := by rw [← Finset.sum_mul, hw, one_mul]

/-- **Every quantum state has total weight `9/2`.** -/
theorem born_total {ψ : Fin 4 → ℝ} (hψ : ∑ k, ψ k ^ 2 = 1) : 2 * ∑ v, born ψ v = 9 := by
  rw [← sum_bases, Finset.sum_congr rfl fun b _ => born_mem hψ b]
  simp

/-- **No quantum state is a mixture of sub-normalized certain states.** -/
theorem born_not_mix_partial {ψ : Fin 4 → ℝ} (hψ : ∑ k, ψ k ^ 2 = 1) :
    born ψ ∉ Mix partialCertain := by
  intro h
  have h1 := mix_sum_le_four h
  have : (9 : ℝ≥0∞) ≤ 8 := by
    calc (9 : ℝ≥0∞) = 2 * ∑ v, born ψ v := (born_total hψ).symm
      _ ≤ 2 * 4 := mul_le_mul_left' h1 _
      _ = 8 := by norm_num
  norm_num at this

/-- A stable set of four rays. -/
def S4 : Finset (Fin 18) := {0, 1, 3, 11}

theorem S4_stable : ∀ b : Fin 9, (Finset.univ.filter (fun i : Fin 4 => bas b i ∈ S4)).card ≤ 1 := by
  decide

noncomputable def ind4 : Fin 18 → ℝ≥0∞ := fun v => if v ∈ S4 then 1 else 0

/-- **The bound `4` is attained.** -/
theorem ind4_mem : ind4 ∈ partialCertain ∧ ∑ v, ind4 v = 4 := by
  classical
  refine ⟨⟨fun v => ?_, fun b => ?_⟩, ?_⟩
  · unfold ind4; split_ifs <;> simp
  · have : ∑ i, ind4 (bas b i) = ((Finset.univ.filter (fun i : Fin 4 => bas b i ∈ S4)).card : ℝ≥0∞) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => by simp [ind4]
    rw [this]; exact_mod_cast S4_stable b
  · have : ∑ v, ind4 v = ((Finset.univ.filter (fun v : Fin 18 => v ∈ S4)).card : ℝ≥0∞) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun v _ => by simp [ind4]
    rw [this]
    have : (Finset.univ.filter (fun v : Fin 18 => v ∈ S4)).card = 4 := by decide
    rw [this]; norm_num

end ConstructiveProb.Quantum
