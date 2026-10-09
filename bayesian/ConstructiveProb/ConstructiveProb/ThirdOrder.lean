/-
# A third-order gap without two four-cycles

`F3 = (2 & 1) ⊸ ((2 ⊸ 2) ⊗ (2 ⊸ 2))`, that is `((2 & 1) ⊗ T)^⊥` with `T` the second-order type of
`LinearInstances.lean`, has calculus strictly smaller than its PCS (`gap_F3`). The factor `2 & 1`
has three points, so its coherence graph has no induced four-cycle (`X3_no_C4`) and `gap_of_C4`
does not apply.

The witness `y3` is `½` on five points. It lies in `P F3` because four pairs of the five points of
`T` used are incoherent in `T` (`y3_mem`). The five points form a five-cycle of coherence in `F3`,
so every `{0,1}`-valued element of `P F3` is `1` on at most two of them (`sharp3_le`), while `y3`
has total weight `5/2` there.
-/
import ConstructiveProb.Retract

open scoped ENNReal
open Finset

namespace ConstructiveProb.Linear

open ConstructiveProb.PCS (orth pairing orth_orth_orth)
open Fm

/-- The input `2 & 1`. -/
abbrev X3 : Fm := wth (base 2) (base 1)

/-- `(2 & 1) ⊸ ((2 ⊸ 2) ⊗ (2 ⊸ 2))`. -/
abbrev F3 : Fm := Fm.neg (tens X3 S2)

theorem F3_eq : F3 = lolli X3 (core 2 2 2 2) := rfl

/-- Five points of the web of `T`. -/
def w0 : web S2 := ((0, 0), (0, 0))
def w1 : web S2 := ((0, 0), (0, 1))
def w2 : web S2 := ((0, 1), (1, 1))
def w3 : web S2 := ((1, 0), (0, 1))
def w4 : web S2 := ((1, 1), (1, 0))

/-- The three points of `2 & 1`. -/
def p0 : web X3 := Sum.inl 0
def p1 : web X3 := Sum.inl 1
def pu : web X3 := Sum.inr 0

/-- The support of the witness. -/
def supp3 : Finset (web F3) := {(p0, w2), (p0, w4), (p1, w0), (pu, w1), (pu, w3)}

/-- The witness: `½` on `supp3`. -/
noncomputable def y3 : web F3 → ℝ≥0∞ := fun v => if v ∈ supp3 then 2⁻¹ else 0

theorem sum_supp3 (f : web F3 → ℝ≥0∞) :
    ∑ v ∈ supp3, f v = f (p0, w2) + f (p0, w4) + f (p1, w0) + f (pu, w1) + f (pu, w3) := by
  simp only [supp3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem pairing_y3 (z : web F3 → ℝ≥0∞) : pairing z y3 = ∑ v ∈ supp3, z v * 2⁻¹ := by
  simp only [pairing, y3, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **The witness is an element of the PCS.** -/
theorem y3_mem : y3 ∈ P F3 := by
  show y3 ∈ orth (orth (orth {z | ∃ x ∈ P X3, ∃ t ∈ P S2, z = tvec x t}))
  rw [orth_orth_orth]
  rintro _ ⟨x, hx, t, ht, rfl⟩
  rw [pairing_y3, ← Finset.sum_mul, sum_supp3]
  simp only [tvec]
  -- the input `2 & 1`
  have hx2 : x p0 + x p1 ≤ 1 := by
    have h := hx.1
    simp only [P, ConstructiveProb.PCS.flat, Set.mem_setOf_eq, Fin.sum_univ_two] at h
    exact h
  have hxu : x pu ≤ 1 := by
    have h := hx.2
    simp only [P, ConstructiveProb.PCS.flat, Set.mem_setOf_eq, Fin.sum_univ_one] at h
    exact h
  -- incoherent pairs of `T`
  have e14 : t w1 + t w4 ≤ 1 :=
    (invariants S2).2.2 w1 w4 (by decide) (by simp [S2, second, coh, lolli, w1, w4]) t ht
  have e23 : t w2 + t w3 ≤ 1 :=
    (invariants S2).2.2 w2 w3 (by decide) (by simp [S2, second, coh, lolli, w2, w3]) t ht
  have e13 : t w1 + t w3 ≤ 1 :=
    (invariants S2).2.2 w1 w3 (by decide) (by simp [S2, second, coh, lolli, w1, w3]) t ht
  have e0 : t w0 ≤ 1 := ((invariants S2).1 w0).2 t ht
  set A := t w2 + t w4
  set B := t w0
  set C := t w1 + t w3
  have hAB : x p0 * A + x p1 * B ≤ max A B :=
    calc x p0 * A + x p1 * B ≤ x p0 * max A B + x p1 * max A B :=
          add_le_add (mul_le_mul_left' (le_max_left _ _) _) (mul_le_mul_left' (le_max_right _ _) _)
      _ = (x p0 + x p1) * max A B := (add_mul _ _ _).symm
      _ ≤ 1 * max A B := mul_le_mul_right' hx2 _
      _ = max A B := one_mul _
  have hC : x pu * C ≤ C := mul_le_of_le_one_left' hxu
  have hAC : A + C ≤ 2 :=
    calc A + C = (t w1 + t w4) + (t w2 + t w3) := by simp only [A, C]; ring
      _ ≤ 1 + 1 := add_le_add e14 e23
      _ = 2 := one_add_one_eq_two
  have hBC : B + C ≤ 2 :=
    calc B + C ≤ 1 + 1 := add_le_add e0 e13
      _ = 2 := one_add_one_eq_two
  have hmax : max A B + C ≤ 2 := by
    rcases le_total A B with h | h
    · rw [max_eq_right h]; exact hBC
    · rw [max_eq_left h]; exact hAC
  calc (x p0 * t w2 + x p0 * t w4 + x p1 * t w0 + x pu * t w1 + x pu * t w3) * 2⁻¹
      = ((x p0 * A + x p1 * B) + x pu * C) * 2⁻¹ := by simp only [A, B, C]; ring
    _ ≤ (max A B + C) * 2⁻¹ := mul_le_mul_right' (add_le_add hAB hC) _
    _ ≤ 2 * 2⁻¹ := mul_le_mul_right' hmax _
    _ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- **A `{0,1}`-valued element is `1` on at most two of the five points.** -/
theorem sharp3_le {s : web F3 → ℝ≥0∞} (hs : s ∈ P F3) (h01 : ∀ v, s v = 0 ∨ s v = 1) :
    ∑ v ∈ supp3, s v ≤ 2 := by
  have inc : ∀ v v' : web F3, v ≠ v' → ¬ coh F3 v v' → s v + s v' ≤ 1 :=
    fun v v' hne hc => (invariants F3).2.2 v v' hne hc s hs
  have e12 := inc (p0, w2) (p0, w4) (by decide) (by simp [S2, second, coh, lolli, p0, w2, w4])
  have e14 := inc (p0, w2) (pu, w1) (by decide) (by simp [S2, second, coh, lolli, p0, pu, w2, w1])
  have e25 := inc (p0, w4) (pu, w3) (by decide) (by simp [S2, second, coh, lolli, p0, pu, w4, w3])
  have e34 := inc (p1, w0) (pu, w1) (by decide) (by simp [S2, second, coh, lolli, p1, pu, w0, w1])
  have e35 := inc (p1, w0) (pu, w3) (by decide) (by simp [S2, second, coh, lolli, p1, pu, w0, w3])
  have k : ¬ ((1 : ℝ≥0∞) + 1 ≤ 1) := by
    rw [one_add_one_eq_two]; exact not_le.2 ENNReal.one_lt_two
  rw [sum_supp3]
  rcases h01 (p0, w2) with h1 | h1 <;> rcases h01 (p0, w4) with h2 | h2 <;>
    rcases h01 (p1, w0) with h3 | h3 <;> rcases h01 (pu, w1) with h4 | h4 <;>
    rcases h01 (pu, w3) with h5 | h5 <;>
    simp only [h1, h2, h3, h4, h5] at e12 e14 e25 e34 e35 ⊢ <;>
    first
    | exact absurd e12 k | exact absurd e14 k | exact absurd e25 k | exact absurd e34 k
    | exact absurd e35 k | norm_num

/-- **The gap at `(2 & 1) ⊸ ((2 ⊸ 2) ⊗ (2 ⊸ 2))`.** -/
theorem gap_F3 : recipe F3 ⊂ P F3 := by
  refine Set.ssubset_iff_subset_ne.2 ⟨recipe_subset_P _, fun h => ?_⟩
  have hy : y3 ∈ recipe F3 := h ▸ y3_mem
  obtain ⟨n, w, s, hs, hw, heq⟩ := hy
  have lhs : ∑ v ∈ supp3, y3 v = 5 * 2⁻¹ := by
    rw [sum_supp3]; simp only [y3]; simp [supp3]; ring
  have rhs : ∑ v ∈ supp3, (∑ i, w i • s i) v ≤ 2 := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    calc ∑ i, ∑ v ∈ supp3, w i * s i v = ∑ i, w i * ∑ v ∈ supp3, s i v := by
          simp [Finset.mul_sum]
      _ ≤ ∑ i, w i * 2 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_left' (sharp3_le (hs i).1 (hs i).2) _
      _ = 2 := by rw [← Finset.sum_mul, hw, one_mul]
  rw [← heq, lhs] at rhs
  have : (5 : ℝ≥0∞) * 2⁻¹ = 5 / 2 := (div_eq_mul_inv _ _).symm
  rw [this, ENNReal.div_le_iff two_ne_zero ENNReal.ofNat_ne_top] at rhs
  norm_num at rhs

/-- **The factor `2 & 1` has no induced four-cycle**: its web has three points. -/
theorem X3_no_C4 (Q : C4 X3) : False := by
  have h := Fintype.card_le_of_injective Q.j Q.j_inj
  have h3 : Fintype.card (web X3) = 3 := rfl
  rw [h3, Fintype.card_prod, Fintype.card_fin] at h
  omega

end ConstructiveProb.Linear
