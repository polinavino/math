/-
# A gap among total programs, with three functional arguments

At `T = ((2 ⊸ 2) ⊗ (2 ⊸ 2))^⊥` every witness of the gap diverges with positive probability on some
pair of total arguments: an element that halts with probability `1` on all of them is a two-party
classical process, and these are mixtures of processes in a fixed order (Baumeler and Wolf). With
three arguments this fails.

`T3 = ((2 ⊸ 2) ⊗ (2 ⊸ 2) ⊗ (2 ⊸ 2))^⊥`. The witness `y5` takes the value `1` at one point and `½` at
fourteen others. It halts with probability exactly `1` on every triple of total functions
(`y5_total`), lies in the PCS (`y5_mem`), and is not in the calculus (`gap_T3`): five of its
points are pairwise exclusive along a five-cycle, so every `{0,1}`-valued element is `1` on at
most two of them (`sharp5_le`), while `y5` has weight `5/2` there.
-/
import ConstructiveProb.Closure

open scoped ENNReal
open Finset

namespace ConstructiveProb.Linear

open ConstructiveProb.PCS (orth pairing lin mem_lin_iff)
open Fm

/-- `2 ⊸ 2`. -/
abbrev L2 : Fm := lolli (base 2) (base 2)

/-- `(2 ⊸ 2) ⊗ (2 ⊸ 2) ⊗ (2 ⊸ 2)`. -/
abbrev S3 : Fm := tens (tens L2 L2) L2

/-- A program with three functional arguments. -/
abbrev T3 : Fm := Fm.neg S3

/-- The web of `T3`, with its standard instances. -/
abbrev W3 : Type := ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) × (Fin 2 × Fin 2)

/-! ### Total functions -/

/-- The graph of a total function, an element of `P (2 ⊸ 2)`. -/
noncomputable def graph2 (f : Fin 2 → Fin 2) : web L2 → ℝ≥0∞ := fun p => if f p.1 = p.2 then 1 else 0

theorem graph2_mem (f : Fin 2 → Fin 2) : graph2 f ∈ P L2 := by
  rw [P_lolli_base]
  refine (mem_lin_iff (X := Fin 2) (Y := Fin 2) _).2 fun a => ?_
  rw [Fin.sum_univ_two]
  rcases Fin.exists_fin_two.1 ⟨f a, rfl⟩ with h | h <;> simp [graph2, h]

theorem coh_L2 (p q : web L2) : coh L2 p q ↔ (p.1 = q.1 → p.2 = q.2) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;> simp [L2, coh, lolli]

/-- A `{0,1}`-valued element of `P (2 ⊸ 2)` lies below the graph of a total function. -/
theorem sharp_L2_le {s : web L2 → ℝ≥0∞} (hs : s ∈ sharpP L2) : ∃ f, s ≤ graph2 f := by
  classical
  have hrow : ∀ a, s (a, 0) + s (a, 1) ≤ 1 := fun a => by
    have h1 : s ∈ lin (Fin 2) (Fin 2) := P_lolli_base 2 2 ▸ hs.1
    have := (mem_lin_iff (X := Fin 2) (Y := Fin 2) s).1 h1 a
    rwa [Fin.sum_univ_two] at this
  refine ⟨fun a => if s (a, 1) = 1 then 1 else 0, fun p => ?_⟩
  obtain ⟨a, b⟩ := p
  rcases hs.2 (a, b) with h | h
  · rw [h]; simp
  · rw [h]
    simp only [graph2]
    rw [if_pos]
    rcases Fin.exists_fin_two.1 ⟨b, rfl⟩ with rfl | rfl
    · have h1 : s (a, 1) ≠ 1 := fun h1 => by
        have := hrow a
        rw [h, h1, one_add_one_eq_two] at this
        exact absurd this (not_le.2 ENNReal.one_lt_two)
      simp [h1]
    · simp [h]

/-- A `{0,1}`-valued element of `P ((2 ⊸ 2) ⊗ (2 ⊸ 2))` lies below a product of graphs. -/
theorem sharp_L2L2_le {s : web (tens L2 L2) → ℝ≥0∞} (hs : s ∈ sharpP (tens L2 L2)) :
    ∃ f g, s ≤ tvec (graph2 f) (graph2 g) := by
  classical
  have hcl := sharp_isClique (tens L2 L2) hs.1 hs.2
  have key1 : ∀ p q p' q', s (p, q) = 1 → s (p', q') = 1 → p.1 = p'.1 → p.2 = p'.2 :=
    fun p q p' q' h h' e => ((coh_L2 p p').1 (hcl (p, q) (p', q') h h').1) e
  have key2 : ∀ p q p' q', s (p, q) = 1 → s (p', q') = 1 → q.1 = q'.1 → q.2 = q'.2 :=
    fun p q p' q' h h' e => ((coh_L2 q q').1 (hcl (p, q) (p', q') h h').2) e
  refine ⟨fun a => if ∃ q, s ((a, 1), q) = 1 then 1 else 0,
    fun c => if ∃ p, s (p, (c, 1)) = 1 then 1 else 0, fun v => ?_⟩
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := v
  rcases hs.2 ((a, b), (c, d)) with h | h
  · rw [h]; simp
  · rw [h]
    have hf : (if ∃ q, s ((a, 1), q) = 1 then (1 : Fin 2) else 0) = b := by
      rcases Fin.exists_fin_two.1 ⟨b, rfl⟩ with rfl | rfl
      · rw [if_neg]
        rintro ⟨q, hq⟩
        exact absurd (key1 _ _ _ _ h hq rfl) (by simp)
      · rw [if_pos ⟨(c, d), h⟩]
    have hg : (if ∃ p, s (p, (c, 1)) = 1 then (1 : Fin 2) else 0) = d := by
      rcases Fin.exists_fin_two.1 ⟨d, rfl⟩ with rfl | rfl
      · rw [if_neg]
        rintro ⟨p, hp⟩
        exact absurd (key2 _ _ _ _ h hp rfl) (by simp)
      · rw [if_pos ⟨(a, b), h⟩]
    simp only [tvec, graph2]
    rw [if_pos hf, if_pos hg, one_mul]

/-! ### The witness -/

/-- The point of weight `1`. -/
def onePt : W3 := (((1, 0), (0, 1)), (1, 1))

/-- The fourteen points of weight `½`. -/
def halfPts : Finset W3 :=
  {(((0, 0), (0, 0)), (0, 0)), (((0, 0), (0, 1)), (1, 0)), (((0, 1), (0, 0)), (0, 0)),
   (((0, 1), (0, 1)), (1, 0)), (((1, 0), (0, 0)), (0, 1)), (((1, 0), (0, 0)), (1, 1)),
   (((1, 0), (1, 0)), (1, 0)), (((1, 0), (1, 1)), (1, 0)), (((1, 1), (0, 0)), (1, 0)),
   (((1, 1), (0, 1)), (0, 0)), (((1, 1), (1, 0)), (0, 1)), (((1, 1), (1, 0)), (1, 1)),
   (((1, 1), (1, 1)), (0, 1)), (((1, 1), (1, 1)), (1, 1))}

/-- Twice the witness. -/
def k3 (v : W3) : ℕ := if v = onePt then 2 else if v ∈ halfPts then 1 else 0

/-- The witness. -/
noncomputable def y5 : web T3 → ℝ≥0∞ := fun v => (k3 v : ℝ≥0∞) * 2⁻¹

/-- Whether `v` is consistent with the total functions `f, g, h`. -/
def cons (f g h : Fin 2 → Fin 2) (v : W3) : ℕ :=
  if f v.1.1.1 = v.1.1.2 ∧ g v.1.2.1 = v.1.2.2 ∧ h v.2.1 = v.2.2 then 1 else 0

/-- On every triple of total functions, the consistent points carry weight `2`. -/
theorem cons_sum : ∀ f g h : Fin 2 → Fin 2, ∑ v : W3, cons f g h v * k3 v = 2 := by
  decide

theorem graphs_eq (f g h : Fin 2 → Fin 2) (v : web T3) :
    tvec (tvec (graph2 f) (graph2 g)) (graph2 h) v = (cons f g h v : ℝ≥0∞) := by
  obtain ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, k⟩⟩ := v
  simp only [tvec, graph2, cons]
  by_cases h1 : f a = b <;> by_cases h2 : g c = d <;> by_cases h3 : h e = k <;> simp [h1, h2, h3]

/-- **The witness halts with probability `1` on every triple of total functions.** -/
theorem y5_total (f g h : Fin 2 → Fin 2) :
    pairing (tvec (tvec (graph2 f) (graph2 g)) (graph2 h)) y5 = 1 := by
  simp only [pairing, graphs_eq, y5]
  have e : ∀ v : web T3, (cons f g h v : ℝ≥0∞) * ((k3 v : ℝ≥0∞) * 2⁻¹) =
      ((cons f g h v * k3 v : ℕ) : ℝ≥0∞) * 2⁻¹ := fun v => by push_cast; ring
  simp only [e]
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  have : (∑ v : web T3, cons f g h v * k3 v) = ∑ v : W3, cons f g h v * k3 v :=
    Fintype.sum_equiv (Equiv.refl _) _ _ fun _ => rfl
  rw [this, cons_sum]
  exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

theorem recipe_L2L2 : recipe (tens L2 L2) = P (tens L2 L2) :=
  recipe_tens (recipe_lolli_base 2 2) (recipe_lolli_base 2 2)

/-- **The witness is an element of the PCS.** -/
theorem y5_mem : y5 ∈ P T3 := by
  rw [P_neg_tens_eq recipe_L2L2 (recipe_lolli_base 2 2)]
  rintro _ ⟨s, hs, c, hc, rfl⟩
  obtain ⟨f, g, hfg⟩ := sharp_L2L2_le hs
  obtain ⟨h, hh⟩ := sharp_L2_le hc
  calc pairing (tvec s c) y5 ≤ pairing (tvec (tvec (graph2 f) (graph2 g)) (graph2 h)) y5 :=
        Finset.sum_le_sum fun v _ => mul_le_mul_left (mul_le_mul' (hfg v.1) (hh v.2)) _
    _ = 1 := y5_total f g h

/-! ### Five exclusive points -/

def c0 : web T3 := (((0, 0), (0, 1)), (1, 0))
def c1 : web T3 := (((1, 0), (1, 0)), (1, 0))
def c2 : web T3 := (((0, 0), (0, 0)), (0, 0))
def c3 : web T3 := (((1, 1), (0, 0)), (1, 0))
def c4 : web T3 := (((1, 1), (1, 0)), (0, 1))

/-- Two points are incoherent in `T3` when each function's observations are compatible. -/
theorem not_coh_T3 (v v' : W3) (hne : v ≠ v') (h1 : v.1.1.1 = v'.1.1.1 → v.1.1.2 = v'.1.1.2)
    (h2 : v.1.2.1 = v'.1.2.1 → v.1.2.2 = v'.1.2.2) (h3 : v.2.1 = v'.2.1 → v.2.2 = v'.2.2) :
    ¬ coh T3 v v' := by
  rintro (h | h)
  · exact hne h
  · exact h ⟨⟨(coh_L2 _ _).2 h1, (coh_L2 _ _).2 h2⟩, (coh_L2 _ _).2 h3⟩

/-- **A `{0,1}`-valued element is `1` on at most two of the five points.** Consecutive points of
the cycle are produced together by some triple of total functions. -/
theorem sharp5_le {s : web T3 → ℝ≥0∞} (hs : s ∈ P T3) (h01 : ∀ v, s v = 0 ∨ s v = 1) :
    s c0 + s c1 + s c2 + s c3 + s c4 ≤ 2 := by
  have inc : ∀ v v' : web T3, v ≠ v' → ¬ coh T3 v v' → s v + s v' ≤ 1 :=
    fun v v' hne hc => (invariants T3).2.2 v v' hne hc s hs
  have e01 := inc c0 c1 (show (c0 : W3) ≠ c1 by decide)
    (not_coh_T3 c0 c1 (by decide) (by decide) (by decide) (by decide))
  have e12 := inc c1 c2 (show (c1 : W3) ≠ c2 by decide)
    (not_coh_T3 c1 c2 (by decide) (by decide) (by decide) (by decide))
  have e23 := inc c2 c3 (show (c2 : W3) ≠ c3 by decide)
    (not_coh_T3 c2 c3 (by decide) (by decide) (by decide) (by decide))
  have e34 := inc c3 c4 (show (c3 : W3) ≠ c4 by decide)
    (not_coh_T3 c3 c4 (by decide) (by decide) (by decide) (by decide))
  have e40 := inc c4 c0 (show (c4 : W3) ≠ c0 by decide)
    (not_coh_T3 c4 c0 (by decide) (by decide) (by decide) (by decide))
  have k : ¬ ((1 : ℝ≥0∞) + 1 ≤ 1) := by
    rw [one_add_one_eq_two]; exact not_le.2 ENNReal.one_lt_two
  rcases h01 c0 with h0 | h0 <;> rcases h01 c1 with h1 | h1 <;> rcases h01 c2 with h2 | h2 <;>
    rcases h01 c3 with h3 | h3 <;> rcases h01 c4 with h4 | h4 <;>
    simp only [h0, h1, h2, h3, h4] at e01 e12 e23 e34 e40 ⊢ <;>
    first
    | exact absurd e01 k | exact absurd e12 k | exact absurd e23 k | exact absurd e34 k
    | exact absurd e40 k | norm_num

theorem y5_cycle : y5 c0 + y5 c1 + y5 c2 + y5 c3 + y5 c4 = 5 * 2⁻¹ := by
  have e0 : k3 c0 = 1 := by decide
  have e1 : k3 c1 = 1 := by decide
  have e2 : k3 c2 = 1 := by decide
  have e3 : k3 c3 = 1 := by decide
  have e4 : k3 c4 = 1 := by decide
  simp only [y5, e0, e1, e2, e3, e4, Nat.cast_one, one_mul]
  ring

/-- **The gap among total programs.** The calculus of `((2 ⊸ 2) ⊗ (2 ⊸ 2) ⊗ (2 ⊸ 2))^⊥` is
strictly smaller than its PCS, witnessed by an element that halts with probability `1` on every
triple of total functions. -/
theorem gap_T3 : recipe T3 ⊂ P T3 := by
  refine Set.ssubset_iff_subset_ne.2 ⟨recipe_subset_P _, fun h => ?_⟩
  have hy : y5 ∈ recipe T3 := h ▸ y5_mem
  obtain ⟨n, w, s, hs, hw, heq⟩ := hy
  have rhs : (∑ i, w i • s i) c0 + (∑ i, w i • s i) c1 + (∑ i, w i • s i) c2 +
      (∑ i, w i • s i) c3 + (∑ i, w i • s i) c4 ≤ 2 := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    calc ∑ i, (w i * s i c0 + w i * s i c1 + w i * s i c2 + w i * s i c3 + w i * s i c4)
        = ∑ i, w i * (s i c0 + s i c1 + s i c2 + s i c3 + s i c4) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, w i * 2 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_left' (sharp5_le (hs i).1 (hs i).2) _
      _ = 2 := by rw [← Finset.sum_mul, hw, one_mul]
  rw [← heq, y5_cycle] at rhs
  have : (5 : ℝ≥0∞) * 2⁻¹ = 5 / 2 := (div_eq_mul_inv _ _).symm
  rw [this, ENNReal.div_le_iff two_ne_zero ENNReal.ofNat_ne_top] at rhs
  norm_num at rhs

end ConstructiveProb.Linear
