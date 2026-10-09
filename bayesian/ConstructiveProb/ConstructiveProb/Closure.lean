/-
# Closure of "no gap" under `⊗` and `&`

* `orth_orth_subset_Mix`: for a finite, downward-closed set `S` of `{0,1}`-vectors containing `0`,
  the bipolar `S^⊥⊥` is `Mix S`. The proof separates a point outside `Mix S` by a hyperplane,
  drops the negative coefficients using downward closure, and normalises by the (positive)
  separating constant.
* `recipe_orth_orth`: the calculus of every formula is biorthogonally closed.
* `recipe_tens`, `recipe_wth`: if the calculus equals the PCS at `A` and at `B`, it does at
  `A ⊗ B` and at `A & B`.
* `recipe_lolli_base`, `recipe_core`: no gap at `n ⊸ m` and at `(n ⊸ m) ⊗ (n' ⊸ m')`.
* `P_neg_tens_eq`: then `P (A ⊗ B)^⊥` is cut out by the products of `{0,1}`-valued elements.
-/
import ConstructiveProb.Retract

open scoped ENNReal
open Finset

namespace ConstructiveProb.Linear

open ConstructiveProb.PCS (orth pairing subset_orth_orth orth_orth_orth Mix_subset_orth)
open Fm

section Bipolar

variable {E : Type} [Fintype E] [DecidableEq E]

theorem orth_antitone {S T : Set (E → ℝ≥0∞)} (h : S ⊆ T) : orth T ⊆ orth S :=
  fun _ hy x hx => hy x (h hx)

/-- **Bipolar theorem for downward-closed sets of `{0,1}`-vectors.** -/
theorem orth_orth_subset_Mix {S : Set (E → ℝ≥0∞)} (hSf : S.Finite)
    (hS : ∀ s ∈ S, ConstructiveProb.IsSharpVec s) (h0 : (0 : E → ℝ≥0∞) ∈ S)
    (hdown : ∀ s ∈ S, ∀ t : E → ℝ≥0∞, ConstructiveProb.IsSharpVec t → t ≤ s → t ∈ S) :
    orth (orth S) ⊆ ConstructiveProb.Mix S := by
  classical
  intro x hx
  have sfin : ∀ s ∈ S, ∀ e, s e ≠ ⊤ := fun s hs e => by
    rcases hS s hs e with h | h <;> simp [h]
  -- `x` is at most `1` at every point
  have hx1 : ∀ e, x e ≤ 1 := by
    intro e
    have hδ : (Pi.single e 1 : E → ℝ≥0∞) ∈ orth S := by
      intro s hs
      rw [pairing_single']
      rcases hS s hs e with h | h <;> simp [h]
    have := hx _ hδ
    rwa [pairing_single] at this
  have hfin : ∀ e, x e ≠ ⊤ := fun e => ne_top_of_le_ne_top ENNReal.one_ne_top (hx1 e)
  let R : (E → ℝ≥0∞) → (E → ℝ) := fun y e => (y e).toReal
  by_contra hnot
  have hout : R x ∉ convexHull ℝ (R '' S) := by
    intro hin
    obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hin
    choose t ht htz using hz
    apply hnot
    have hx_eq : x = ∑ i, ENNReal.ofReal (w i) • t i := by
      funext e
      have := congrFun hsum e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← htz, R] at this ⊢
      rw [← ENNReal.ofReal_toReal (hfin e), ← this,
        ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hw0 i) ENNReal.toReal_nonneg]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_mul (hw0 i), ENNReal.ofReal_toReal (sfin _ (ht i) e)]
    rw [hx_eq]
    refine ConstructiveProb.mem_Mix_of_fintype _ _ ht ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw0 i, hw1, ENNReal.ofReal_one]
  have hconv : Convex ℝ (convexHull ℝ (R '' S)) := convex_convexHull ℝ _
  have hclosed : IsClosed (convexHull ℝ (R '' S)) :=
    ((hSf.image R).isCompact_convexHull ℝ).isClosed
  obtain ⟨f, u, hfx, hfS⟩ := geometric_hahn_banach_point_closed hconv hclosed hout
  -- `c = -f` in coordinates: `∑ c s < β < ∑ c x` with `β = -u`
  let c : E → ℝ := fun e => -f (Pi.single e 1)
  have hf : ∀ y : E → ℝ, f y = -∑ e, c e * y e := by
    intro y
    conv_lhs => rw [show y = ∑ e, y e • (Pi.single e (1 : ℝ) : E → ℝ) by
      funext e'; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, c, mul_comm]
  have hcS : ∀ s ∈ S, ∑ e, c e * (R s) e < -u := fun s hs => by
    have := hfS (R s) (subset_convexHull ℝ _ ⟨s, hs, rfl⟩); rw [hf] at this; linarith
  have hcx : -u < ∑ e, c e * (R x) e := by rw [hf] at hfx; linarith
  have hβ : 0 < -u := by
    have := hcS 0 h0; simpa [R] using this
  -- drop the negative coefficients
  let cp : E → ℝ := fun e => max (c e) 0
  have hcp0 : ∀ e, 0 ≤ cp e := fun e => le_max_right _ _
  have hcpS : ∀ s ∈ S, ∑ e, cp e * (R s) e < -u := by
    intro s hs
    let s' : E → ℝ≥0∞ := fun e => if 0 < c e then s e else 0
    have hs' : s' ∈ S := hdown s hs s' (fun e => by
      simp only [s']; split_ifs
      · exact hS s hs e
      · exact Or.inl rfl) (fun e => by simp only [s']; split_ifs <;> simp)
    have := hcS s' hs'
    calc ∑ e, cp e * (R s) e = ∑ e, c e * (R s') e := by
          refine Finset.sum_congr rfl fun e _ => ?_
          simp only [cp, R, s']
          split_ifs with h
          · rw [max_eq_left h.le]
          · rw [max_eq_right (not_lt.1 h)]; simp
      _ < -u := this
  have hcpx : -u < ∑ e, cp e * (R x) e :=
    lt_of_lt_of_le hcx (Finset.sum_le_sum fun e _ =>
      mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
  -- the functional `cp / β` is orthogonal to `S` but pairs with `x` above `1`
  let g : E → ℝ≥0∞ := fun e => ENNReal.ofReal (cp e / -u)
  have hpair : ∀ y : E → ℝ≥0∞, (∀ e, y e ≠ ⊤) →
      pairing y g = ENNReal.ofReal ((∑ e, cp e * (R y) e) / -u) := by
    intro y hy
    have key : ∀ e, y e * g e = ENNReal.ofReal (cp e * (R y) e / -u) := by
      intro e
      have hye : y e = ENNReal.ofReal ((y e).toReal) := (ENNReal.ofReal_toReal (hy e)).symm
      calc y e * g e = ENNReal.ofReal ((y e).toReal) * ENNReal.ofReal (cp e / -u) := by
            rw [← hye]
        _ = ENNReal.ofReal ((y e).toReal * (cp e / -u)) :=
            (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
        _ = ENNReal.ofReal (cp e * (R y) e / -u) := by congr 1; simp only [R]; ring
    simp only [pairing, key, Finset.sum_div]
    rw [ENNReal.ofReal_sum_of_nonneg fun e _ =>
      div_nonneg (mul_nonneg (hcp0 e) ENNReal.toReal_nonneg) hβ.le]
  have hg : g ∈ orth S := by
    intro s hs
    rw [hpair s (sfin s hs)]
    exact ENNReal.ofReal_le_one.2 ((div_le_one hβ).2 (hcpS s hs).le)
  have hxg := hx g hg
  rw [pairing_comm', hpair x hfin] at hxg
  have h1 : 1 < (∑ e, cp e * (R x) e) / -u := (one_lt_div hβ).2 hcpx
  have h2 : (1 : ℝ≥0∞) < ENNReal.ofReal ((∑ e, cp e * (R x) e) / -u) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans one_pos h1)).2 h1
  exact absurd hxg (not_le.2 h2)

theorem mem_Mix_self {S : Set (E → ℝ≥0∞)} {s : E → ℝ≥0∞} (hs : s ∈ S) :
    s ∈ ConstructiveProb.Mix S := by
  have := ConstructiveProb.mem_Mix_of_fintype (S := S) (fun _ : Unit => (1 : ℝ≥0∞)) (fun _ => s)
    (fun _ => hs) (by simp)
  simpa using this

theorem orth_Mix (S : Set (E → ℝ≥0∞)) : orth (ConstructiveProb.Mix S) = orth S := by
  apply le_antisymm (orth_antitone fun s hs => mem_Mix_self hs)
  intro f hf
  have : ConstructiveProb.Mix S ⊆ orth {f} := Mix_subset_orth fun s hs g hg => by
    rw [Set.mem_singleton_iff.1 hg, pairing_comm']; exact hf s hs
  exact fun m hm => by rw [pairing_comm']; exact this hm f rfl

end Bipolar

/-! ### The calculus is biorthogonally closed -/

/-- The `{0,1}`-valued elements of `P A`. -/
def sharpP (A : Fm) : Set (web A → ℝ≥0∞) := {z | z ∈ P A ∧ ∀ s, z s = 0 ∨ z s = 1}

theorem recipe_orth_orth (A : Fm) : orth (orth (recipe A)) = recipe A := by
  apply le_antisymm _ (subset_orth_orth _)
  rw [recipe, orth_Mix]
  exact orth_orth_subset_Mix (ConstructiveProb.finite_of_sharp fun s hs => hs.2) (fun s hs => hs.2)
    ⟨zero_mem_P A, fun _ => Or.inl rfl⟩
    (fun s hs t ht hts => ⟨P_downward A hs.1 hts, ht⟩)

/-! ### Closure under `⊗` and `&` -/

theorem tvec_sharp {X Y : Type} {s : X → ℝ≥0∞} {t : Y → ℝ≥0∞}
    (hs : ∀ a, s a = 0 ∨ s a = 1) (ht : ∀ b, t b = 0 ∨ t b = 1) :
    ∀ p, tvec s t p = 0 ∨ tvec s t p = 1 := by
  rintro ⟨a, b⟩
  rcases hs a with h | h <;> rcases ht b with h' | h' <;> simp [tvec, h, h']

theorem tvec_mem_P {A B : Fm} {x : web A → ℝ≥0∞} {y : web B → ℝ≥0∞} (hx : x ∈ P A)
    (hy : y ∈ P B) : tvec x y ∈ P (tens A B) :=
  subset_orth_orth _ ⟨x, hx, y, hy, rfl⟩

theorem tvec_sum {X Y : Type} [Fintype X] [Fintype Y] {m n : ℕ} (w : Fin m → ℝ≥0∞)
    (s : Fin m → X → ℝ≥0∞) (v : Fin n → ℝ≥0∞) (t : Fin n → Y → ℝ≥0∞) :
    tvec (∑ i, w i • s i) (∑ j, v j • t j)
      = ∑ ij : Fin m × Fin n, (w ij.1 * v ij.2) • tvec (s ij.1) (t ij.2) := by
  funext ⟨a, b⟩
  simp only [tvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **No gap at `A ⊗ B`.** -/
theorem recipe_tens {A B : Fm} (hA : recipe A = P A) (hB : recipe B = P B) :
    recipe (tens A B) = P (tens A B) := by
  apply le_antisymm (recipe_subset_P _)
  show orth (orth {z | ∃ x ∈ P A, ∃ y ∈ P B, z = tvec x y}) ⊆ recipe (tens A B)
  rw [← recipe_orth_orth (tens A B)]
  refine orth_antitone (orth_antitone ?_)
  rintro _ ⟨x, hx, y, hy, rfl⟩
  rw [← hA] at hx; rw [← hB] at hy
  obtain ⟨m, w, s, hs, hw, rfl⟩ := hx
  obtain ⟨n, v, t, ht, hv, rfl⟩ := hy
  rw [tvec_sum]
  refine ConstructiveProb.mem_Mix_of_fintype _ _ (fun ij =>
    ⟨tvec_mem_P (hs ij.1).1 (ht ij.2).1, tvec_sharp (hs ij.1).2 (ht ij.2).2⟩) ?_
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, hv, mul_one, hw]

/-- The pairing of two vectors on the summands, as a vector on `A ⊕ B`. -/
def svec' {X Y : Type} (x : X → ℝ≥0∞) (y : Y → ℝ≥0∞) : X ⊕ Y → ℝ≥0∞
  | Sum.inl a => x a
  | Sum.inr b => y b

/-- **No gap at `A & B`.** -/
theorem recipe_wth {A B : Fm} (hA : recipe A = P A) (hB : recipe B = P B) :
    recipe (wth A B) = P (wth A B) := by
  apply le_antisymm (recipe_subset_P _)
  intro z hz
  have hx := hz.1; have hy := hz.2
  rw [← hA] at hx; rw [← hB] at hy
  obtain ⟨m, w, s, hs, hw, hxe⟩ := hx
  obtain ⟨n, v, t, ht, hv, hye⟩ := hy
  have hz' : z = ∑ ij : Fin m × Fin n, (w ij.1 * v ij.2) • svec' (s ij.1) (t ij.2) := by
    funext p
    rcases p with a | b
    · have := congrFun hxe a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [this, Fintype.sum_prod_type]
      simp only [svec']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum, hv, mul_one]
    · have := congrFun hye b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [this, Fintype.sum_prod_type, Finset.sum_comm]
      simp only [svec']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul, ← Finset.sum_mul, hw, one_mul]
  rw [hz']
  refine ConstructiveProb.mem_Mix_of_fintype _ _ (fun ij => ⟨⟨?_, ?_⟩, ?_⟩) ?_
  · exact (hs ij.1).1
  · exact (ht ij.2).1
  · rintro (a | b)
    · exact (hs ij.1).2 a
    · exact (ht ij.2).2 b
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hv, mul_one, hw]

theorem Mix_mono' {E : Type} {S T : Set (E → ℝ≥0∞)} (h : S ⊆ T) :
    ConstructiveProb.Mix S ⊆ ConstructiveProb.Mix T :=
  fun _ ⟨n, w, s, hs, hw, he⟩ => ⟨n, w, s, fun i => h (hs i), hw, he⟩

/-- **No gap at first order**, as an equation for formulas. -/
theorem recipe_lolli_base (n m : ℕ) :
    recipe (lolli (base n) (base m)) = P (lolli (base n) (base m)) := by
  apply le_antisymm (recipe_subset_P _)
  have hP := recipe_first_order n m
  intro x hx
  rw [hP] at hx
  show x ∈ ConstructiveProb.Mix {z | z ∈ P (lolli (base n) (base m)) ∧ ∀ s, z s = 0 ∨ z s = 1}
  rw [← ConstructiveProb.Mix_Mix]
  refine Mix_mono' (fun z hz => ?_) hx
  obtain ⟨f, rfl⟩ := hz
  refine mem_Mix_self ⟨hP ▸ mem_Mix_self ⟨f, rfl⟩, fun p => ?_⟩
  simp only [ConstructiveProb.PCS.det]
  split_ifs <;> simp

/-- **No gap at the core** `(n ⊸ m) ⊗ (n' ⊸ m')`. -/
theorem recipe_core (n m n' m' : ℕ) : recipe (core n m n' m') = P (core n m n' m') :=
  recipe_tens (recipe_lolli_base n m) (recipe_lolli_base n' m')

/-- **The dual of a tensor is cut out by `{0,1}`-valued rectangles.** If the calculus equals the
PCS at `A` and at `B`, then `z ∈ P (A ⊗ B)^⊥` iff `z` pairs to at most `1` with `s ⊗ t` for all
`{0,1}`-valued `s ∈ P A`, `t ∈ P B`. -/
theorem P_neg_tens_eq {A B : Fm} (hA : recipe A = P A) (hB : recipe B = P B) :
    P (Fm.neg (tens A B)) = orth {z | ∃ s ∈ sharpP A, ∃ t ∈ sharpP B, z = tvec s t} := by
  show orth (orth (orth {z | ∃ x ∈ P A, ∃ y ∈ P B, z = tvec x y})) = _
  rw [orth_orth_orth]
  apply le_antisymm
  · exact orth_antitone fun _ ⟨s, hs, t, ht, h⟩ => ⟨s, hs.1, t, ht.1, h⟩
  · -- every product is a mixture of `{0,1}`-valued rectangles
    have hsub : {z | ∃ x ∈ P A, ∃ y ∈ P B, z = tvec x y} ⊆
        ConstructiveProb.Mix {z | ∃ s ∈ sharpP A, ∃ t ∈ sharpP B, z = tvec s t} := by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      rw [← hA] at hx; rw [← hB] at hy
      obtain ⟨m, w, s, hs, hw, rfl⟩ := hx
      obtain ⟨n, v, t, ht, hv, rfl⟩ := hy
      rw [tvec_sum]
      refine ConstructiveProb.mem_Mix_of_fintype _ _ (fun ij => ⟨s ij.1, hs ij.1, t ij.2, ht ij.2,
        rfl⟩) ?_
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, hv, mul_one, hw]
    rw [← orth_Mix]
    exact orth_antitone hsub

end ConstructiveProb.Linear
