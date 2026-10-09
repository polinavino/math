/-
# Cographs and forests from additive formulas: basic definitions

* `PMix`: finite convex mixtures with positive real weights, closed under mixing (`PMix_bind`),
  products (`PMix_prod`) and linear maps (`PMix_map`).
* `ACode`: formulas built from `1` with `&` and `⊕`. Their coherence graphs are the cographs.
  `ω a v` is the largest weight of a clique (`ω_attain`, `clique_le_ω`): a sum for `&`, a
  maximum for `⊕`.
* `TCode`: formulas built from `1` with `⊕` and `X & 1`. Their coherence graphs are the
  comparability graphs of rooted forests, the root of `X & 1` being the point of `1`.
  `PathSums t y` is the set of sums of `y` along the paths from a root.
-/
import ConstructiveProb.Closure

open Finset

namespace ConstructiveProb.Cograph

/-! ### Mixtures with positive weights -/

section PMix

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Finite convex mixtures with positive weights. -/
def PMix (S : Set E) : Set E :=
  {x | ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (s : ι → E),
    (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ (∀ i, s i ∈ S) ∧ x = ∑ i, w i • s i}

theorem mem_PMix_self {S : Set E} {s : E} (hs : s ∈ S) : s ∈ PMix S :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => s, fun _ => one_pos, by simp, fun _ => hs, by simp⟩

theorem PMix_mono {S T : Set E} (h : S ⊆ T) : PMix S ⊆ PMix T := by
  rintro x ⟨ι, _, w, s, hw, h1, hs, rfl⟩
  exact ⟨ι, inferInstance, w, s, hw, h1, fun i => h (hs i), rfl⟩

theorem sum_pos_part {κ : Type} [Fintype κ] (v : κ → ℝ) (hv : ∀ k, 0 ≤ v k) (f : κ → E) :
    ∑ k : {k // 0 < v k}, v k • f k = ∑ k, v k • f k := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => 0 < v k) (fun k => v k • f k)]
  have : ∑ k : {k // ¬ 0 < v k}, v k • f k = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [show v k = 0 from le_antisymm (not_lt.1 k.2) (hv k), zero_smul]
  rw [this, add_zero]

theorem sum_pos_part' {κ : Type} [Fintype κ] (v : κ → ℝ) (hv : ∀ k, 0 ≤ v k) :
    ∑ k : {k // 0 < v k}, v k = ∑ k, v k := by
  have := sum_pos_part (E := ℝ) v hv (fun _ => 1)
  simpa using this

/-- **Mixtures of mixtures.** Nonnegative weights; components of weight `0` are ignored. -/
theorem PMix_bind {S : Set E} {κ : Type} [Fintype κ] (v : κ → ℝ) (x : κ → E)
    (hv : ∀ k, 0 ≤ v k) (h1 : ∑ k, v k = 1) (hx : ∀ k, 0 < v k → x k ∈ PMix S) :
    ∑ k, v k • x k ∈ PMix S := by
  classical
  have hx' : ∀ k : {k // 0 < v k}, ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (s : ι → E),
      (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ (∀ i, s i ∈ S) ∧ x k = ∑ i, w i • s i :=
    fun k => hx k.1 k.2
  choose ι hι w s hw hw1 hs hxe using hx'
  refine ⟨Σ k : {k // 0 < v k}, ι k, inferInstance, fun p => v p.1 * w p.1 p.2,
    fun p => s p.1 p.2, fun p => mul_pos p.1.2 (hw _ _), ?_, fun p => hs _ _, ?_⟩
  · rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum, hw1, mul_one]
    rw [sum_pos_part' v hv, h1]
  · rw [Fintype.sum_sigma, ← sum_pos_part v hv x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hxe k, Finset.smul_sum]
    simp only [smul_smul]

/-- A convex combination of two mixtures. -/
theorem PMix_combo {S : Set E} {x y : E} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : 0 < t → x ∈ PMix S) (hy : t < 1 → y ∈ PMix S) : t • x + (1 - t) • y ∈ PMix S := by
  have := PMix_bind (S := S) (κ := Bool) (fun b => if b then t else 1 - t)
    (fun b => if b then x else y) (fun b => by cases b <;> simp <;> linarith)
    (by simp) (fun b hb => by cases b <;> simp at hb ⊢ <;> [exact hy (by linarith); exact hx hb])
  simpa [add_comm] using this

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

theorem PMix_prod {S : Set E} {T : Set F} {x : E} {y : F} (hx : x ∈ PMix S) (hy : y ∈ PMix T) :
    (x, y) ∈ PMix (S ×ˢ T) := by
  obtain ⟨ι, _, w, s, hw, hw1, hs, rfl⟩ := hx
  obtain ⟨κ, _, v, u, hv, hv1, hu, rfl⟩ := hy
  refine ⟨ι × κ, inferInstance, fun p => w p.1 * v p.2, fun p => (s p.1, u p.2),
    fun p => mul_pos (hw _) (hv _), ?_, fun p => ⟨hs _, hu _⟩, ?_⟩
  · rw [Fintype.sum_prod_type]; simp only [← Finset.mul_sum, hv1, mul_one, hw1]
  · rw [Fintype.sum_prod_type]
    ext
    · simp only [Prod.fst_sum, Prod.smul_fst]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_smul]
      simp only [← Finset.mul_sum, hv1, mul_one]
    · simp only [Prod.snd_sum, Prod.smul_snd]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_smul]
      simp only [mul_comm (w _) (v j), ← Finset.mul_sum, hw1, mul_one]

theorem PMix_map (f : E →ₗ[ℝ] F) {S : Set E} {x : E} (hx : x ∈ PMix S) : f x ∈ PMix (f '' S) := by
  obtain ⟨ι, _, w, s, hw, hw1, hs, rfl⟩ := hx
  exact ⟨ι, inferInstance, w, fun i => f (s i), hw, hw1, fun i => ⟨s i, hs i, rfl⟩,
    by simp [map_sum, map_smul]⟩

theorem PMix_image_subset (f : E →ₗ[ℝ] F) {S : Set E} {T : Set F} (h : f '' S ⊆ T) {x : E}
    (hx : x ∈ PMix S) : f x ∈ PMix T :=
  PMix_mono h (PMix_map f hx)

end PMix

/-! ### Additive codes -/

open ConstructiveProb.Linear (Fm web)

/-- Formulas built from `1` with `&` and `⊕`. -/
inductive ACode
  | one
  | wth (a b : ACode)
  | plus (a b : ACode)

namespace ACode

/-- The formula of a code. -/
def toFm : ACode → Fm
  | one => Fm.base 1
  | wth a b => Fm.wth a.toFm b.toFm
  | plus a b => Fm.plus a.toFm b.toFm

/-- The web of a code. -/
abbrev W (a : ACode) : Type := web a.toFm

instance : Unique (W one) := inferInstanceAs (Unique (Fin 1))

/-- The point of `1`. -/
def pt : W one := (0 : Fin 1)

theorem sum_wth {M : Type*} [AddCommMonoid M] (a b : ACode) (f : W (wth a b) → M) :
    ∑ x, f x = ∑ x, f (Sum.inl x) + ∑ x, f (Sum.inr x) :=
  Fintype.sum_sum_type (α₁ := W a) (α₂ := W b) f

theorem sum_plus {M : Type*} [AddCommMonoid M] (a b : ACode) (f : W (plus a b) → M) :
    ∑ x, f x = ∑ x, f (Sum.inl x) + ∑ x, f (Sum.inr x) :=
  Fintype.sum_sum_type (α₁ := W a) (α₂ := W b) f

theorem sum_one {M : Type*} [AddCommMonoid M] (f : W one → M) : ∑ x, f x = f pt := by
  rw [Fintype.sum_unique]; rfl

theorem eq_pt (x : W one) : x = pt := Subsingleton.elim (α := Fin 1) x pt

/-- The largest weight of a clique. -/
noncomputable def ω : (a : ACode) → (W a → ℝ) → ℝ
  | one, v => v pt
  | wth a b, v => ω a (fun x => v (Sum.inl x)) + ω b (fun x => v (Sum.inr x))
  | plus a b, v => max (ω a (fun x => v (Sum.inl x))) (ω b (fun x => v (Sum.inr x)))

/-- Coherence of a code (reflexive). -/
def coh : (a : ACode) → W a → W a → Prop
  | one, _, _ => True
  | wth a _, Sum.inl x, Sum.inl y => coh a x y
  | wth _ b, Sum.inr x, Sum.inr y => coh b x y
  | wth _ _, Sum.inl _, Sum.inr _ => True
  | wth _ _, Sum.inr _, Sum.inl _ => True
  | plus a _, Sum.inl x, Sum.inl y => coh a x y
  | plus _ b, Sum.inr x, Sum.inr y => coh b x y
  | plus _ _, Sum.inl _, Sum.inr _ => False
  | plus _ _, Sum.inr _, Sum.inl _ => False

theorem coh_refl : ∀ (a : ACode) (x : W a), coh a x x
  | one, _ => by simp [coh]
  | wth a _, Sum.inl x => coh_refl a x
  | wth _ b, Sum.inr x => coh_refl b x
  | plus a _, Sum.inl x => coh_refl a x
  | plus _ b, Sum.inr x => coh_refl b x

theorem coh_toFm : ∀ (a : ACode) (x y : W a), ConstructiveProb.Linear.coh a.toFm x y ↔ coh a x y
  | one, x, y => by
    simp only [toFm, ConstructiveProb.Linear.coh, coh, iff_true]
    exact Subsingleton.elim (α := Fin 1) x y
  | wth a b, Sum.inl x, Sum.inl y => coh_toFm a x y
  | wth a b, Sum.inr x, Sum.inr y => coh_toFm b x y
  | wth a b, Sum.inl x, Sum.inr y => by simp [toFm, ConstructiveProb.Linear.coh, coh]
  | wth a b, Sum.inr x, Sum.inl y => by simp [toFm, ConstructiveProb.Linear.coh, coh]
  | plus a b, Sum.inl x, Sum.inl y => by
    simp only [toFm, Fm.plus, ConstructiveProb.Linear.coh, coh]
    rw [← coh_toFm a x y]
    constructor
    · rintro (h | h)
      · cases h; exact ConstructiveProb.Linear.coh_refl _ _
      · by_contra hc
        exact h (Or.inr hc)
    · intro h
      by_cases hxy : x = y
      · exact Or.inl (by rw [hxy])
      · right; rintro (h' | h')
        · exact hxy h'
        · exact h' h
  | plus a b, Sum.inr x, Sum.inr y => by
    simp only [toFm, Fm.plus, ConstructiveProb.Linear.coh, coh]
    rw [← coh_toFm b x y]
    constructor
    · rintro (h | h)
      · cases h; exact ConstructiveProb.Linear.coh_refl _ _
      · by_contra hc
        exact h (Or.inr hc)
    · intro h
      by_cases hxy : x = y
      · exact Or.inl (by rw [hxy])
      · right; rintro (h' | h')
        · exact hxy h'
        · exact h' h
  | plus a b, Sum.inl x, Sum.inr y => by
    simp [toFm, Fm.plus, ConstructiveProb.Linear.coh, coh]
  | plus a b, Sum.inr x, Sum.inl y => by
    simp [toFm, Fm.plus, ConstructiveProb.Linear.coh, coh]

/-- The indicator of a clique. -/
def IsClique (a : ACode) (c : W a → ℝ) : Prop :=
  (∀ x, c x = 0 ∨ c x = 1) ∧ ∀ x y, c x = 1 → c y = 1 → coh a x y

theorem ω_mono : ∀ (a : ACode) {v w : W a → ℝ}, v ≤ w → ω a v ≤ ω a w
  | one, v, w, h => h pt
  | wth a b, v, w, h => add_le_add (ω_mono a fun x => h _) (ω_mono b fun x => h _)
  | plus a b, v, w, h => max_le_max (ω_mono a fun x => h _) (ω_mono b fun x => h _)

theorem ω_zero : ∀ a : ACode, ω a 0 = 0
  | one => rfl
  | wth a b => by
    show ω a 0 + ω b 0 = 0
    rw [ω_zero a, ω_zero b, add_zero]
  | plus a b => by
    show max (ω a 0) (ω b 0) = 0
    rw [ω_zero a, ω_zero b, max_self]

theorem ω_smul : ∀ (a : ACode) {c : ℝ} (v : W a → ℝ), 0 ≤ c → ω a (c • v) = c * ω a v
  | one, c, v, _ => rfl
  | wth a b, c, v, hc => by
    show ω a (c • fun x => v (Sum.inl x)) + ω b (c • fun x => v (Sum.inr x)) = _
    rw [ω_smul a _ hc, ω_smul b _ hc]
    show _ = c * (ω a _ + ω b _)
    rw [mul_add]
  | plus a b, c, v, hc => by
    show max (ω a (c • fun x => v (Sum.inl x))) (ω b (c • fun x => v (Sum.inr x))) = _
    rw [ω_smul a _ hc, ω_smul b _ hc]
    show _ = c * max (ω a _) (ω b _)
    rw [mul_max_of_nonneg _ _ hc]

theorem ω_nonneg (a : ACode) {v : W a → ℝ} (hv : 0 ≤ v) : 0 ≤ ω a v := by
  have := ω_mono a hv; rwa [ω_zero] at this

/-- **The weight of a clique is at most `ω`.** -/
theorem clique_le_ω : ∀ (a : ACode) {v : W a → ℝ}, 0 ≤ v → ∀ c : W a → ℝ, IsClique a c →
    ∑ x, c x * v x ≤ ω a v
  | one, v, hv, c, hc => by
    rw [sum_one]
    show c pt * v pt ≤ v pt
    rcases hc.1 pt with h | h <;> rw [h]
    · simp; exact hv pt
    · simp
  | wth a b, v, hv, c, hc => by
    rw [sum_wth]
    exact add_le_add
      (clique_le_ω a (fun x => hv _) (fun x => c (Sum.inl x))
        ⟨fun x => hc.1 _, fun x y hx hy => hc.2 _ _ hx hy⟩)
      (clique_le_ω b (fun x => hv _) (fun x => c (Sum.inr x))
        ⟨fun x => hc.1 _, fun x y hx hy => hc.2 _ _ hx hy⟩)
  | plus a b, v, hv, c, hc => by
    rw [sum_plus]
    have ha := clique_le_ω a (v := fun x => v (Sum.inl x)) (fun x => hv (Sum.inl x))
        (fun x => c (Sum.inl x)) ⟨fun x => hc.1 _, fun x y hx hy => hc.2 _ _ hx hy⟩
    have hb := clique_le_ω b (v := fun x => v (Sum.inr x)) (fun x => hv (Sum.inr x))
        (fun x => c (Sum.inr x)) ⟨fun x => hc.1 _, fun x y hx hy => hc.2 _ _ hx hy⟩
    by_cases hA : ∃ x, c (Sum.inl x) = 1
    · obtain ⟨x0, hx0⟩ := hA
      have hB : ∀ y, c (Sum.inr y) = 0 := fun y => by
        rcases hc.1 (Sum.inr y) with h | h
        · exact h
        · exact absurd (hc.2 _ _ hx0 h) (by simp [coh])
      have : ∑ x, c (Sum.inr x) * v (Sum.inr x) = 0 :=
        Finset.sum_eq_zero fun y _ => by rw [hB y, zero_mul]
      rw [this, add_zero]
      exact le_trans ha (le_max_left _ _)
    · push_neg at hA
      have hA' : ∀ x, c (Sum.inl x) = 0 := fun x => (hc.1 _).resolve_right (hA x)
      have : ∑ x, c (Sum.inl x) * v (Sum.inl x) = 0 :=
        Finset.sum_eq_zero fun y _ => by rw [hA' y, zero_mul]
      rw [this, zero_add]
      exact le_trans hb (le_max_right _ _)

/-- **`ω` is attained by a clique.** -/
theorem ω_attain : ∀ (a : ACode) (v : W a → ℝ), ∃ c : W a → ℝ, IsClique a c ∧
    ω a v = ∑ x, c x * v x
  | one, v => ⟨fun _ => 1, ⟨fun _ => Or.inr rfl, fun _ _ _ _ => trivial⟩, by
      rw [sum_one]; simp; rfl⟩
  | wth a b, v => by
    obtain ⟨ca, hca, ha⟩ := ω_attain a (fun x => v (Sum.inl x))
    obtain ⟨cb, hcb, hb⟩ := ω_attain b (fun x => v (Sum.inr x))
    refine ⟨fun x => match x with | Sum.inl x => ca x | Sum.inr x => cb x, ⟨?_, ?_⟩, ?_⟩
    · rintro (x | x)
      · exact hca.1 x
      · exact hcb.1 x
    · rintro (x | x) (y | y) hx hy
      · exact hca.2 x y hx hy
      · trivial
      · trivial
      · exact hcb.2 x y hx hy
    · show ω a _ + ω b _ = _
      rw [ha, hb, sum_wth]
  | plus a b, v => by
    obtain ⟨ca, hca, ha⟩ := ω_attain a (fun x => v (Sum.inl x))
    obtain ⟨cb, hcb, hb⟩ := ω_attain b (fun x => v (Sum.inr x))
    rcases le_total (ω a (fun x => v (Sum.inl x))) (ω b (fun x => v (Sum.inr x))) with h | h
    · refine ⟨fun x => match x with | Sum.inl _ => 0 | Sum.inr x => cb x, ⟨?_, ?_⟩, ?_⟩
      · rintro (x | x)
        · exact Or.inl rfl
        · exact hcb.1 x
      · rintro (x | x) (y | y) hx hy
        · exact absurd hx (by simp)
        · exact absurd hx (by simp)
        · exact absurd hy (by simp)
        · exact hcb.2 x y hx hy
      · show max _ _ = _
        rw [max_eq_right h, hb, sum_plus]
        simp
    · refine ⟨fun x => match x with | Sum.inl x => ca x | Sum.inr _ => 0, ⟨?_, ?_⟩, ?_⟩
      · rintro (x | x)
        · exact hca.1 x
        · exact Or.inl rfl
      · rintro (x | x) (y | y) hx hy
        · exact hca.2 x y hx hy
        · exact absurd hy (by simp)
        · exact absurd hx (by simp)
        · exact absurd hx (by simp)
      · show max _ _ = _
        rw [max_eq_left h, ha, sum_plus]
        simp

theorem coord_le_ω (a : ACode) {v : W a → ℝ} (hv : 0 ≤ v) (x : W a) : v x ≤ ω a v := by
  classical
  have := clique_le_ω a hv (fun y => if y = x then 1 else 0)
    ⟨fun y => by by_cases h : y = x <;> simp [h], fun y z hy hz => by
      by_cases h1 : y = x <;> by_cases h2 : z = x <;> simp [h1, h2] at hy hz
      subst h1; subst h2; exact coh_refl a _⟩
  simpa using this

theorem pair_le_ω (a : ACode) {v : W a → ℝ} (hv : 0 ≤ v) {x y : W a} (hxy : x ≠ y)
    (h : coh a x y) : v x + v y ≤ ω a v := by
  classical
  have hyx : coh a y x := by
    have := (coh_toFm a x y).2 h
    exact (coh_toFm a y x).1 (ConstructiveProb.Linear.coh_symm _ this)
  have := clique_le_ω a hv (fun z => if z = x ∨ z = y then 1 else 0)
    ⟨fun z => by by_cases h : z = x ∨ z = y <;> simp [h], fun u w hu hw => by
      simp only [ite_eq_left_iff, not_or, zero_ne_one, imp_false, not_and, not_not] at hu hw
      by_cases hux : u = x <;> by_cases hwx : w = x
      · subst hux; subst hwx; exact coh_refl a _
      · subst hux; rw [hw hwx]; exact h
      · subst hwx; rw [hu hux]; exact hyx
      · rw [hu hux, hw hwx]; exact coh_refl a _⟩
  have hs : ∑ z, (if z = x ∨ z = y then (1 : ℝ) else 0) * v z = v x + v y := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [show (univ.filter fun z => z = x ∨ z = y) = {x, y} by ext z; simp]
    exact Finset.sum_pair hxy
  rw [hs] at this
  exact this

/-- A stable set, as a `{0,1}`-vector of `ω` at most `1`. -/
def IsStab (a : ACode) (v : W a → ℝ) : Prop := (∀ x, v x = 0 ∨ v x = 1) ∧ ω a v ≤ 1

end ACode

/-! ### Forest codes -/

/-- Formulas built from `1` with `⊕` and `X & 1`. -/
inductive TCode
  | one
  | plus (s t : TCode)
  | cone (t : TCode)

namespace TCode

/-- The additive code of a forest code. -/
def toA : TCode → ACode
  | one => ACode.one
  | plus s t => ACode.plus s.toA t.toA
  | cone t => ACode.wth t.toA ACode.one

/-- The nodes. -/
abbrev N (t : TCode) : Type := ACode.W t.toA

/-- The root of `t & 1`. -/
def root (t : TCode) : N (cone t) := Sum.inr ACode.pt

/-- The sums of `y` along the paths from a root, including the empty path. -/
def PathSums {V : Type*} [AddCommMonoid V] : (t : TCode) → (N t → V) → Set V
  | one, y => {0, y ACode.pt}
  | plus s t, y => PathSums s (fun x => y (Sum.inl x)) ∪ PathSums t (fun x => y (Sum.inr x))
  | cone t, y => insert 0 ((fun S => y (root t) + S) '' PathSums t (fun x => y (Sum.inl x)))

theorem zero_mem_PathSums {V : Type*} [AddCommMonoid V] :
    ∀ (t : TCode) (y : N t → V), (0 : V) ∈ PathSums t y
  | one, _ => Set.mem_insert _ _
  | plus s _, y => Or.inl (zero_mem_PathSums s _)
  | cone _, _ => Set.mem_insert _ _

theorem PathSums_map {V V' : Type*} [AddCommMonoid V] [AddCommMonoid V'] (f : V →+ V') :
    ∀ (t : TCode) (y : N t → V), PathSums t (fun x => f (y x)) = f '' PathSums t y
  | one, y => by simp [PathSums, Set.image_insert_eq]
  | plus s t, y => by
    simp only [PathSums, Set.image_union]
    rw [PathSums_map f s, PathSums_map f t]
  | cone t, y => by
    simp only [PathSums, Set.image_insert_eq, map_zero]
    rw [PathSums_map f t, Set.image_image, Set.image_image]
    congr 1
    exact Set.image_congr fun S _ => (map_add f _ _).symm

/-- Every node lies on a path. -/
theorem le_PathSums {α : Type*} :
    ∀ (t : TCode) (y : N t → α → ℝ), 0 ≤ y → ∀ x, ∃ S ∈ PathSums t y, y x ≤ S
  | one, y, _, x => ⟨y ACode.pt, Set.mem_insert_of_mem _ rfl, by rw [ACode.eq_pt x]⟩
  | plus s t, y, hy, Sum.inl x => by
    obtain ⟨S, hS, h⟩ := le_PathSums s (fun x => y (Sum.inl x)) (fun x => hy _) x
    exact ⟨S, Or.inl hS, h⟩
  | plus s t, y, hy, Sum.inr x => by
    obtain ⟨S, hS, h⟩ := le_PathSums t (fun x => y (Sum.inr x)) (fun x => hy _) x
    exact ⟨S, Or.inr hS, h⟩
  | cone t, y, hy, Sum.inl x => by
    obtain ⟨S, hS, h⟩ := le_PathSums t (fun x => y (Sum.inl x)) (fun x => hy _) x
    refine ⟨y (root t) + S, Set.mem_insert_of_mem _ ⟨S, hS, rfl⟩, fun a => ?_⟩
    have h1 : y (Sum.inl x) a ≤ S a := h a
    have h0 : (0 : ℝ) ≤ y (root t) a := hy (root t) a
    show y (Sum.inl x) a ≤ y (root t) a + S a
    linarith
  | cone t, y, hy, Sum.inr x => by
    refine ⟨y (root t) + 0, Set.mem_insert_of_mem _ ⟨0, zero_mem_PathSums _ _, rfl⟩, ?_⟩
    rw [add_zero, show x = ACode.pt from ACode.eq_pt x]
    rfl

theorem PathSums_nonneg {α : Type*} :
    ∀ (t : TCode) (y : N t → α → ℝ), 0 ≤ y → ∀ S ∈ PathSums t y, 0 ≤ S
  | one, y, hy, S, hS => by
    rcases hS with rfl | hS
    · exact le_rfl
    · rw [Set.mem_singleton_iff.1 hS]; exact hy _
  | plus s t, y, hy, S, hS => hS.elim (PathSums_nonneg s _ (fun x => hy _) S)
      (PathSums_nonneg t _ (fun x => hy _) S)
  | cone t, y, hy, S, hS => by
    rcases hS with rfl | ⟨S', hS', rfl⟩
    · exact le_rfl
    · exact add_nonneg (hy _) (PathSums_nonneg t _ (fun x => hy _) S' hS')

end TCode

end ConstructiveProb.Cograph
