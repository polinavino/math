/-
# The recipe: a probability calculus is the set of mixtures of certain states

One definition, `Mix S`, the finite convex mixtures of a set `S` of `ℝ≥0∞`-valued functions on
events, and its instances:

* **Frames** (`frame_recipe`): on a finite frame `LowerSet P`, the valuations are exactly
  `Mix` of the sharp (`{0,1}`-valued) valuations. Here modularity is not an axiom of the
  recipe; it is what mixing sharp valuations produces.
* **PCS, first order** (`pcs_recipe`): `flat X ⊸ flat Y` is exactly `Mix` of the deterministic
  partial programs.
* **PCS, second order** (`pcs_recipe_fails`): `(Bool ⊸ Bool) ⊸ (Bool ⊸ Bool)^⊥` is *not* `Mix`
  of its `{0,1}`-valued elements (the pentagon).

The second part checks the PCS axioms for the spaces used: each is an orthogonal `S^⊥` (hence
`P^⊥⊥ = P`), and each web point is both reachable and bounded.
-/
import ConstructiveProb.Representation
import ConstructiveProb.Sequential

open scoped ENNReal
open Finset

namespace ConstructiveProb

/-! ### The recipe -/

section Recipe

variable {E : Type*}

/-- **Finite convex mixtures** of a set `S` of states. -/
def Mix (S : Set (E → ℝ≥0∞)) : Set (E → ℝ≥0∞) :=
  {x | ∃ (n : ℕ) (w : Fin n → ℝ≥0∞) (s : Fin n → E → ℝ≥0∞),
    (∀ i, s i ∈ S) ∧ ∑ i, w i = 1 ∧ x = ∑ i, w i • s i}

/-- A mixture indexed by any finite type is in `Mix`. -/
theorem mem_Mix_of_fintype {S : Set (E → ℝ≥0∞)} {ι : Type*} [Fintype ι] (w : ι → ℝ≥0∞)
    (s : ι → E → ℝ≥0∞) (hs : ∀ i, s i ∈ S) (hw : ∑ i, w i = 1) :
    ∑ i, w i • s i ∈ Mix S := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, w ∘ e.symm, s ∘ e.symm, fun i => hs _, ?_, ?_⟩
  · rw [← hw]; exact Equiv.sum_comp e.symm w
  · exact (Equiv.sum_comp e.symm (fun i => w i • s i)).symm


/-! ### General theorems, for every logic

A *logic* here is just a set `E` of events with a set `S` of *certain states* (its two-valued
models, or deterministic programs): `{0,1}`-valued functions on `E`. The calculus is `Mix S`.
The three classical axioms are instances of one schema: an *affine law*
`∑ a e · x e + k ≤ ∑ b e · x e + k'` with nonnegative coefficients (monotonicity
`x a ≤ x b`; normalization `x ⊤ ≤ 1`, `1 ≤ x ⊤`; modularity, two opposite inequalities). -/

/-- `x` is `{0,1}`-valued: a certain state. -/
def IsSharpVec (x : E → ℝ≥0∞) : Prop := ∀ e, x e = 0 ∨ x e = 1

/-- **Criterion (1) for every logic.** The certain elements of the calculus are exactly the
certain states: mixing never manufactures a new certain state. -/
theorem sharp_mem_Mix_iff {S : Set (E → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s)
    {x : E → ℝ≥0∞} (hx : IsSharpVec x) : x ∈ Mix S ↔ x ∈ S := by
  constructor
  · rintro ⟨n, w, s, hs, hw, rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h; push_neg at h; simp [h] at hw
    have hev : ∀ e, (∑ j, w j • s j) e = ∑ j, w j * s j e := fun e => by
      simp [Finset.sum_apply]
    have hle : ∀ e, w i * s i e ≤ ∑ j, w j * s j e := fun e =>
      Finset.single_le_sum (f := fun j => w j * s j e) (fun _ _ => bot_le) (Finset.mem_univ i)
    have hwi : w i ≤ 1 := hw ▸ Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
    have hwt : w i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hwi
    suffices h : s i = ∑ j, w j • s j by rw [← h]; exact hs i
    funext e
    rw [hev]
    have hxe := hx e
    rw [hev] at hxe
    rcases hxe with h0 | h1
    · rcases hS _ (hs i) e with h | h
      · rw [h, h0]
      · have := hle e; rw [h, h0, mul_one] at this
        exact absurd (le_antisymm this bot_le) hi
    · rcases hS _ (hs i) e with h | h
      · exfalso
        have hsplit : ∑ j, w j * s j e ≤ ∑ j ∈ univ.erase i, w j := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), h, mul_zero, zero_add]
          refine Finset.sum_le_sum fun j _ => ?_
          rcases hS _ (hs j) e with h' | h' <;> simp [h']
        have htot : w i + ∑ j ∈ univ.erase i, w j = 1 := by
          rw [Finset.add_sum_erase _ _ (Finset.mem_univ i), hw]
        rw [h1] at hsplit
        have h3 : w i + 1 ≤ 1 := by
          calc w i + 1 ≤ w i + ∑ j ∈ univ.erase i, w j := by gcongr
            _ = 1 := htot
        have h4 : w i + 1 ≤ 0 + 1 := by simpa using h3
        exact hi (le_antisymm ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 h4) bot_le)
      · rw [h, h1]
  · intro hx'
    refine ⟨1, fun _ => 1, fun _ => x, fun _ => hx', by simp, ?_⟩
    simp

/-- **The calculus is closed under mixing**, for every logic: a mixture of mixtures of certain
states is a mixture of certain states. -/
theorem Mix_Mix (S : Set (E → ℝ≥0∞)) : Mix (Mix S) = Mix S := by
  ext x
  constructor
  · rintro ⟨n, w, y, hy, hw, rfl⟩
    choose m u s hs hu hys using hy
    have key : ∑ i, w i • y i = ∑ k : (Σ i, Fin (m i)), (w k.1 * u k.1 k.2) • s k.1 k.2 := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hys i, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
    rw [key]
    refine mem_Mix_of_fintype _ _ (fun k => hs k.1 k.2) ?_
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum, hu, mul_one, hw]
  · intro hx
    exact ⟨1, fun _ => 1, fun _ => x, fun _ => hx, by simp, by simp⟩

/-- An affine law with nonnegative coefficients: `∑ a e · x e + k ≤ ∑ b e · x e + k'`. -/
structure AffineLaw (E : Type*) [Fintype E] where
  a : E → ℝ≥0∞
  b : E → ℝ≥0∞
  k : ℝ≥0∞
  k' : ℝ≥0∞

/-- `x` satisfies the law. -/
def AffineLaw.Holds [Fintype E] (L : AffineLaw E) (x : E → ℝ≥0∞) : Prop :=
  ∑ e, L.a e * x e + L.k ≤ ∑ e, L.b e * x e + L.k'

/-- **Soundness, for every logic.** Every affine law valid on the certain states is valid on
the whole calculus. This is the general form of "monotonicity, normalization and modularity
hold for every valuation". -/
theorem AffineLaw.holds_of_Mix [Fintype E] (L : AffineLaw E) {S : Set (E → ℝ≥0∞)}
    (hL : ∀ s ∈ S, L.Holds s) {x : E → ℝ≥0∞} (hx : x ∈ Mix S) : L.Holds x := by
  obtain ⟨n, w, s, hs, hw, rfl⟩ := hx
  have lin : ∀ c : E → ℝ≥0∞, ∀ k : ℝ≥0∞,
      ∑ e, c e * (∑ i, w i • s i) e + k = ∑ i, w i * (∑ e, c e * s i e + k) := by
    intro c k
    have hk : ∑ i, w i * k = k := by rw [← Finset.sum_mul, hw, one_mul]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, hk]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => by ring
  unfold AffineLaw.Holds
  rw [lin, lin]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_left' (hL _ (hs i)) _


/-! ### Completeness, for every logic with finitely many events and certain states

The calculus is *exactly* what the affine laws valid on the certain states cut out. So the
right generalization of "monotonicity, normalization, modularity" to an arbitrary logic is:
all affine laws its certain states obey, and nothing else. -/

section Completeness

variable [Fintype E]

theorem ofReal_affine {y : E → ℝ≥0∞} (hy : ∀ e, y e ≠ ⊤) {c : E → ℝ} (hc : ∀ e, 0 ≤ c e)
    {k : ℝ} (hk : 0 ≤ k) :
    ∑ e, ENNReal.ofReal (c e) * y e + ENNReal.ofReal k
      = ENNReal.ofReal (∑ e, c e * (y e).toReal + k) := by
  rw [ENNReal.ofReal_add (Finset.sum_nonneg fun e _ => mul_nonneg (hc e) ENNReal.toReal_nonneg) hk,
    ENNReal.ofReal_sum_of_nonneg fun e _ => mul_nonneg (hc e) ENNReal.toReal_nonneg]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [ENNReal.ofReal_mul (hc e), ENNReal.ofReal_toReal (hy e)]

/-- **Completeness.** For a finite set `S` of certain states, a vector is a mixture of them iff
it satisfies every affine law they all satisfy. -/
theorem Mix_eq_laws {S : Set (E → ℝ≥0∞)} (hSf : S.Finite) (hS : ∀ s ∈ S, IsSharpVec s) :
    Mix S = {x | ∀ L : AffineLaw E, (∀ s ∈ S, L.Holds s) → L.Holds x} := by
  classical
  ext x
  refine ⟨fun hx L hL => L.holds_of_Mix hL hx, fun hx => ?_⟩
  -- `x` is finite: the law `x e ≤ 1` holds on certain states
  have hfin : ∀ e, x e ≠ ⊤ := by
    intro e
    have := hx ⟨Pi.single e 1, 0, 0, 1⟩ (fun s hs => by
      simp only [AffineLaw.Holds, Pi.single_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero, zero_add]
      rcases hS s hs e with h | h <;> simp [h])
    simp only [AffineLaw.Holds, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero, zero_add] at this
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (by simpa using this)
  have sfin : ∀ s ∈ S, ∀ e, s e ≠ ⊤ := fun s hs e => by
    rcases hS s hs e with h | h <;> simp [h]
  let R : (E → ℝ≥0∞) → (E → ℝ) := fun y e => (y e).toReal
  by_contra hnot
  -- the real image of `x` lies outside the convex hull of the certain states
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
    refine mem_Mix_of_fintype _ _ ht ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw0 i, hw1, ENNReal.ofReal_one]
  -- separate
  have hconv : Convex ℝ (convexHull ℝ (R '' S)) := convex_convexHull ℝ _
  have hclosed : IsClosed (convexHull ℝ (R '' S)) :=
    ((hSf.image R).isCompact_convexHull ℝ).isClosed
  obtain ⟨f, u, hfx, hfS⟩ := geometric_hahn_banach_point_closed hconv hclosed hout
  let c : E → ℝ := fun e => f (Pi.single e 1)
  have hf : ∀ y : E → ℝ, f y = ∑ e, c e * y e := by
    intro y
    conv_lhs => rw [show y = ∑ e, y e • (Pi.single e (1 : ℝ) : E → ℝ) by
      funext e'; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, c, mul_comm]
  -- the law  ∑ c⁻ y + u⁺ ≤ ∑ c⁺ y + u⁻,  i.e.  f y ≥ u
  let cp : E → ℝ := fun e => max (c e) 0
  let cn : E → ℝ := fun e => max (-c e) 0
  let L : AffineLaw E := ⟨fun e => ENNReal.ofReal (cn e), fun e => ENNReal.ofReal (cp e),
    ENNReal.ofReal (max u 0), ENNReal.ofReal (max (-u) 0)⟩
  have hsplit : ∀ y : E → ℝ, f y - u
      = (∑ e, cp e * y e + max (-u) 0) - (∑ e, cn e * y e + max u 0) := by
    intro y
    rw [hf]
    have : ∀ e, c e * y e = cp e * y e - cn e * y e := fun e => by
      simp only [cp, cn]; rcases le_total (c e) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    simp only [this, Finset.sum_sub_distrib]
    rcases le_total u 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hcp : ∀ e, 0 ≤ cp e := fun e => le_max_right _ _
  have hcn : ∀ e, 0 ≤ cn e := fun e => le_max_right _ _
  have hholds : ∀ y : E → ℝ≥0∞, (∀ e, y e ≠ ⊤) →
      (L.Holds y ↔ ∑ e, cn e * (R y) e + max u 0 ≤ ∑ e, cp e * (R y) e + max (-u) 0) := by
    intro y hy
    simp only [AffineLaw.Holds, L]
    rw [ofReal_affine hy hcn (le_max_right _ _), ofReal_affine hy hcp (le_max_right _ _)]
    exact ENNReal.ofReal_le_ofReal_iff (add_nonneg
      (Finset.sum_nonneg fun e _ => mul_nonneg (hcp e) ENNReal.toReal_nonneg) (le_max_right _ _))
  have hvalid : ∀ s ∈ S, L.Holds s := by
    intro s hs
    rw [hholds s (sfin s hs)]
    have := hfS (R s) (subset_convexHull ℝ _ ⟨s, hs, rfl⟩)
    have := hsplit (R s)
    linarith
  have hxL := (hholds x hfin).1 (hx L hvalid)
  have := hsplit (R x)
  linarith


/-- Over finitely many events there are only finitely many certain states. -/
theorem finite_of_sharp {S : Set (E → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s) : S.Finite := by
  classical
  refine (Set.finite_range (fun b : E → Bool => fun e => if b e then (1 : ℝ≥0∞) else 0)).subset ?_
  intro s hs
  refine ⟨fun e => decide (s e = 1), funext fun e => ?_⟩
  rcases hS s hs e with h | h <;> simp [h]

/-- **Completeness, without a finiteness hypothesis on the certain states.** -/
theorem Mix_eq_laws' {S : Set (E → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s) :
    Mix S = {x | ∀ L : AffineLaw E, (∀ s ∈ S, L.Holds s) → L.Holds x} :=
  Mix_eq_laws (finite_of_sharp hS) hS

end Completeness


/-! ### Infinitely many events: completeness on every finite window -/

section Local

/-- An affine law mentioning only the finitely many events in `F`. -/
structure FinLaw (E : Type*) where
  F : Finset E
  a : E → ℝ≥0∞
  b : E → ℝ≥0∞
  k : ℝ≥0∞
  k' : ℝ≥0∞

def FinLaw.Holds (L : FinLaw E) (x : E → ℝ≥0∞) : Prop :=
  ∑ e ∈ L.F, L.a e * x e + L.k ≤ ∑ e ∈ L.F, L.b e * x e + L.k'

/-- Restriction of a state to a finite window of events. -/
def restr (F : Finset E) (x : E → ℝ≥0∞) : F → ℝ≥0∞ := fun e => x e

/-- **Local completeness, for every logic.** With arbitrarily many events, a vector satisfies
every finitely supported affine law valid on the certain states iff on every finite window of
events it is a mixture of (restrictions of) certain states. -/
theorem laws_iff_local_Mix {S : Set (E → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s)
    (x : E → ℝ≥0∞) :
    (∀ L : FinLaw E, (∀ s ∈ S, L.Holds s) → L.Holds x) ↔
      ∀ F : Finset E, restr F x ∈ Mix (restr F '' S) := by
  classical
  -- a law on the window `F` and the corresponding law on `E` agree on restrictions
  let up : (F : Finset E) → AffineLaw F → FinLaw E := fun F L =>
    ⟨F, fun e => if h : e ∈ F then L.a ⟨e, h⟩ else 0, fun e => if h : e ∈ F then L.b ⟨e, h⟩ else 0,
      L.k, L.k'⟩
  have hup : ∀ (F : Finset E) (L : AffineLaw F) (y : E → ℝ≥0∞),
      (up F L).Holds y ↔ L.Holds (restr F y) := by
    intro F L y
    simp only [FinLaw.Holds, AffineLaw.Holds, up, restr]
    rw [← Finset.sum_attach F, ← Finset.sum_attach F]
    simp only [Finset.coe_mem, dif_pos]
    rfl
  have hsharp : ∀ F : Finset E, ∀ t ∈ restr F '' S, IsSharpVec t := by
    rintro F _ ⟨s, hs, rfl⟩ e; exact hS s hs e
  constructor
  · intro hx F
    rw [Mix_eq_laws' (hsharp F)]
    intro L hL
    rw [← hup]
    exact hx _ fun s hs => (hup F L s).2 (hL _ ⟨s, hs, rfl⟩)
  · intro hx L hL
    -- view `L` as a law on its own window
    let L' : AffineLaw L.F := ⟨fun e => L.a e, fun e => L.b e, L.k, L.k'⟩
    have key : ∀ y : E → ℝ≥0∞, L.Holds y ↔ L'.Holds (restr L.F y) := by
      intro y
      simp only [FinLaw.Holds, AffineLaw.Holds, L', restr]
      rw [← Finset.sum_attach L.F, ← Finset.sum_attach L.F]
      rfl
    have := hx L.F
    rw [Mix_eq_laws' (hsharp L.F)] at this
    rw [key]
    exact this L' (by rintro _ ⟨s, hs, rfl⟩; exact (key s).1 (hL s hs))

end Local

end Recipe

/-! ### Instance 1: finite frames -/

section Frame

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P]

theorem deltaPoint_isSharp (p : P) : (deltaPoint p).IsSharp := by
  intro U; by_cases h : p ∈ U <;> simp [h]

theorem Valuation.mass_zero_or_one {v : Valuation (LowerSet P)} (hv : v.IsSharp) (p : P) :
    v.mass p = 0 ∨ v.mass p = 1 := by
  unfold Valuation.mass
  rcases hv (LowerSet.Iic p) with h1 | h1 <;> rcases hv (LowerSet.Iio p) with h2 | h2 <;>
    simp [h1, h2]

/-- **Sharp valuations on a finite frame are point valuations.** -/
theorem Valuation.eq_deltaPoint_of_isSharp {v : Valuation (LowerSet P)} (hv : v.IsSharp) :
    ∃ p, v = deltaPoint p := by
  have hsum := v.sum_mass
  obtain ⟨p, hp⟩ : ∃ p, v.mass p ≠ 0 := by
    by_contra h; push_neg at h; simp [h] at hsum
  have hp1 : v.mass p = 1 := (v.mass_zero_or_one hv p).resolve_left hp
  have hq : ∀ q ≠ p, v.mass q = 0 := by
    intro q hqp
    have hle : v.mass p + v.mass q ≤ 1 := by
      rw [← hsum, ← Finset.sum_pair hqp.symm]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [hp1] at hle
    exact (v.mass_zero_or_one hv q).resolve_right fun h => by
      rw [h] at hle; norm_num at hle
  refine ⟨p, ?_⟩
  rw [v.eq_mix_deltaPoint]
  cases v with
  | mk f h0 h1 hm hmod => ?_
  simp only [Valuation.mix] at *
  congr 1
  funext U
  rw [Finset.sum_eq_single p (fun q _ hqp => by rw [hq q hqp, zero_mul])
    (fun h => absurd (Finset.mem_univ p) h), hp1, one_mul]
  rfl

/-- **The recipe on finite frames.** The valuations on `LowerSet P` are exactly the mixtures of
its sharp valuations. -/
theorem frame_recipe :
    Set.range (fun v : Valuation (LowerSet P) => v.toFun)
      = Mix {f | ∃ v : Valuation (LowerSet P), v.IsSharp ∧ f = v.toFun} := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    have h := congrArg Valuation.toFun v.eq_mix_deltaPoint
    have : v.toFun = ∑ p, v.mass p • (deltaPoint p).toFun := by
      rw [h]; funext U; simp [Valuation.mix, Finset.sum_apply]
    show v.toFun ∈ _
    rw [this]
    exact mem_Mix_of_fintype _ _ (fun p => ⟨deltaPoint p, deltaPoint_isSharp p, rfl⟩) v.sum_mass
  · rintro ⟨n, w, s, hs, hw, rfl⟩
    choose v hv hvs using hs
    refine ⟨Valuation.mix w hw v, ?_⟩
    funext U
    simp [Valuation.mix, Finset.sum_apply, hvs]

end Frame

/-! ### Instances 2 and 3: probabilistic coherence spaces -/

namespace PCS

/-- **The recipe on first-order PCS.** `flat X ⊸ flat Y` is exactly the set of mixtures of the
deterministic partial programs. -/
theorem pcs_recipe {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] :
    lin X Y = Mix (Set.range (det : (X → Option Y) → X × Y → ℝ≥0∞)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨w, hw, rfl⟩ := (mem_lin_iff_mix t).1 ht
    exact mem_Mix_of_fintype w det (fun f => ⟨f, rfl⟩) hw
  · rintro ⟨n, w, s, hs, hw, rfl⟩
    choose f hf using hs
    rw [mem_lin_iff]
    intro a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hf]
    rw [Finset.sum_comm]
    calc ∑ i, ∑ b, w i * det (f i) (a, b) = ∑ i, w i * ∑ b, det (f i) (a, b) := by
          simp [Finset.mul_sum]
      _ ≤ ∑ i, w i * 1 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_left' (det_row_le_one (f i) a) _
      _ = 1 := by simp [hw]

/-- **The recipe fails at second order.** `(Bool ⊸ Bool) ⊸ (Bool ⊸ Bool)^⊥` is not the set of
mixtures of its `{0,1}`-valued elements: the pentagon is a witness. -/
theorem pcs_recipe_fails :
    tensDual ≠ Mix {z | z ∈ tensDual ∧ ∀ pq, z pq = 0 ∨ z pq = 1} := by
  intro h
  have hm := h ▸ pentElt_mem
  obtain ⟨n, w, s, hs, hw, heq⟩ := hm
  exact pentElt_not_mix univ w hw s (fun i _ => (hs i).1) (fun i _ => (hs i).2) heq

/-! ### The PCS axioms for `flat`, `lin` and `tensDual` -/

section Axioms

variable {E : Type*} [Fintype E]

/-- The PCS pairing. -/
noncomputable def pairing (x y : E → ℝ≥0∞) : ℝ≥0∞ := ∑ e, x e * y e

/-- The orthogonal of a set of vectors. -/
def orth (S : Set (E → ℝ≥0∞)) : Set (E → ℝ≥0∞) := {y | ∀ x ∈ S, pairing x y ≤ 1}

theorem subset_orth_orth (S : Set (E → ℝ≥0∞)) : S ⊆ orth (orth S) := by
  intro x hx y hy
  have := hy x hx
  simpa [pairing, mul_comm] using this

theorem orth_anti {S T : Set (E → ℝ≥0∞)} (h : S ⊆ T) : orth T ⊆ orth S :=
  fun _ hy x hx => hy x (h hx)

/-- Every orthogonal is biorthogonally closed: `(S^⊥)^⊥⊥ = S^⊥`. -/
theorem orth_orth_orth (S : Set (E → ℝ≥0∞)) : orth (orth (orth S)) = orth S :=
  le_antisymm (orth_anti (subset_orth_orth S)) (subset_orth_orth _)

/-- **Danos–Ehrhard axioms** on a finite web: biorthogonal closure, every web point reachable,
every web point bounded. -/
structure IsPCS (P : Set (E → ℝ≥0∞)) : Prop where
  closed : orth (orth P) = P
  total : ∀ e, ∃ x ∈ P, x e ≠ 0
  bounded : ∀ e, ∃ M ≠ ⊤, ∀ x ∈ P, x e ≤ M

theorem isPCS_of_eq_orth {P S : Set (E → ℝ≥0∞)} (hP : P = orth S)
    (htot : ∀ e, ∃ x ∈ P, x e ≠ 0) (hbd : ∀ e, ∀ x ∈ P, x e ≤ 1) : IsPCS P :=
  ⟨by rw [hP, orth_orth_orth], htot, fun e => ⟨1, ENNReal.one_ne_top, hbd e⟩⟩

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- An orthogonal is closed under finite mixtures. -/
theorem Mix_subset_orth {S T : Set (E → ℝ≥0∞)} (h : S ⊆ orth T) : Mix S ⊆ orth T := by
  rintro _ ⟨n, w, s, hs, hw, rfl⟩ x hx
  calc pairing x (∑ i, w i • s i) = ∑ i, w i * pairing x (s i) := by
        simp only [pairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i, w i * 1 := Finset.sum_le_sum fun i _ => mul_le_mul_left' (h (hs i) x hx) _
    _ = 1 := by simp [hw]

theorem flat_eq_orth : flat X = orth {fun _ => 1} := by
  ext x; simp [flat, orth, pairing]

theorem isPCS_flat : IsPCS (flat X) := by
  refine isPCS_of_eq_orth flat_eq_orth (fun a => ⟨Pi.single a 1, by simp [flat], by simp⟩) ?_
  intro a x hx
  exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ a)).trans hx

/-- Row indicator of `a`. -/
def row (a : X) : X × Y → ℝ≥0∞ := fun ab => if ab.1 = a then 1 else 0

theorem lin_eq_orth : lin X Y = orth (Set.range (row (Y := Y))) := by
  ext t
  rw [mem_lin_iff]
  simp only [orth, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq,
    pairing, row, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]
  refine forall_congr' fun a => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem isPCS_lin : IsPCS (lin X Y) := by
  refine isPCS_of_eq_orth lin_eq_orth (fun ab => ⟨Pi.single ab 1, ?_, by simp⟩) ?_
  · rw [mem_lin_iff]; intro a
    rcases ab with ⟨a', b'⟩
    by_cases h : a = a'
    · subst h; simp [Pi.single_apply, Prod.ext_iff]
    · simp [Pi.single_apply, Prod.ext_iff, h]
  · rintro ⟨a, b⟩ t ht
    exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ b)).trans
      ((mem_lin_iff t).1 ht a)

theorem tensDual_eq_orth :
    tensDual = orth {x | ∃ y ∈ lin Bool Bool, ∃ z ∈ lin Bool Bool, x = tens y z} := by
  ext t
  simp only [tensDual, orth, Set.mem_setOf_eq, pairing]
  constructor
  · rintro h x ⟨y, hy, z, hz, rfl⟩
    have := h y hy z hz
    rw [Fintype.sum_prod_type]
    convert this using 2 with p _
    exact Finset.sum_congr rfl fun q _ => by simp only [tens]; ring
  · intro h y hy z hz
    have := h (tens y z) ⟨y, hy, z, hz, rfl⟩
    rw [Fintype.sum_prod_type] at this
    convert this using 2 with p _
    exact Finset.sum_congr rfl fun q _ => by simp only [tens]; ring

theorem isPCS_tensDual : IsPCS tensDual := by
  refine isPCS_of_eq_orth tensDual_eq_orth (fun pq => ⟨Pi.single pq 1, ?_, by simp⟩) ?_
  · refine mem_tensDual_of_det _ fun f g => ?_
    rw [pair_det]
    calc ∑ x ∈ univ.filter (covers f g), (Pi.single pq 1 : W × W → ℝ≥0∞) x
        ≤ ∑ x, (Pi.single pq 1 : W × W → ℝ≥0∞) x :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = 1 := by simp
  · intro pq t ht
    obtain ⟨f, g, hc, -⟩ := covers_of_compat2 (s := pq) (t := pq) ⟨Or.inl rfl, Or.inl rfl⟩
    have h1 := ht _ (det_mem_lin f) _ (det_mem_lin g)
    rw [pair_det] at h1
    exact (Finset.single_le_sum (f := t) (fun _ _ => bot_le)
      (Finset.mem_filter.2 ⟨Finset.mem_univ pq, hc⟩)).trans h1

/-- **At second order the recipe gives a strictly smaller space than PCS.** Mixtures of the
certain elements stay inside the PCS, and the pentagon shows the inclusion is strict. -/
theorem Mix_sharp_ssubset_tensDual :
    Mix {z | z ∈ tensDual ∧ ∀ pq, z pq = 0 ∨ z pq = 1} ⊂ tensDual := by
  refine ⟨?_, fun h => ?_⟩
  · rw [tensDual_eq_orth]
    exact Mix_subset_orth fun z hz => tensDual_eq_orth ▸ hz.1
  · obtain ⟨n, w, s, hs, hw, heq⟩ := h pentElt_mem
    exact pentElt_not_mix univ w hw s (fun i _ => (hs i).1) (fun i _ => (hs i).2) heq

/-- **At second order the recipe gives the sequential calculus.** The mixtures of the certain
elements of `(Bool ⊸ Bool) ⊸ (Bool ⊸ Bool)^⊥` are exactly the mixtures of deterministic
sequential strategies. -/
theorem recipe_second_order_eq_sequential :
    Mix {z | z ∈ tensDual ∧ ∀ pq, z pq = 0 ∨ z pq = 1}
      = Mix {z | z ∈ sequential ∧ ∀ pq, z pq = 0 ∨ z pq = 1} := by
  rw [sharp_tensDual_eq_sharp_sequential]

/-- The pentagon element has total weight `5/2` on the pentagon. -/
theorem pentElt_pent_sum : ∑ pq ∈ pent, pentElt pq = 5 * 2⁻¹ := by
  have h2 : ∀ pq ∈ pent, pentElt pq = 2⁻¹ := fun pq hpq => if_pos hpq
  have hc : pent.card = 5 := by decide
  rw [Finset.sum_congr rfl h2, Finset.sum_const, hc, nsmul_eq_mul]; norm_num

/-- **The PCS bound on the pentagon is `5/2`.** Each of the five adjacent pairs of pentagon
points is covered by one deterministic pair, so its two weights sum to at most `1`; adding the
five edge constraints counts every point twice. With `pentElt_mem`, the bound is attained. -/
theorem tensDual_pent_le {t : W × W → ℝ≥0∞} (ht : t ∈ tensDual) :
    2 * ∑ pq ∈ pent, t pq ≤ 5 := by
  have edge : ∀ s s' : W × W, s ≠ s' → compat2 s s' → t s + t s' ≤ 1 := by
    intro s s' hne hc
    obtain ⟨f, g, hs, hs'⟩ := covers_of_compat2 hc
    have h1 := ht _ (det_mem_lin f) _ (det_mem_lin g)
    rw [pair_det] at h1
    refine le_trans ?_ h1
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hs, hs'])
  have e1 := edge ((true, true), (true, true)) ((false, true), (false, true)) (by decide) (by decide)
  have e2 := edge ((false, true), (false, true)) ((false, true), (true, false)) (by decide) (by decide)
  have e3 := edge ((false, true), (true, false)) ((true, false), (false, false)) (by decide) (by decide)
  have e4 := edge ((true, false), (false, false)) ((false, false), (false, false)) (by decide) (by decide)
  have e5 := edge ((false, false), (false, false)) ((true, true), (true, true)) (by decide) (by decide)
  rw [sum_pent]
  calc 2 * (t ((true, true), (true, true)) + (t ((true, false), (false, false)) +
        (t ((false, true), (true, false)) + (t ((false, true), (false, true)) +
        t ((false, false), (false, false))))))
      = (t ((true, true), (true, true)) + t ((false, true), (false, true))) +
        (t ((false, true), (false, true)) + t ((false, true), (true, false))) +
        (t ((false, true), (true, false)) + t ((true, false), (false, false))) +
        (t ((true, false), (false, false)) + t ((false, false), (false, false))) +
        (t ((false, false), (false, false)) + t ((true, true), (true, true))) := by ring
    _ ≤ 1 + 1 + 1 + 1 + 1 := by gcongr
    _ = 5 := by norm_num

end Axioms

end PCS

end ConstructiveProb
