/-
# Probabilistic coherence spaces as mixtures of certain states (first-order, finite webs)

Test of the recipe "a probability calculus is the set of mixtures of the logic's certain
states" against probabilistic coherence spaces (Danos–Ehrhard), on finite webs and first-order
types only. Coefficients live in `ℝ≥0∞`.

* `flat X` is the PCS of a finite data type (`1 ⊕ ⋯ ⊕ 1`): sub-probability vectors on `X`.
* `lin X Y` is `flat X ⊸ flat Y`: matrices sending `flat X` into `flat Y`.

Findings.
1. `lin X Y` is *not* a set of sub-probability distributions on its web `X × Y`: the identity
   on `Bool` has total mass `2` (`id_mem_lin`, `id_not_mem_flat`). So the reading "an element
   of a PCS is a sub-probability over web points" is false beyond data types.
2. `lin X Y` *is* exactly the set of mixtures of deterministic partial maps `X → Option Y`
   (`mem_lin_iff_mix`). The recipe holds once the certain states of a function type are taken
   to be deterministic programs rather than web points. `flat Y` is the case `X = Unit`.
3. The tensor discriminates: on a one-point web `p ⊗ p = p²`, which differs from `p` for
   `0 < p < 1` (`tens_self_ne`), in contrast to `tensorValuation`'s collapse on formulas.
-/
import Mathlib

open scoped ENNReal
open Finset

namespace ConstructiveProb.PCS

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The PCS of a finite data type: sub-probability vectors. -/
def flat (X : Type*) [Fintype X] : Set (X → ℝ≥0∞) := {x | ∑ a, x a ≤ 1}

/-- Matrix action of `t` on the web `X × Y`. -/
noncomputable def app (t : X × Y → ℝ≥0∞) (x : X → ℝ≥0∞) : Y → ℝ≥0∞ :=
  fun b => ∑ a, x a * t (a, b)

/-- The PCS `flat X ⊸ flat Y`. -/
def lin (X Y : Type*) [Fintype X] [Fintype Y] : Set (X × Y → ℝ≥0∞) :=
  {t | ∀ x ∈ flat X, app t x ∈ flat Y}

/-- Elements of `flat X ⊸ flat Y` are exactly the row-substochastic matrices. -/
theorem mem_lin_iff [DecidableEq X] (t : X × Y → ℝ≥0∞) :
    t ∈ lin X Y ↔ ∀ a, ∑ b, t (a, b) ≤ 1 := by
  constructor
  · intro h a
    have hx : (Pi.single a 1 : X → ℝ≥0∞) ∈ flat X := by
      simp [flat]
    have := h _ hx
    simpa [flat, app, Pi.single_apply] using this
  · intro h x hx
    calc ∑ b, app t x b = ∑ a, x a * ∑ b, t (a, b) := by
          simp only [app, Finset.mul_sum]; exact Finset.sum_comm
      _ ≤ ∑ a, x a := Finset.sum_le_sum fun a _ => mul_le_of_le_one_right' (h a)
      _ ≤ 1 := hx

/-- The identity on `Bool`. -/
noncomputable def idBool : Bool × Bool → ℝ≥0∞ := fun ab => if ab.1 = ab.2 then 1 else 0

theorem id_mem_lin : idBool ∈ lin Bool Bool := by
  rw [mem_lin_iff]; intro a; cases a <;> simp [idBool]

/-- **Finding 1.** The identity is a legitimate element of `Bool ⊸ Bool` but carries total
mass `2` on its web, so it is no sub-probability over web points. -/
theorem id_not_mem_flat : idBool ∉ flat (Bool × Bool) := by
  simp only [flat, Set.mem_setOf_eq, Fintype.sum_prod_type, idBool]
  norm_num

/-- A deterministic partial program `f : X → Option Y`, as a point of the web of `X ⊸ Y`. -/
noncomputable def det (f : X → Option Y) : X × Y → ℝ≥0∞ := by
  classical exact fun ab => if f ab.1 = some ab.2 then 1 else 0

omit [Fintype X] in
theorem det_row_le_one (f : X → Option Y) (a : X) : ∑ b, det f (a, b) ≤ 1 := by
  classical
  unfold det
  cases h : f a with
  | none => simp [h]
  | some c =>
    simp only [h, Option.some.injEq]
    rw [Finset.sum_ite_eq]; simp

/-- Completion of row `a` of `t` to a probability on `Option Y` (`none` absorbs the deficit). -/
noncomputable def rowDist (t : X × Y → ℝ≥0∞) (a : X) : Option Y → ℝ≥0∞
  | none => 1 - ∑ b, t (a, b)
  | some b => t (a, b)

omit [Fintype X] in
theorem rowDist_sum (t : X × Y → ℝ≥0∞) (a : X) (h : ∑ b, t (a, b) ≤ 1) :
    ∑ o, rowDist t a o = 1 := by
  rw [Fintype.sum_option]; simp only [rowDist]
  exact tsub_add_cancel_of_le h

/-- **Finding 2.** `flat X ⊸ flat Y` is exactly the set of convex mixtures of deterministic
partial programs. The weight of `f` is the product weight `∏ a, rowDist t a (f a)`. -/
theorem mem_lin_iff_mix [DecidableEq X] (t : X × Y → ℝ≥0∞) :
    t ∈ lin X Y ↔ ∃ w : (X → Option Y) → ℝ≥0∞, ∑ f, w f = 1 ∧ t = ∑ f, w f • det f := by
  classical
  rw [mem_lin_iff]
  constructor
  · intro h
    refine ⟨fun f => ∏ a, rowDist t a (f a), ?_, ?_⟩
    · rw [← Fintype.prod_sum (fun a o => rowDist t a o)]; exact Finset.prod_eq_one fun a _ => rowDist_sum t a (h a)
    · funext ⟨a, b⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, det]
      -- marginalize: replace row `a` by the indicator of `some b`
      let q : X → Option Y → ℝ≥0∞ := fun a' o =>
        rowDist t a' o * (if a' = a then (if o = some b then 1 else 0) else 1)
      have hq := Fintype.prod_sum q
      have lhs : ∏ a', ∑ o, q a' o = t (a, b) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
        have h1 : ∑ o, q a o = t (a, b) := by
          simp only [q, if_true, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq']; simp [rowDist]
        have h2 : ∏ a' ∈ univ.erase a, ∑ o, q a' o = 1 := by
          refine Finset.prod_eq_one fun a' ha' => ?_
          have : a' ≠ a := Finset.ne_of_mem_erase ha'
          simp only [q, this, if_false, mul_one]
          exact rowDist_sum t a' (h a')
        rw [h1, h2, mul_one]
      rw [← lhs, hq]
      refine Finset.sum_congr rfl fun f _ => ?_
      simp only [q, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_ite_eq' univ a, if_pos (Finset.mem_univ a)]
  · rintro ⟨w, hw, rfl⟩ a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    calc ∑ f, ∑ b, w f * det f (a, b) = ∑ f, w f * ∑ b, det f (a, b) := by
          simp [Finset.mul_sum]
      _ ≤ ∑ f, w f := Finset.sum_le_sum fun f _ => mul_le_of_le_one_right' (det_row_le_one f a)
      _ = 1 := hw

/-- Tensor of vectors on the product web. -/
noncomputable def tens (x : X → ℝ≥0∞) (y : Y → ℝ≥0∞) : X × Y → ℝ≥0∞ := fun ab => x ab.1 * y ab.2

theorem tens_mem_flat {x : X → ℝ≥0∞} {y : Y → ℝ≥0∞} (hx : x ∈ flat X) (hy : y ∈ flat Y) :
    tens x y ∈ flat (X × Y) := by
  simp only [flat, Set.mem_setOf_eq, tens, Fintype.sum_prod_type, ← Finset.mul_sum,
    ← Finset.sum_mul] at *
  exact mul_le_one' hx hy

/-- **Finding 3.** On a one-point web, using a resource twice has weight `p²`, which differs from
`p` whenever `0 < p < 1`: the tensor discriminates `a` from `a ⊗ a`. -/
theorem tens_self_ne {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    tens (fun _ : Unit => p) (fun _ : Unit => p) ((), ()) ≠ p := by
  simp only [tens]
  intro h
  have hpt : p ≠ ⊤ := (hp1.trans ENNReal.one_lt_top).ne
  have : p * p < 1 * p := ENNReal.mul_lt_mul_left hp0.ne' hpt hp1
  rw [one_mul, h] at this
  exact lt_irrefl _ this

/-! ### Second order: the recipe fails

`A = Bool ⊸ Bool` has web `W = Bool × Bool` (input, output) and `P(A) = lin Bool Bool`. The PCS
`(A ⊗ A)^⊥ = A ⊸ A^⊥` is `tensDual`. It contains the *pentagon* element `pentElt`, weight `1/2` on
five web points arranged as a 5-cycle of jointly coverable pairs, and `pentElt` is no mixture of
`{0,1}`-valued (deterministic) elements of `tensDual`: on those five points every deterministic
element has total weight at most `2`, the pentagon has `5/2`. -/

/-- Web of `Bool ⊸ Bool`. -/
abbrev W := Bool × Bool

/-- `(P(A) ⊗ P(A))^⊥` for `A = Bool ⊸ Bool`, i.e. the PCS `A ⊸ A^⊥`. -/
def tensDual : Set (W × W → ℝ≥0∞) :=
  {t | ∀ y ∈ lin Bool Bool, ∀ z ∈ lin Bool Bool, ∑ p, ∑ q, y p * t (p, q) * z q ≤ 1}

/-- The five pentagon points. -/
def pent : Finset (W × W) :=
  {((true, true), (true, true)), ((true, false), (false, false)),
   ((false, true), (true, false)), ((false, true), (false, true)),
   ((false, false), (false, false))}

/-- The pentagon element: `1/2` on each pentagon point. -/
noncomputable def pentElt : W × W → ℝ≥0∞ := fun pq => if pq ∈ pent then 2⁻¹ else 0

/-- `(f, g)` covers the web point `(p, q)` when `p` lies in `f` and `q` in `g`. -/
def covers (f g : Bool → Option Bool) (pq : W × W) : Prop :=
  f pq.1.1 = some pq.1.2 ∧ g pq.2.1 = some pq.2.2

instance (f g : Bool → Option Bool) : DecidablePred (covers f g) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Two web points of `Bool ⊸ Bool` lie in a common deterministic program. -/
def compat (p q : W) : Prop := p = q ∨ p.1 ≠ q.1

/-- Two web points of `tensDual` lie in a common deterministic pair. -/
def compat2 (s t : W × W) : Prop := compat s.1 t.1 ∧ compat s.2 t.2

instance : DecidableRel compat := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidableRel compat2 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem compat_of_some {f : Bool → Option Bool} {p q : W} (hp : f p.1 = some p.2)
    (hq : f q.1 = some q.2) : compat p q := by
  by_cases h : p.1 = q.1
  · left; rw [h] at hp; exact Prod.ext h (Option.some_injective _ (hp.symm.trans hq))
  · exact Or.inr h

theorem compat2_of_covers {f g : Bool → Option Bool} {s t : W × W} (hs : covers f g s)
    (ht : covers f g t) : compat2 s t :=
  ⟨compat_of_some hs.1 ht.1, compat_of_some hs.2 ht.2⟩

/-- A deterministic program through two compatible points. -/
def through (p q : W) : Bool → Option Bool := fun b => if b = p.1 then some p.2 else some q.2

theorem through_left (p q : W) : through p q p.1 = some p.2 := by simp [through]

theorem through_right {p q : W} (h : compat p q) : through p q q.1 = some q.2 := by
  unfold through
  split_ifs with h'
  · rcases h with h | h
    · rw [h]
    · exact absurd h'.symm h
  · rfl

theorem covers_of_compat2 {s t : W × W} (h : compat2 s t) :
    ∃ f g, covers f g s ∧ covers f g t :=
  ⟨through s.1 t.1, through s.2 t.2, ⟨through_left _ _, through_left _ _⟩,
    ⟨through_right h.1, through_right h.2⟩⟩

/-- The compatibility graph on the pentagon is a 5-cycle: it has no triangle ... -/
theorem pent_clique_le_two : ∀ B ∈ pent.powerset,
    (∀ s ∈ B, ∀ t ∈ B, compat2 s t) → B.card ≤ 2 := by
  decide

/-- ... and no independent triple. -/
theorem pent_indep_le_two : ∀ B ∈ pent.powerset,
    (∀ s ∈ B, ∀ t ∈ B, compat2 s t → s = t) → B.card ≤ 2 := by
  decide

/-- Each deterministic pair covers at most two pentagon points. -/
theorem pent_cover_le_two (f g : Bool → Option Bool) : (pent.filter (covers f g)).card ≤ 2 :=
  pent_clique_le_two _ (Finset.mem_powerset.2 (Finset.filter_subset _ _)) fun s hs t ht =>
    compat2_of_covers (Finset.mem_filter.1 hs).2 (Finset.mem_filter.1 ht).2

theorem det_mem_lin (f : Bool → Option Bool) : det f ∈ lin Bool Bool :=
  (mem_lin_iff _).2 (det_row_le_one f)

theorem det_mul_det (f g : Bool → Option Bool) (t : W × W → ℝ≥0∞) (pq : W × W) :
    det f pq.1 * t pq * det g pq.2 = if covers f g pq then t pq else 0 := by
  classical
  unfold det covers
  by_cases h1 : f pq.1.1 = some pq.1.2 <;> by_cases h2 : g pq.2.1 = some pq.2.2 <;> simp [h1, h2]

/-- The pairing against a deterministic pair is the sum over covered points. -/
theorem pair_det (f g : Bool → Option Bool) (t : W × W → ℝ≥0∞) :
    ∑ p, ∑ q, det f p * t (p, q) * det g q = ∑ pq ∈ univ.filter (covers f g), t pq := by
  rw [← Fintype.sum_prod_type', Finset.sum_filter]
  exact Finset.sum_congr rfl fun pq _ => det_mul_det f g t pq

/-- To test membership in `tensDual` it suffices to test deterministic pairs (bilinearity). -/
theorem mem_tensDual_of_det (t : W × W → ℝ≥0∞)
    (h : ∀ f g : Bool → Option Bool, ∑ p, ∑ q, det f p * t (p, q) * det g q ≤ 1) :
    t ∈ tensDual := by
  intro y hy z hz
  obtain ⟨u, hu, rfl⟩ := (mem_lin_iff_mix y).1 hy
  obtain ⟨v, hv, rfl⟩ := (mem_lin_iff_mix z).1 hz
  have hexp : ∑ p, ∑ q, (∑ f, u f • det f) p * t (p, q) * (∑ g, v g • det g) q
      = ∑ f, ∑ g, u f * v g * ∑ p, ∑ q, det f p * t (p, q) * det g q := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => enter [2, p, 2, q]; rw [Finset.sum_comm]
    conv_lhs => enter [2, p]; rw [Finset.sum_comm]
    conv_lhs => enter [2, p, 2, f]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => enter [2, f]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ =>
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [hexp]
  calc ∑ f, ∑ g, u f * v g * ∑ p, ∑ q, det f p * t (p, q) * det g q
    _ ≤ ∑ f, ∑ g, u f * v g * 1 :=
          Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun g _ => mul_le_mul_left' (h f g) _
    _ = 1 := by simp [← Finset.mul_sum, hu, hv]

/-- **The pentagon is a legitimate element** of `(Bool ⊸ Bool) ⊸ (Bool ⊸ Bool)^⊥`. -/
theorem pentElt_mem : pentElt ∈ tensDual := by
  refine mem_tensDual_of_det _ fun f g => ?_
  rw [pair_det]
  calc ∑ pq ∈ univ.filter (covers f g), pentElt pq
        = ∑ pq ∈ pent.filter (covers f g), (2⁻¹ : ℝ≥0∞) := by
          rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_subset (Finset.subset_univ pent)]
          · refine Finset.sum_congr rfl fun pq hpq => ?_
            simp [pentElt, hpq]
          · intro pq _ hpq; simp [pentElt, hpq]
    _ = (pent.filter (covers f g)).card * 2⁻¹ := by simp
    _ ≤ 2 * 2⁻¹ := mul_le_mul_right' (by exact_mod_cast pent_cover_le_two f g) _
    _ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- A deterministic (`{0,1}`-valued) element of `tensDual` has total weight at most `2` on the
pentagon. -/
theorem det_pent_le_two {z : W × W → ℝ≥0∞} (hz : z ∈ tensDual)
    (h01 : ∀ pq, z pq = 0 ∨ z pq = 1) : ∑ pq ∈ pent, z pq ≤ 2 := by
  classical
  set B := pent.filter (fun pq => z pq = 1)
  have hsum : ∑ pq ∈ pent, z pq = B.card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun pq _ => ?_
    rcases h01 pq with h | h <;> simp [h]
  have hB : ∀ f g : Bool → Option Bool, (B.filter (covers f g)).card ≤ 1 := by
    intro f g
    have h1 := hz _ (det_mem_lin f) _ (det_mem_lin g)
    rw [pair_det] at h1
    have h2 : ((B.filter (covers f g)).card : ℝ≥0∞) ≤ ∑ pq ∈ univ.filter (covers f g), z pq := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      calc ∑ pq ∈ B.filter (covers f g), ((1 : ℕ) : ℝ≥0∞)
            = ∑ pq ∈ B.filter (covers f g), z pq := by
              refine Finset.sum_congr rfl fun pq hpq => ?_
              simp only [B, Finset.mem_filter] at hpq; simp [hpq.1.2]
        _ ≤ ∑ pq ∈ univ.filter (covers f g), z pq := by
              refine Finset.sum_le_sum_of_subset ?_
              intro pq hpq; simp only [Finset.mem_filter] at hpq ⊢; exact ⟨Finset.mem_univ _, hpq.2⟩
    exact_mod_cast h2.trans h1
  have := pent_indep_le_two B (Finset.mem_powerset.2 (Finset.filter_subset _ _))
    fun s hs t ht hst => by
      obtain ⟨f, g, hfs, hft⟩ := covers_of_compat2 hst
      exact Finset.card_le_one.1 (hB f g) s (Finset.mem_filter.2 ⟨hs, hfs⟩) t
        (Finset.mem_filter.2 ⟨ht, hft⟩)
  rw [hsum]; exact_mod_cast this

/-- **Finding 4: the recipe fails at second order.** The pentagon element of
`(Bool ⊸ Bool) ⊸ (Bool ⊸ Bool)^⊥` is not a convex mixture of deterministic (`{0,1}`-valued)
elements of that PCS. -/
theorem pentElt_not_mix {ι : Type*} (s : Finset ι) (w : ι → ℝ≥0∞) (hw : ∑ i ∈ s, w i = 1)
    (z : ι → W × W → ℝ≥0∞) (hz : ∀ i ∈ s, z i ∈ tensDual)
    (h01 : ∀ i ∈ s, ∀ pq, z i pq = 0 ∨ z i pq = 1) :
    pentElt ≠ ∑ i ∈ s, w i • z i := by
  intro h
  have lhs : ∑ pq ∈ pent, pentElt pq = 5 * 2⁻¹ := by
    have h2 : ∀ pq ∈ pent, pentElt pq = 2⁻¹ := fun pq hpq => if_pos hpq
    have hc : pent.card = 5 := by decide
    rw [Finset.sum_congr rfl h2, Finset.sum_const, hc, nsmul_eq_mul]; norm_num
  have rhs : ∑ pq ∈ pent, (∑ i ∈ s, w i • z i) pq ≤ 2 := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    calc ∑ i ∈ s, ∑ pq ∈ pent, w i * z i pq = ∑ i ∈ s, w i * ∑ pq ∈ pent, z i pq := by
          simp [Finset.mul_sum]
      _ ≤ ∑ i ∈ s, w i * 2 :=
          Finset.sum_le_sum fun i hi => mul_le_mul_left' (det_pent_le_two (hz i hi) (h01 i hi)) _
      _ = 2 := by rw [← Finset.sum_mul, hw, one_mul]
  rw [← h, lhs] at rhs
  have : (5 : ℝ≥0∞) * 2⁻¹ = 5 / 2 := (div_eq_mul_inv _ _).symm
  rw [this, ENNReal.div_le_iff two_ne_zero ENNReal.ofNat_ne_top] at rhs
  norm_num at rhs

end ConstructiveProb.PCS
