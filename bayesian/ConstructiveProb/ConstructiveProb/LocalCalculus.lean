/-
# Local certainty: linear logic and quantum event logic

The construction of `Recipe.lean` mixes global certain states. For an event structure given by
contexts (sets of jointly observable, mutually exclusive outcomes), the *local* calculus asks only
that the restriction to every context be a (sub)probability, and the *global* calculus is the set
of mixtures of its `{0,1}`-valued elements (`locS`, `locN`, `globS`, `globN`). With one context the
two agree (`globN_single`, `globS_single`).

* Linear logic. The local calculus of a formula `A`, whose contexts are the supports of the
  `{0,1}`-valued elements of `P A^⊥` (`loc_eq_locS`), contains the PCS, which contains the calculus
  (`recipe_sub_P_sub_loc`). The PCS equals it iff the dual has no gap (`P_eq_loc_iff`). At `T` the
  first inclusion is strict and the second is an equality (`P_S2_eq_loc`), and at `(T ⊗ T)^⊥` the
  second is strict (`P_TT_ssubset_loc`, Shannon's set).
* Quantum event logic on Cabello's set. The local calculus is the set of states of
  `Quantum.lean` (`locN_cabello`), the global one is empty (`globN_cabello`), and Born states are
  local. The local calculus is strictly larger than the mixtures of Born states (`half_not_born`):
  the witness forgets that `(0,0,0,1)` lies in the span of the orthogonal rays `(1,0,0,±1)`, which
  every Born state respects (`born_mono`). The Born states of the rays determine orthogonality and
  certainty (`born_ray_zero_iff`, `born_ray_one_iff`).
-/
import ConstructiveProb.Quantum
import ConstructiveProb.ThreeArg

open scoped ENNReal
open Finset

namespace ConstructiveProb.Contexts

open ConstructiveProb (Mix IsSharpVec mem_Mix_of_fintype)

variable {E : Type} [Fintype E] [DecidableEq E]

/-- The local calculus with divergence: at most `1` on every context. -/
def locS (C : Set (Finset E)) : Set (E → ℝ≥0∞) := {x | ∀ t ∈ C, ∑ e ∈ t, x e ≤ 1}

/-- The local calculus: exactly `1` on every context. -/
def locN (C : Set (Finset E)) : Set (E → ℝ≥0∞) := {x | ∀ t ∈ C, ∑ e ∈ t, x e = 1}

/-- The global calculus with divergence: mixtures of the `{0,1}`-valued local states. -/
def globS (C : Set (Finset E)) : Set (E → ℝ≥0∞) := Mix {x | x ∈ locS C ∧ IsSharpVec x}

/-- The global calculus: mixtures of the `{0,1}`-valued normalized local states. -/
def globN (C : Set (Finset E)) : Set (E → ℝ≥0∞) := Mix {x | x ∈ locN C ∧ IsSharpVec x}

theorem sum_mix (t : Finset E) {n : ℕ} (w : Fin n → ℝ≥0∞) (s : Fin n → E → ℝ≥0∞) :
    ∑ e ∈ t, (∑ i, w i • s i) e = ∑ i, w i * ∑ e ∈ t, s i e := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- **Global states are local.** -/
theorem globN_sub (C : Set (Finset E)) : globN C ⊆ locN C := by
  rintro _ ⟨n, w, s, hs, hw, rfl⟩ t ht
  rw [sum_mix]
  simp only [fun i => (hs i).1 t ht, mul_one, hw]

theorem globS_sub (C : Set (Finset E)) : globS C ⊆ locS C := by
  rintro _ ⟨n, w, s, hs, hw, rfl⟩ t ht
  rw [sum_mix]
  calc ∑ i, w i * ∑ e ∈ t, s i e ≤ ∑ i, w i * 1 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_left' ((hs i).1 t ht) _
    _ = 1 := by simp [hw]

/-- **One context: the local and the global calculus agree**, and both are classical
probability on the outcomes. -/
theorem globN_single : globN ({Finset.univ} : Set (Finset E)) = locN {Finset.univ} := by
  refine le_antisymm (globN_sub _) fun x hx => ?_
  have h1 : ∑ e, x e = 1 := hx _ rfl
  have hx' : x = ∑ e, x e • (Pi.single e 1 : E → ℝ≥0∞) := by
    funext a; simp [Finset.sum_apply, Pi.single_apply]
  rw [hx']
  refine mem_Mix_of_fintype _ _ (fun e => ⟨?_, fun a => ?_⟩) h1
  · rintro t rfl; simp
  · by_cases h : a = e <;> simp [Pi.single_apply, h]

theorem globS_single : globS ({Finset.univ} : Set (Finset E)) = locS {Finset.univ} := by
  refine le_antisymm (globS_sub _) fun x hx => ?_
  have h1 : ∑ e, x e ≤ 1 := hx _ rfl
  let w : Option E → ℝ≥0∞ := fun o => o.elim (1 - ∑ e, x e) x
  let s : Option E → E → ℝ≥0∞ := fun o => o.elim 0 fun e => Pi.single e 1
  have hx' : x = ∑ o, w o • s o := by
    funext a; simp [w, s, Fintype.sum_option, Finset.sum_apply, Pi.single_apply]
  rw [hx']
  refine mem_Mix_of_fintype w s (fun o => ⟨?_, fun a => ?_⟩) ?_
  · rintro t rfl
    cases o with
    | none => simp [s]
    | some e => simp [s]
  · cases o with
    | none => simp [s]
    | some e => by_cases h : a = e <;> simp [s, Pi.single_apply, h]
  · simp only [w, Fintype.sum_option, Option.elim]
    exact tsub_add_cancel_of_le h1

end ConstructiveProb.Contexts

namespace ConstructiveProb.Linear

open ConstructiveProb.PCS (orth pairing subset_orth_orth)
open ConstructiveProb.Contexts (locS)
open Fm

/-! ### Linear logic -/

/-- The local calculus of a formula: at most `1` against every `{0,1}`-valued element of the
dual. -/
def loc (A : Fm) : Set (web A → ℝ≥0∞) := orth (sharpP (Fm.neg A))

/-- The contexts of `A`: the supports of the `{0,1}`-valued elements of the dual. -/
def dualCtx (A : Fm) : Set (Finset (web A)) :=
  {t | ∃ s ∈ sharpP (Fm.neg A), t = Finset.univ.filter fun e => s e = 1}

theorem pairing_sharp {E : Type} [Fintype E] [DecidableEq E] {s : E → ℝ≥0∞}
    (hs : ∀ e, s e = 0 ∨ s e = 1) (x : E → ℝ≥0∞) :
    pairing s x = ∑ e ∈ Finset.univ.filter (fun e => s e = 1), x e := by
  rw [Finset.sum_filter, pairing]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases hs e with h | h <;> simp [h]

/-- **The local calculus of a formula is the local calculus of its contexts.** -/
theorem loc_eq_locS (A : Fm) : loc A = locS (dualCtx A) := by
  ext x
  constructor
  · rintro hx _ ⟨s, hs, rfl⟩
    rw [← pairing_sharp hs.2]; exact hx s hs
  · intro hx s hs
    rw [pairing_sharp hs.2]; exact hx _ ⟨s, hs, rfl⟩

theorem loc_eq (A : Fm) : loc A = orth (recipe (Fm.neg A)) := by
  rw [loc, recipe, orth_Mix]; rfl

theorem P_eq_orth (A : Fm) : P A = orth (P (Fm.neg A)) := ((isPCS_P A).closed).symm

/-- **The PCS lies between the calculus and the local calculus.** -/
theorem recipe_sub_P_sub_loc (A : Fm) : recipe A ⊆ P A ∧ P A ⊆ loc A := by
  refine ⟨recipe_subset_P A, ?_⟩
  rw [loc_eq, P_eq_orth A]
  exact orth_antitone (recipe_subset_P _)

/-- **The PCS is the local calculus iff the dual has no gap.** -/
theorem P_eq_loc_iff (A : Fm) : P A = loc A ↔ recipe (Fm.neg A) = P (Fm.neg A) := by
  rw [loc_eq, P_eq_orth A]
  constructor
  · intro h
    have := congrArg orth h
    rw [recipe_orth_orth, (isPCS_P (Fm.neg A)).closed] at this
    exact this.symm
  · intro h; rw [h]

/-- Indicators of cliques are local. -/
theorem clique_mem_loc (A : Fm) {c : web A → ℝ≥0∞} (h01 : ∀ e, c e = 0 ∨ c e = 1)
    (hc : ∀ x y, c x = 1 → c y = 1 → coh A x y) : c ∈ loc A := by
  classical
  intro s hs
  have hs' := sharp_isClique (Fm.neg A) hs.1 hs.2
  have hterm : ∀ e, s e * c e = if s e = 1 ∧ c e = 1 then 1 else 0 := fun e => by
    rcases hs.2 e with h | h <;> rcases h01 e with h' | h' <;> simp [h, h']
  rw [pairing, Finset.sum_congr rfl fun e _ => hterm e, Finset.sum_boole]
  have : (Finset.univ.filter fun e => s e = 1 ∧ c e = 1).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases hs' a b ha.1 hb.1 with h | h
    · exact h
    · exact absurd (hc a b ha.2 hb.2) h
  exact_mod_cast this

theorem P_negneg (X : Fm) : P (Fm.neg (Fm.neg X)) = P X := (isPCS_P X).closed

theorem recipe_negneg (X : Fm) : recipe (Fm.neg (Fm.neg X)) = recipe X := by
  show ConstructiveProb.Mix {z | z ∈ P (Fm.neg (Fm.neg X)) ∧ _} = ConstructiveProb.Mix {z | z ∈ P X ∧ _}
  rw [P_negneg]

/-- **At `T` the PCS is the local calculus**, since its dual, the core, has no gap. -/
theorem P_S2_eq_loc : P S2 = loc S2 := by
  rw [P_eq_loc_iff]
  show recipe (Fm.neg (Fm.neg (core 2 2 2 2))) = P (Fm.neg (Fm.neg (core 2 2 2 2)))
  rw [recipe_negneg, P_negneg, recipe_core]

/-- **At `(T ⊗ T)^⊥` the PCS is strictly smaller than the local calculus**: Shannon's set is a
local `{0,1}`-valued state outside the PCS. -/
theorem P_TT_ssubset_loc : P TT ⊂ loc TT := by
  classical
  refine Set.ssubset_iff_subset_ne.2 ⟨(recipe_sub_P_sub_loc TT).2, fun h => shannonF_not_mem ?_⟩
  rw [h]
  refine clique_mem_loc TT (fun e => by by_cases he : e ∈ shannonF <;> simp [he]) fun x y hx hy => ?_
  have hx' : x ∈ shannonF := by by_contra h'; simp [h'] at hx
  have hy' : y ∈ shannonF := by by_contra h'; simp [h'] at hy
  exact shannonF_clique x hx' y hy'

end ConstructiveProb.Linear

namespace ConstructiveProb.Quantum

open ConstructiveProb.Contexts (locN globN)

/-! ### Quantum event logic on Cabello's set -/

/-- The nine contexts. -/
def ctx : Set (Finset (Fin 18)) := {t | ∃ b, t = Finset.univ.image (bas b)}

theorem bas_inj : ∀ b, Function.Injective (bas b) := by
  intro b i j h; revert b i j; decide

theorem sum_ctx (x : Fin 18 → ℝ≥0∞) (b : Fin 9) :
    ∑ e ∈ Finset.univ.image (bas b), x e = ∑ i, x (bas b i) :=
  Finset.sum_image fun i _ j _ h => bas_inj b h

/-- **The local calculus is the set of quantum-logic states.** -/
theorem locN_cabello : locN ctx = states := by
  ext x
  constructor
  · intro hx b; rw [← sum_ctx]; exact hx _ ⟨b, rfl⟩
  · rintro hx _ ⟨b, rfl⟩; rw [sum_ctx]; exact hx b

/-- **The global calculus is empty** (Kochen–Specker). -/
theorem globN_cabello : globN ctx = ∅ := by
  have : {x | x ∈ locN ctx ∧ IsSharpVec x} = certain := by
    rw [locN_cabello]; ext x; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [globN, this, Mix_certain_empty]

theorem born_local {ψ : Fin 4 → ℝ} (hψ : ∑ k, ψ k ^ 2 = 1) : born ψ ∈ locN ctx :=
  locN_cabello ▸ born_mem hψ

/-- The rays used by the witness of strictness. -/
theorem vec1 : vec 1 = ![0, 0, 0, 1] := rfl
theorem vec11 : vec 11 = ![1, 0, 0, -1] := rfl
theorem vec12 : vec 12 = ![1, 0, 0, 1] := rfl

/-- **Born states respect the subspace order.** `(0,0,0,1)` lies in the span of the orthogonal
rays `(1,0,0,1)` and `(1,0,0,-1)`, and its Born weight is at most theirs. -/
theorem born_mono (ψ : Fin 4 → ℝ) : born ψ 1 ≤ born ψ 12 + born ψ 11 := by
  simp only [born, vec1, vec11, vec12, Fin.sum_univ_four]
  simp
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg (ψ 0)]

/-- The witness: `½` on nine rays, two in every context. -/
def halfSet : Finset (Fin 18) := {0, 1, 2, 6, 7, 9, 14, 16, 17}

noncomputable def half : Fin 18 → ℝ≥0∞ := fun v => if v ∈ halfSet then 2⁻¹ else 0

theorem half_two : ∀ b : Fin 9, (Finset.univ.filter fun i : Fin 4 => bas b i ∈ halfSet).card = 2 := by
  decide

theorem half_mem : half ∈ locN ctx := by
  rw [locN_cabello]
  intro b
  simp only [half]
  rw [← Finset.sum_filter, Finset.sum_const, half_two, nsmul_eq_mul]
  norm_num [ENNReal.mul_inv_cancel]

/-- **The local calculus is strictly larger than the quantum states.** The witness is a state of
the event logic and not a mixture of Born states. -/
theorem half_not_born :
    half ∈ locN ctx ∧ half ∉ Mix {x | ∃ ψ : Fin 4 → ℝ, ∑ k, ψ k ^ 2 = 1 ∧ x = born ψ} := by
  refine ⟨half_mem, ?_⟩
  rintro ⟨n, w, s, hs, hw, heq⟩
  have key : ∀ i, s i 1 ≤ s i 12 + s i 11 := fun i => by
    obtain ⟨ψ, -, hψ⟩ := hs i; rw [hψ]; exact born_mono ψ
  have h1 : half 1 ≤ half 12 + half 11 := by
    rw [heq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib, ← mul_add]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_left' (key i) _
  simp [half, halfSet] at h1

/-! ### The Born states determine the event logic -/

/-- The unit vector of a ray. -/
noncomputable def unit (u : Fin 18) : Fin 4 → ℝ := fun k => (vec u k : ℝ) / Real.sqrt (dot (vec u) (vec u))

theorem dot_pos : ∀ u : Fin 18, 0 < dot (vec u) (vec u) := by decide

theorem cs_eq_iff : ∀ u v : Fin 18,
    dot (vec u) (vec v) ^ 2 = dot (vec u) (vec u) * dot (vec v) (vec v) ↔ u = v := by decide

theorem dot_cast (u v : Fin 18) : ∑ k, (vec u k : ℝ) * (vec v k : ℝ) = (dot (vec u) (vec v) : ℝ) := by
  simp [dot]

theorem born_unit (u v : Fin 18) :
    born (unit u) v = ENNReal.ofReal ((dot (vec u) (vec v) : ℝ) ^ 2 /
      ((dot (vec u) (vec u) : ℝ) * (dot (vec v) (vec v) : ℝ))) := by
  have hu : (0 : ℝ) < dot (vec u) (vec u) := by exact_mod_cast dot_pos u
  simp only [born, unit]
  congr 1
  have e1 : ∑ k, (vec u k : ℝ) / Real.sqrt (dot (vec u) (vec u)) * (vec v k : ℝ) =
      (dot (vec u) (vec v) : ℝ) / Real.sqrt (dot (vec u) (vec u)) := by
    rw [← dot_cast u v, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ k, ((vec v k : ℝ)) ^ 2 = (dot (vec v) (vec v) : ℝ) := by
    rw [← dot_cast v v]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2, div_pow, Real.sq_sqrt hu.le, div_div]

/-- **Orthogonality is recovered**: two rays are orthogonal iff the Born state of one gives the
other probability `0`. -/
theorem born_ray_zero_iff (u v : Fin 18) : born (unit u) v = 0 ↔ dot (vec u) (vec v) = 0 := by
  have hu : (0 : ℝ) < dot (vec u) (vec u) := by exact_mod_cast dot_pos u
  have hv : (0 : ℝ) < dot (vec v) (vec v) := by exact_mod_cast dot_pos v
  rw [born_unit, ENNReal.ofReal_eq_zero, div_nonpos_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_le.2 (mul_pos hu hv))
    · have : ((dot (vec u) (vec v) : ℤ) : ℝ) = 0 := by nlinarith [sq_nonneg ((dot (vec u) (vec v) : ℤ) : ℝ)]
      exact_mod_cast this
  · intro h; right; rw [h]; simp; positivity

/-- **Certainty is recovered**: the only ray of probability `1` under the Born state of `u` is
`u`. -/
theorem born_ray_one_iff (u v : Fin 18) : born (unit u) v = 1 ↔ u = v := by
  have hu : (0 : ℝ) < dot (vec u) (vec u) := by exact_mod_cast dot_pos u
  have hv : (0 : ℝ) < dot (vec v) (vec v) := by exact_mod_cast dot_pos v
  rw [born_unit, ENNReal.ofReal_eq_one, div_eq_one_iff_eq (mul_pos hu hv).ne', ← cs_eq_iff]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem unit_norm (u : Fin 18) : ∑ k, unit u k ^ 2 = 1 := by
  have hu : (0 : ℝ) < dot (vec u) (vec u) := by exact_mod_cast dot_pos u
  simp only [unit, div_pow, Real.sq_sqrt hu.le, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hu.ne']
  rw [← dot_cast u u]; exact Finset.sum_congr rfl fun k _ => by ring

end ConstructiveProb.Quantum
