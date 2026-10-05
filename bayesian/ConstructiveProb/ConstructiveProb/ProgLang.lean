/-
# A linear probabilistic language for the second-order type

Programs of type `((X ⊸ Y) ⊗ (X' ⊸ Y'))^⊥` receive `f : X ⊸ Y` and `g : X' ⊸ Y'` and must call
each exactly once; the four stages of the syntax enforce this. Every stage has finite probabilistic
choice (`choose`, with sub-probability weights; the missing mass diverges) and divergence.

* `P0.sound`: every program denotes a randomized sequential program, so an element of the
  recipe's calculus (`recipe_eq_sequentialG`).
* `P0.sharp_definable`: every certain element of the probabilistic coherence space is the
  denotation of a deterministic program.

So the calculus is the convex hull of the denotations of this language, and the pentagon is the
denotation of no program.
-/
import ConstructiveProb.GeneralKuhn

open scoped ENNReal

namespace ConstructiveProb.PCS.General

variable {X Y X' Y' : Type} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
  [DecidableEq X] [DecidableEq Y] [DecidableEq X'] [DecidableEq Y']

/-! ### Syntax -/

/-- Both functions have been called. -/
inductive PEnd
  | halt
  | diverge
  | choose (k : Nat) (w : Fin k → ℝ≥0∞) (hw : ∑ i, w i ≤ 1) (p : Fin k → PEnd)

/-- One function has been called; the other, with inputs `C` and outputs `D`, must be called. -/
inductive POne (C D : Type)
  | diverge
  | choose (k : Nat) (w : Fin k → ℝ≥0∞) (hw : ∑ i, w i ≤ 1) (p : Fin k → POne C D)
  | call (c : C) (k : D → PEnd)

/-- No function has been called. -/
inductive P0 (X Y X' Y' : Type)
  | diverge
  | choose (k : Nat) (w : Fin k → ℝ≥0∞) (hw : ∑ i, w i ≤ 1) (p : Fin k → P0 X Y X' Y')
  | callF (a : X) (k : Y → POne X' Y')
  | callG (c : X') (k : Y' → POne X Y)

/-! ### Denotations -/

noncomputable def PEnd.den : PEnd → ℝ≥0∞
  | .halt => 1
  | .diverge => 0
  | .choose _ w _ p => ∑ i, w i * (p i).den

noncomputable def POne.den {C D : Type} [DecidableEq C] : POne C D → C × D → ℝ≥0∞
  | .diverge => fun _ => 0
  | .choose _ w _ p => fun cd => ∑ i, w i * (p i).den cd
  | .call c k => fun cd => if cd.1 = c then (k cd.2).den else 0

noncomputable def P0.den : P0 X Y X' Y' → (X × Y) × (X' × Y') → ℝ≥0∞
  | .diverge => fun _ => 0
  | .choose _ w _ p => fun u => ∑ i, w i * (p i).den u
  | .callF a k => fun u => if u.1.1 = a then (k u.1.2).den u.2 else 0
  | .callG c k => fun u => if u.2.1 = c then (k u.2.2).den u.1 else 0

/-! ### Soundness -/

theorem PEnd.den_le_one : ∀ p : PEnd, p.den ≤ 1
  | .halt => le_refl _
  | .diverge => zero_le_one
  | .choose _ w hw p => by
    simp only [PEnd.den]
    calc ∑ i, w i * (p i).den ≤ ∑ i, w i * 1 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_left' ((p i).den_le_one) _
      _ ≤ 1 := by simpa using hw

/-- A one-call program is a behavioural core with a trivial first stage. -/
theorem POne.core {C D : Type} [Fintype C] [DecidableEq C] :
    ∀ p : POne C D, ∃ K : Core Unit Unit C D, K.mass ≤ 1 ∧
      ∀ c d, p.den (c, d) = K.val () () c d
  | .diverge => ⟨⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩, by
      simp [Core.mass], fun _ _ => by simp [POne.den, Core.val]⟩
  | .call c k => ⟨⟨fun _ => 1, fun _ _ c' => if c' = c then 1 else 0,
      fun _ _ _ d => (k d).den, fun _ _ => by simp, fun _ _ _ d => (k d).den_le_one⟩,
      by simp [Core.mass], fun c' d => by
        simp only [POne.den, Core.val, one_mul]
        split_ifs <;> simp⟩
  | .choose n w hw p => by
    choose K hK hval using fun i => POne.core (p i)
    have hw1 : ∀ i, w i ≤ 1 := fun i =>
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)).trans hw
    obtain ⟨K', hK'μ, hK'v⟩ := core_mixG w K fun i a =>
      ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (hw1 i))
        (ne_top_of_le_ne_top ENNReal.one_ne_top (((K i).μ_le_mass a).trans (hK i)))
    refine ⟨K', ?_, fun c d => ?_⟩
    · simp only [Core.mass, hK'μ, Fintype.univ_unit, Finset.sum_singleton]
      calc ∑ i, w i * (K i).μ () ≤ ∑ i, w i * 1 := Finset.sum_le_sum fun i _ =>
            mul_le_mul_left' (by simpa [Core.mass] using hK i) _
        _ ≤ 1 := by simpa using hw
    · simp only [POne.den, hK'v, hval]

/-- A sub-convex combination of randomized sequential programs is one. -/
theorem sequentialG_subconvex {n : Nat} (w : Fin n → ℝ≥0∞) (hw : ∑ i, w i ≤ 1)
    (t : Fin n → (X × Y) × (X' × Y') → ℝ≥0∞) (ht : ∀ i, t i ∈ sequentialG X Y X' Y') :
    (fun u => ∑ i, w i * t i u) ∈ sequentialG X Y X' Y' := by
  choose F G hm htF using ht
  have hw1 : ∀ i, w i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)).trans hw
  have fin1 : ∀ x : ℝ≥0∞, x ≤ 1 → x ≠ ⊤ := fun x h => ne_top_of_le_ne_top ENNReal.one_ne_top h
  obtain ⟨F', hF'μ, eF⟩ := core_mixG w F fun i a => ENNReal.mul_ne_top (fin1 _ (hw1 i))
    (fin1 _ (((F i).μ_le_mass a).trans (le_self_add.trans (hm i))))
  obtain ⟨G', hG'μ, eG⟩ := core_mixG w G fun i a => ENNReal.mul_ne_top (fin1 _ (hw1 i))
    (fin1 _ (((G i).μ_le_mass a).trans (le_add_self.trans (hm i))))
  refine ⟨F', G', ?_, ?_⟩
  · simp only [Core.mass, hF'μ, hG'μ]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a i => w i * (G i).μ a),
      ← Finset.sum_add_distrib]
    calc ∑ i, (∑ a, w i * (F i).μ a + ∑ a, w i * (G i).μ a) ≤ ∑ i, w i * 1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
          exact mul_le_mul_left' (hm i) _
      _ ≤ 1 := by simpa using hw
  · funext u
    simp only [eF, eG]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [htF i, mul_add]

/-- **Soundness**: every program denotes a randomized sequential program. -/
theorem P0.sound : ∀ p : P0 X Y X' Y', p.den ∈ sequentialG X Y X' Y'
  | .diverge => by
    refine ⟨⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩,
      ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩, by simp [Core.mass], ?_⟩
    funext u; simp [P0.den, Core.val]
  | .choose _ w hw p => by
    have := sequentialG_subconvex w hw (fun i => (p i).den) fun i => P0.sound (p i)
    simpa [P0.den] using this
  | .callF a k => by
    choose K hK hval using fun b => POne.core (k b)
    refine ⟨⟨fun x => if x = a then 1 else 0, fun _ b c => (K b).μ () * (K b).κ () () c,
      fun _ b c d => (K b).ρ () () c d, fun _ b => ?_, fun _ b _ _ => (K b).hρ _ _ _ _⟩,
      ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩, by
        simp [Core.mass, Finset.sum_ite_eq'], ?_⟩
    · rw [← Finset.mul_sum]
      calc (K b).μ () * ∑ c, (K b).κ () () c ≤ 1 * 1 :=
            mul_le_mul' (by simpa [Core.mass] using hK b) ((K b).hκ () ())
        _ = 1 := one_mul 1
    · funext u
      simp only [P0.den, Core.val, mul_zero, add_zero, zero_mul]
      split_ifs with h
      · rw [hval]; simp only [Core.val, one_mul]; try ring
      · simp
  | .callG c k => by
    choose K hK hval using fun d => POne.core (k d)
    refine ⟨⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩,
      ⟨fun x => if x = c then 1 else 0, fun _ d a => (K d).μ () * (K d).κ () () a,
      fun _ d a b => (K d).ρ () () a b, fun _ d => ?_, fun _ d _ _ => (K d).hρ _ _ _ _⟩, by
        simp [Core.mass, Finset.sum_ite_eq'], ?_⟩
    · rw [← Finset.mul_sum]
      calc (K d).μ () * ∑ a, (K d).κ () () a ≤ 1 * 1 :=
            mul_le_mul' (by simpa [Core.mass] using hK d) ((K d).hκ () ())
        _ = 1 := one_mul 1
    · funext u
      simp only [P0.den, Core.val, zero_mul, zero_add]
      split_ifs with h
      · rw [hval]; simp only [Core.val, one_mul]; try ring
      · simp

/-- **Every program denotes an element of the recipe's calculus.** -/
theorem P0.den_mem_recipe [Nonempty X] [Nonempty X'] (p : P0 X Y X' Y') :
    p.den ∈ Mix {z | z ∈ tD X Y X' Y' ∧ ∀ u, z u = 0 ∨ z u = 1} := by
  rw [recipe_eq_sequentialG]; exact p.sound

/-! ### Definability of certain elements -/

/-- Halt exactly when `b` holds. -/
def PEnd.ofBool (b : Bool) : PEnd := if b then .halt else .diverge

theorem PEnd.den_ofBool (b : Bool) : (PEnd.ofBool b).den = if b then 1 else 0 := by
  cases b <;> rfl

/-- **Certain elements are definable**: every `{0,1}`-valued element of the probabilistic
coherence space is the denotation of a deterministic program. -/
theorem P0.sharp_definable [Nonempty X] [Nonempty X'] {z : (X × Y) × (X' × Y') → ℝ≥0∞}
    (hz : z ∈ tD X Y X' Y') (h01 : ∀ u, z u = 0 ∨ z u = 1) : ∃ p : P0 X Y X' Y', p.den = z := by
  classical
  have hzero : ∀ u, z u ≠ 1 → z u = 0 := fun u h => (h01 u).resolve_right h
  rcases (sharp_tD_iff h01).1 hz with ⟨a, cf, hT⟩ | ⟨c, af, hT⟩
  · refine ⟨.callF a fun b => .call (cf b) fun d => PEnd.ofBool (decide (z ((a, b), (cf b, d)) = 1)),
      ?_⟩
    funext u
    obtain ⟨⟨a', b⟩, ⟨c', d⟩⟩ := u
    simp only [P0.den, POne.den, PEnd.den_ofBool]
    by_cases ha : a' = a
    · subst ha
      by_cases hc : c' = cf b
      · subst hc
        rw [if_pos rfl, if_pos rfl]
        by_cases h1 : z ((a', b), (cf b, d)) = 1
        · simp [h1]
        · simp [h1, hzero _ h1]
      · rw [if_pos rfl, if_neg hc]
        exact (hzero _ fun h1 => hc (hT _ h1).2).symm
    · rw [if_neg ha]
      exact (hzero _ fun h1 => ha (hT _ h1).1).symm
  · refine ⟨.callG c fun d => .call (af d) fun b => PEnd.ofBool (decide (z ((af d, b), (c, d)) = 1)),
      ?_⟩
    funext u
    obtain ⟨⟨a', b⟩, ⟨c', d⟩⟩ := u
    simp only [P0.den, POne.den, PEnd.den_ofBool]
    by_cases hc : c' = c
    · subst hc
      by_cases ha : a' = af d
      · subst ha
        rw [if_pos rfl, if_pos rfl]
        by_cases h1 : z ((af d, b), (c', d)) = 1
        · simp [h1]
        · simp [h1, hzero _ h1]
      · rw [if_pos rfl, if_neg ha]
        exact (hzero _ fun h1 => ha (hT _ h1).2).symm
    · rw [if_neg hc]
      exact (hzero _ fun h1 => hc (hT _ h1).1).symm

/-- **The calculus is exactly the set of denotations of programs.** -/
theorem recipe_eq_denotations [Nonempty X] [Nonempty X'] :
    Mix {z | z ∈ tD X Y X' Y' ∧ ∀ u, z u = 0 ∨ z u = 1} = Set.range (P0.den (X := X) (Y := Y)
      (X' := X') (Y' := Y')) := by
  apply le_antisymm
  · rintro _ ⟨n, w, s, hs, hw, rfl⟩
    choose p hp using fun i => P0.sharp_definable (hs i).1 (hs i).2
    refine ⟨.choose n w (le_of_eq hw) p, ?_⟩
    funext u
    simp only [P0.den, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hp]
  · rintro _ ⟨p, rfl⟩
    exact p.den_mem_recipe

end ConstructiveProb.PCS.General
