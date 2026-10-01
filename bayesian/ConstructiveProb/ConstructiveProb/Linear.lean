/-
# Multiplicative–additive linear logic: PCS and coherence semantics

Formulas are built from finite data types (`base n`, the flat type on `Fin n`) by linear
negation, `⊗` and `&`; `⅋`, `⊕` and `⊸` are defined through negation. Each formula `A` has a
finite web `web A`, a probabilistic coherence space `P A` (Danos–Ehrhard) and a coherence
relation `coh A` (Girard). For every formula:

* `isPCS_P`: `P A` is a probabilistic coherence space (biorthogonally closed, total, bounded);
* `recipe_subset_P`: mixtures of the certain (`{0,1}`-valued) elements of `P A` lie in `P A`;
* `sharp_isClique`: every certain element of `P A` is a clique of the coherence space `A`;
* `single_mem_P`, `pair_mem_P`: every singleton and every coherent pair is an element of `P A`.

The converse of `sharp_isClique` fails: `TensorGap.shannon_not_mem` gives a clique of the
coherence space `(T ⊗ T)^⊥` whose indicator is not an element of the PCS.
-/
import ConstructiveProb.Recipe

open scoped ENNReal
open Finset

namespace ConstructiveProb.Linear

open ConstructiveProb.PCS (orth pairing flat IsPCS orth_orth_orth subset_orth_orth isPCS_flat
  Mix_subset_orth)

/-- MALL formulas over finite data types. -/
inductive Fm where
  | base (n : ℕ)
  | neg (A : Fm)
  | tens (A B : Fm)
  | wth (A B : Fm)

namespace Fm

def par (A B : Fm) : Fm := neg (tens (neg A) (neg B))
def plus (A B : Fm) : Fm := neg (wth (neg A) (neg B))
def lolli (A B : Fm) : Fm := neg (tens A (neg B))

end Fm

open Fm

/-- The web of a formula. -/
@[reducible] def web : Fm → Type
  | base n => Fin n
  | neg A => web A
  | tens A B => web A × web B
  | wth A B => web A ⊕ web B

@[reducible] instance instFintypeWeb : (A : Fm) → Fintype (web A)
  | base n => inferInstanceAs (Fintype (Fin n))
  | neg A => instFintypeWeb A
  | tens A B => @instFintypeProd _ _ (instFintypeWeb A) (instFintypeWeb B)
  | wth A B => @instFintypeSum _ _ (instFintypeWeb A) (instFintypeWeb B)

@[reducible] instance instDecEqWeb : (A : Fm) → DecidableEq (web A)
  | base n => inferInstanceAs (DecidableEq (Fin n))
  | neg A => instDecEqWeb A
  | tens A B => @instDecidableEqProd _ _ (instDecEqWeb A) (instDecEqWeb B)
  | wth A B => @instDecidableEqSum _ _ (instDecEqWeb A) (instDecEqWeb B)

/-- Tensor of two vectors. -/
noncomputable def tvec {X Y : Type} (x : X → ℝ≥0∞) (y : Y → ℝ≥0∞) : X × Y → ℝ≥0∞ :=
  fun ab => x ab.1 * y ab.2

/-- Pairing of two vectors on a sum web. -/
noncomputable def svec {X Y : Type} (x : X → ℝ≥0∞) (y : Y → ℝ≥0∞) : X ⊕ Y → ℝ≥0∞
  | Sum.inl a => x a
  | Sum.inr b => y b

/-- The probabilistic coherence space of a formula. -/
def P : (A : Fm) → Set (web A → ℝ≥0∞)
  | base n => flat (Fin n)
  | neg A => orth (P A)
  | tens A B => orth (orth {z | ∃ x ∈ P A, ∃ y ∈ P B, z = tvec x y})
  | wth A B => {z | (fun a => z (Sum.inl a)) ∈ P A ∧ (fun b => z (Sum.inr b)) ∈ P B}

/-- The coherence relation (reflexive) of a formula. -/
def coh : (A : Fm) → web A → web A → Prop
  | base _ => fun x y => x = y
  | neg A => fun x y => x = y ∨ ¬ coh A x y
  | tens A B => fun s t => coh A s.1 t.1 ∧ coh B s.2 t.2
  | wth A B => fun s t => match s, t with
    | Sum.inl a, Sum.inl a' => coh A a a'
    | Sum.inr b, Sum.inr b' => coh B b b'
    | _, _ => True

theorem coh_refl : ∀ (A : Fm) (s : web A), coh A s s
  | base _, _ => rfl
  | neg _, _ => Or.inl rfl
  | tens A B, s => ⟨coh_refl A s.1, coh_refl B s.2⟩
  | wth A _, Sum.inl a => coh_refl A a
  | wth _ B, Sum.inr b => coh_refl B b

/-! ### Generic facts about orthogonals -/

section Generic

variable {E : Type} [Fintype E] [DecidableEq E]

theorem zero_mem_orth (S : Set (E → ℝ≥0∞)) : (0 : E → ℝ≥0∞) ∈ orth S := fun x _ => by
  simp [pairing]

theorem orth_downward {S : Set (E → ℝ≥0∞)} {y z : E → ℝ≥0∞} (hz : z ∈ orth S) (h : y ≤ z) :
    y ∈ orth S := fun x hx =>
  le_trans (Finset.sum_le_sum fun e _ => mul_le_mul_left' (h e) _) (hz x hx)

theorem pairing_single (s : E) (x : E → ℝ≥0∞) : pairing (Pi.single s 1) x = x s := by
  simp [pairing, Pi.single_apply]

theorem pairing_single' (s : E) (x : E → ℝ≥0∞) : pairing x (Pi.single s 1) = x s := by
  simp [pairing, Pi.single_apply]

theorem pairing_add_right (x y z : E → ℝ≥0∞) : pairing x (y + z) = pairing x y + pairing x z := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_add_left (x y z : E → ℝ≥0∞) : pairing (y + z) x = pairing y x + pairing z x := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

/-- The indicator of a two-element set `{s, t}`. -/
noncomputable def pr (s t : E) : E → ℝ≥0∞ := Pi.single s 1 + Pi.single t 1

end Generic

/-! ### Structural facts, by induction on formulas -/

theorem zero_mem_P : ∀ A : Fm, (0 : web A → ℝ≥0∞) ∈ P A
  | base n => show ∑ a, (0 : web (base n) → ℝ≥0∞) a ≤ 1 by simp
  | neg A => zero_mem_orth _
  | tens A B => zero_mem_orth _
  | wth A B => ⟨zero_mem_P A, zero_mem_P B⟩

theorem P_downward : ∀ (A : Fm) {y z : web A → ℝ≥0∞}, z ∈ P A → y ≤ z → y ∈ P A
  | base n, y, z, hz, h => le_trans (Finset.sum_le_sum fun e _ => h e) (hz : ∑ e, z e ≤ 1)
  | neg A, _, _, hz, h => orth_downward hz h
  | tens A B, _, _, hz, h => orth_downward hz h
  | wth A B, _, _, hz, h => ⟨P_downward A hz.1 fun a => h (Sum.inl a),
      P_downward B hz.2 fun b => h (Sum.inr b)⟩

theorem tvec_single {X Y : Type} [DecidableEq X] [DecidableEq Y] (a : X) (b : Y) :
    tvec (Pi.single a (1 : ℝ≥0∞)) (Pi.single b 1) = Pi.single (a, b) 1 := by
  funext ab; rcases ab with ⟨a', b'⟩
  by_cases ha : a' = a <;> by_cases hb : b' = b <;> simp [tvec, Pi.single_apply, ha, hb]

theorem pairing_tvec {X Y : Type} [Fintype X] [Fintype Y] (x u : X → ℝ≥0∞) (y v : Y → ℝ≥0∞) :
    pairing (tvec x y) (tvec u v) = pairing x u * pairing y v := by
  simp only [pairing, tvec, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The three invariants: singletons are elements and every element is bounded by `1` at each
point (`C1`); coherent pairs are elements (`C2`); every element sums to at most `1` on every
incoherent pair (`I2`). -/
theorem invariants : ∀ A : Fm,
    (∀ s : web A, Pi.single s 1 ∈ P A ∧ ∀ x ∈ P A, x s ≤ 1) ∧
    (∀ s t : web A, s ≠ t → coh A s t → pr s t ∈ P A) ∧
    (∀ s t : web A, s ≠ t → ¬ coh A s t → ∀ x ∈ P A, x s + x t ≤ 1)
  | base n => by
    refine ⟨fun s => ⟨show ∑ a, (Pi.single s 1 : web (base n) → ℝ≥0∞) a ≤ 1 by simp,
      fun x hx => ?_⟩, fun s t hst h => absurd h hst,
      fun s t hst _ x hx => ?_⟩
    · exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ s)).trans
        (hx : ∑ e, x e ≤ 1)
    · rw [← Finset.sum_pair hst]
      exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans (hx : ∑ e, x e ≤ 1)
  | neg A => by
    obtain ⟨c1, c2, i2⟩ := invariants A
    refine ⟨fun s => ⟨fun x hx => ?_, fun y hy => ?_⟩, fun s t hst h => ?_,
      fun s t hst h y hy => ?_⟩
    · rw [pairing_single']; exact (c1 s).2 x hx
    · have := hy _ (c1 s).1; rwa [pairing_single] at this
    · have hn : ¬ coh A s t := by
        rcases h with h | h
        · exact absurd h hst
        · exact h
      intro x hx
      rw [pr, pairing_add_right, pairing_single', pairing_single']
      exact i2 s t hst hn x hx
    · have hc : coh A s t := by
        by_contra hn; exact h (Or.inr hn)
      have := hy _ (c2 s t hst hc)
      rwa [pr, pairing_add_left, pairing_single, pairing_single] at this
  | tens A B => by
    obtain ⟨c1A, c2A, i2A⟩ := invariants A
    obtain ⟨c1B, c2B, i2B⟩ := invariants B
    have gen_mem : ∀ {x y}, x ∈ P A → y ∈ P B → tvec x y ∈ P (tens A B) := fun hx hy =>
      subset_orth_orth _ ⟨_, hx, _, hy, rfl⟩
    -- an indicator of one or two points of `A` (resp. `B`) that is an element
    have one_or_pair : ∀ (C : Fm) (a a' : web C), coh C a a' →
        (∀ s : web C, Pi.single s 1 ∈ P C ∧ ∀ x ∈ P C, x s ≤ 1) →
        (∀ s t : web C, s ≠ t → coh C s t → pr s t ∈ P C) →
        ∃ u ∈ P C, 1 ≤ u a ∧ 1 ≤ u a' := by
      intro C a a' hc c1 c2
      by_cases h : a = a'
      · subst h; exact ⟨_, (c1 a).1, by simp, by simp⟩
      · exact ⟨_, c2 a a' h hc, by simp [pr, Pi.single_apply, h],
          by simp [pr, Pi.single_apply, Ne.symm h]⟩
    refine ⟨fun s => ⟨?_, fun z hz => ?_⟩, fun s t hst h => ?_, fun s t hst h z hz => ?_⟩
    · rw [← tvec_single]; exact gen_mem (c1A s.1).1 (c1B s.2).1
    · have hd : Pi.single s 1 ∈ orth {z | ∃ x ∈ P A, ∃ y ∈ P B, z = tvec x y} := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        rw [pairing_single']
        exact (mul_le_mul' ((c1A s.1).2 x hx) ((c1B s.2).2 y hy)).trans (by simp)
      have := hz _ hd; rwa [pairing_single] at this
    · obtain ⟨u, hu, hu1, hu2⟩ := one_or_pair A s.1 t.1 h.1 c1A c2A
      obtain ⟨v, hv, hv1, hv2⟩ := one_or_pair B s.2 t.2 h.2 c1B c2B
      refine P_downward (tens A B) (gen_mem hu hv) fun e => ?_
      simp only [pr, Pi.add_apply, Pi.single_apply, tvec]
      by_cases hs : e = s <;> by_cases ht : e = t
      · exact absurd (hs.symm.trans ht) hst
      · subst hs; simp [ht]; exact one_le_mul hu1 hv1
      · subst ht; simp [hs]; exact one_le_mul hu2 hv2
      · simp [hs, ht]
    · have hd : pr s t ∈ orth {z | ∃ x ∈ P A, ∃ y ∈ P B, z = tvec x y} := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        rw [pr, pairing_add_right, pairing_single', pairing_single']
        simp only [tvec]
        by_cases hA : coh A s.1 t.1
        · have hB : ¬ coh B s.2 t.2 := fun hB => h ⟨hA, hB⟩
          have hne : s.2 ≠ t.2 := fun e => hB (e ▸ coh_refl B s.2)
          calc x s.1 * y s.2 + x t.1 * y t.2 ≤ 1 * y s.2 + 1 * y t.2 := by
                gcongr
                · exact (c1A s.1).2 x hx
                · exact (c1A t.1).2 x hx
            _ ≤ 1 := by simpa using i2B s.2 t.2 hne hB y hy
        · have hne : s.1 ≠ t.1 := fun e => hA (e ▸ coh_refl A s.1)
          calc x s.1 * y s.2 + x t.1 * y t.2 ≤ x s.1 * 1 + x t.1 * 1 := by
                gcongr
                · exact (c1B s.2).2 y hy
                · exact (c1B t.2).2 y hy
            _ ≤ 1 := by simpa using i2A s.1 t.1 hne hA x hx
      have := hz _ hd
      rwa [pr, pairing_add_left, pairing_single, pairing_single] at this
  | wth A B => by
    obtain ⟨c1A, c2A, i2A⟩ := invariants A
    obtain ⟨c1B, c2B, i2B⟩ := invariants B
    refine ⟨fun s => ?_, fun s t hst h => ?_, fun s t hst h z hz => ?_⟩
    · rcases s with a | b
      · refine ⟨⟨?_, ?_⟩, fun z hz => (c1A a).2 _ hz.1⟩
        · convert (c1A a).1 using 1; funext a'; by_cases h : a' = a <;> simp [Pi.single_apply, h, Sum.inl_injective.eq_iff]
        · convert zero_mem_P B using 1; funext b'; simp [Pi.single_apply]
      · refine ⟨⟨?_, ?_⟩, fun z hz => (c1B b).2 _ hz.2⟩
        · convert zero_mem_P A using 1; funext a'; simp [Pi.single_apply]
        · convert (c1B b).1 using 1; funext b'; by_cases h : b' = b <;> simp [Pi.single_apply, h, Sum.inr_injective.eq_iff]
    · rcases s with a | b <;> rcases t with a' | b'
      · have hne : a ≠ a' := fun e => hst (by rw [e])
        refine ⟨?_, ?_⟩
        · convert c2A a a' hne h using 1
          funext x; by_cases h1 : x = a <;> by_cases h2 : x = a' <;>
            simp [pr, Pi.single_apply, h1, h2]
        · convert zero_mem_P B using 1; funext y; simp [pr, Pi.single_apply]
      · refine ⟨?_, ?_⟩
        · convert (c1A a).1 using 1; funext x; by_cases h1 : x = a <;> simp [pr, Pi.single_apply, h1]
        · convert (c1B b').1 using 1; funext y; by_cases h1 : y = b' <;>
            simp [pr, Pi.single_apply, h1]
      · refine ⟨?_, ?_⟩
        · convert (c1A a').1 using 1; funext x; by_cases h1 : x = a' <;>
            simp [pr, Pi.single_apply, h1]
        · convert (c1B b).1 using 1; funext y; by_cases h1 : y = b <;> simp [pr, Pi.single_apply, h1]
      · have hne : b ≠ b' := fun e => hst (by rw [e])
        refine ⟨?_, ?_⟩
        · convert zero_mem_P A using 1; funext x; simp [pr, Pi.single_apply]
        · convert c2B b b' hne h using 1
          funext y; by_cases h1 : y = b <;> by_cases h2 : y = b' <;>
            simp [pr, Pi.single_apply, h1, h2]
    · rcases s with a | b <;> rcases t with a' | b'
      · exact i2A a a' (fun e => hst (by rw [e])) h _ hz.1
      · exact absurd trivial h
      · exact absurd trivial h
      · exact i2B b b' (fun e => hst (by rw [e])) h _ hz.2

/-- **Singletons are elements**, at every formula. -/
theorem single_mem_P (A : Fm) (s : web A) : Pi.single s 1 ∈ P A := ((invariants A).1 s).1

/-- **Coherent pairs are elements**, at every formula. -/
theorem pair_mem_P (A : Fm) {s t : web A} (hst : s ≠ t) (h : coh A s t) : pr s t ∈ P A :=
  (invariants A).2.1 s t hst h

/-- **Every certain element of the PCS is a clique of the coherence space**, at every formula. -/
theorem sharp_isClique (A : Fm) {z : web A → ℝ≥0∞} (hz : z ∈ P A)
    (h01 : ∀ s, z s = 0 ∨ z s = 1) : ∀ s t, z s = 1 → z t = 1 → coh A s t := by
  intro s t hs ht
  by_contra hc
  have hst : s ≠ t := fun e => hc (e ▸ coh_refl A s)
  have := (invariants A).2.2 s t hst hc z hz
  rw [hs, ht] at this
  norm_num at this

/-! ### Every formula denotes a PCS -/

theorem orth_total_bounded {E : Type} [Fintype E] [DecidableEq E] {Q : Set (E → ℝ≥0∞)}
    (hQ : IsPCS Q) : IsPCS (orth Q) := by
  refine ⟨orth_orth_orth Q, fun e => ?_, fun e => ?_⟩
  · obtain ⟨M, hM, hbd⟩ := hQ.bounded e
    refine ⟨Pi.single e (max M 1)⁻¹, fun x hx => ?_, by simpa using hM⟩
    rw [pairing]
    simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    calc x e * (max M 1)⁻¹ ≤ max M 1 * (max M 1)⁻¹ :=
          mul_le_mul_right' ((hbd x hx).trans (le_max_left _ _)) _
      _ = 1 := ENNReal.mul_inv_cancel (by positivity) (max_ne_top hM ENNReal.one_ne_top)
  · obtain ⟨x, hx, hx0⟩ := hQ.total e
    obtain ⟨M, hM, hbd⟩ := hQ.bounded e
    have hxt : x e ≠ ⊤ := ne_top_of_le_ne_top hM (hbd x hx)
    refine ⟨(x e)⁻¹, ENNReal.inv_ne_top.2 hx0, fun y hy => ?_⟩
    have h1 : x e * y e ≤ 1 :=
      (Finset.single_le_sum (f := fun e => x e * y e) (fun _ _ => bot_le)
        (Finset.mem_univ e)).trans (hy x hx)
    rw [ENNReal.le_inv_iff_mul_le, mul_comm]; exact h1

/-- **Every formula denotes a probabilistic coherence space.** -/
theorem isPCS_P : ∀ A : Fm, IsPCS (P A)
  | base n => isPCS_flat
  | neg A => orth_total_bounded (isPCS_P A)
  | tens A B => by
    refine ⟨orth_orth_orth _, fun e => ⟨_, single_mem_P _ e, by simp⟩, fun e => ?_⟩
    obtain ⟨u, hu, hu0⟩ := (orth_total_bounded (isPCS_P A)).total e.1
    obtain ⟨v, hv, hv0⟩ := (orth_total_bounded (isPCS_P B)).total e.2
    obtain ⟨Mu, hMu, hbu⟩ := (orth_total_bounded (isPCS_P A)).bounded e.1
    obtain ⟨Mv, hMv, hbv⟩ := (orth_total_bounded (isPCS_P B)).bounded e.2
    have hd : tvec u v ∈ orth {z | ∃ x ∈ P A, ∃ y ∈ P B, z = tvec x y} := by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      rw [pairing_tvec]
      exact (mul_le_mul' (hu x hx) (hv y hy)).trans (by simp)
    have hfin : u e.1 * v e.2 ≠ ⊤ := ENNReal.mul_ne_top (ne_top_of_le_ne_top hMu (hbu u hu))
      (ne_top_of_le_ne_top hMv (hbv v hv))
    refine ⟨(u e.1 * v e.2)⁻¹, ENNReal.inv_ne_top.2 (mul_ne_zero hu0 hv0), fun z hz => ?_⟩
    have h1 : tvec u v e * z e ≤ 1 :=
      (Finset.single_le_sum (f := fun e => tvec u v e * z e) (fun _ _ => bot_le)
        (Finset.mem_univ e)).trans (hz _ hd)
    rw [ENNReal.le_inv_iff_mul_le, mul_comm]; exact h1
  | wth A B => by
    have hA := isPCS_P A
    have hB := isPCS_P B
    -- `P (A & B)` is the orthogonal of the injected duals
    let S : Set (web (wth A B) → ℝ≥0∞) :=
      {w | (∃ u ∈ orth (P A), w = svec u 0) ∨ (∃ v ∈ orth (P B), w = svec 0 v)}
    have hpair : ∀ (z : web (wth A B) → ℝ≥0∞) (u : web A → ℝ≥0∞) (v : web B → ℝ≥0∞),
        pairing (svec u v) z = pairing u (fun a => z (Sum.inl a)) +
          pairing v (fun b => z (Sum.inr b)) := by
      intro z u v
      simp [pairing, Fintype.sum_sum_type, svec]
    have hS : P (wth A B) = orth S := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩ w hw
        rcases hw with ⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩
        · rw [hpair]; simp only [pairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
            add_zero]
          have := hu _ h1; simpa [pairing, mul_comm] using this
        · rw [hpair]; simp only [pairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
            zero_add]
          have := hv _ h2; simpa [pairing, mul_comm] using this
      · intro h
        refine ⟨?_, ?_⟩
        · rw [← hA.closed]
          intro u hu
          have := h _ (Or.inl ⟨u, hu, rfl⟩)
          rw [hpair] at this
          simpa [pairing, mul_comm] using this
        · rw [← hB.closed]
          intro v hv
          have := h _ (Or.inr ⟨v, hv, rfl⟩)
          rw [hpair] at this
          simpa [pairing, mul_comm] using this
    refine ⟨by rw [hS, orth_orth_orth], fun e => ⟨_, single_mem_P _ e, by simp⟩, fun e => ?_⟩
    rcases e with a | b
    · obtain ⟨M, hM, hb⟩ := hA.bounded a
      exact ⟨M, hM, fun z hz => hb _ hz.1⟩
    · obtain ⟨M, hM, hb⟩ := hB.bounded b
      exact ⟨M, hM, fun z hz => hb _ hz.2⟩

/-- **The recipe is contained in the PCS**, at every formula. -/
theorem recipe_subset_P (A : Fm) :
    Mix {z | z ∈ P A ∧ ∀ s, z s = 0 ∨ z s = 1} ⊆ P A := by
  rw [← (isPCS_P A).closed]
  exact Mix_subset_orth fun z hz => (isPCS_P A).closed.symm ▸ hz.1

/-- **Criterion (i)**, at every formula: the certain elements of the recipe's calculus are the
certain elements of the PCS. -/
theorem recipe_sharp_iff (A : Fm) {x : web A → ℝ≥0∞} (hx : ∀ s, x s = 0 ∨ x s = 1) :
    x ∈ Mix {z | z ∈ P A ∧ ∀ s, z s = 0 ∨ z s = 1} ↔ x ∈ P A :=
  ⟨fun h => recipe_subset_P A h, fun h => (sharp_mem_Mix_iff (fun _ hz => hz.2) hx).2 ⟨h, hx⟩⟩

end ConstructiveProb.Linear
