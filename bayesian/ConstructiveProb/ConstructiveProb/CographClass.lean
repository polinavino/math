/-
# The exact condition at second order, for additive types

`second_order_iff`: for `X, Y` built from `1` with `&` and `⊕`, the calculus of `(X ⊗ Y)^⊥` equals
its PCS iff the coherence graph of `X` or of `Y` has no induced four-cycle.

* `GIso`: bijections of webs preserving and reflecting coherence. They give retracts.
* `tree_of_noC4`: a code without an induced four-cycle is isomorphic to a forest code. In a `&`
  of two codes one side is a clique, since two incoherent pairs, one on each side, form a
  four-cycle, and a clique joined to a forest code is a forest code.
* `retractSwap`: `B ⊗ A` is a retract of `A ⊗ B`.
-/
import ConstructiveProb.CographPCS

open scoped ENNReal
open Finset

namespace ConstructiveProb.Cograph

open ACode TCode ConstructiveProb.Linear
open ConstructiveProb.PCS (orth pairing)

/-! ### Isomorphisms of codes -/

/-- A bijection of webs preserving and reflecting coherence. -/
structure GIso (a b : ACode) where
  e : W a ≃ W b
  coh_iff : ∀ x y, ACode.coh a x y ↔ ACode.coh b (e x) (e y)

namespace GIso

def refl (a : ACode) : GIso a a := ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩

def trans {a b c : ACode} (I : GIso a b) (J : GIso b c) : GIso a c :=
  ⟨I.e.trans J.e, fun x y => (I.coh_iff x y).trans (J.coh_iff _ _)⟩

def plus {a b a' b' : ACode} (I : GIso a a') (J : GIso b b') :
    GIso (ACode.plus a b) (ACode.plus a' b') :=
  ⟨Equiv.sumCongr I.e J.e, by
    rintro (x | x) (y | y)
    · exact I.coh_iff x y
    · exact Iff.rfl
    · exact Iff.rfl
    · exact J.coh_iff x y⟩

def wth {a b a' b' : ACode} (I : GIso a a') (J : GIso b b') :
    GIso (ACode.wth a b) (ACode.wth a' b') :=
  ⟨Equiv.sumCongr I.e J.e, by
    rintro (x | x) (y | y)
    · exact I.coh_iff x y
    · exact Iff.rfl
    · exact Iff.rfl
    · exact J.coh_iff x y⟩

def comm (a b : ACode) : GIso (ACode.wth a b) (ACode.wth b a) :=
  ⟨Equiv.sumComm _ _, by rintro (x | x) (y | y) <;> exact Iff.rfl⟩

def assoc (a b c : ACode) : GIso (ACode.wth (ACode.wth a b) c) (ACode.wth a (ACode.wth b c)) :=
  ⟨Equiv.sumAssoc _ _ _, by rintro ((x | x) | x) ((y | y) | y) <;> exact Iff.rfl⟩

end GIso

/-! ### Isomorphic codes are retracts of each other -/

theorem push_equiv {E F : Type} [Fintype E] [DecidableEq F] (e : E ≃ F) (x : E → ℝ≥0∞) :
    push e x = fun y => x (e.symm y) := by
  funext y
  simp only [push]
  rw [Finset.sum_eq_single (e.symm y)
    (fun d _ h => if_neg fun h' => h (by rw [← h', Equiv.symm_apply_apply])) (by simp)]
  simp

/-- Precomposing with a map that reflects coherence keeps elements of the PCS. -/
theorem comp_mem_P {a b : ACode} (f : W a → W b)
    (hf : ∀ x y, ACode.coh b (f x) (f y) → ACode.coh a x y) {z : W b → ℝ≥0∞}
    (hz : z ∈ P b.toFm) : (fun x => z (f x)) ∈ P a.toFm := by
  rw [← recipe_code b] at hz
  rw [← recipe_code a]
  obtain ⟨n, w, s, hs, hw, rfl⟩ := hz
  have : (fun x => (∑ i, w i • s i) (f x)) = ∑ i, w i • (fun x => s i (f x)) := by
    funext x; simp only [Finset.sum_apply, Pi.smul_apply]
  rw [this]
  refine ConstructiveProb.mem_Mix_of_fintype _ _ (fun i => ⟨?_, fun x => (hs i).2 _⟩) hw
  refine clique_mem_P a _ (fun x => (hs i).2 _) fun x y hx hy => hf x y ?_
  exact (coh_toFm b _ _).1 (sharp_isClique b.toFm (hs i).1 (hs i).2 _ _ hx hy)

/-- **An isomorphism of codes is a retract.** -/
def GIso.retract {a b : ACode} (I : GIso a b) : Retract a.toFm b.toFm where
  j := I.e
  inj := I.e.injective
  push_mem x hx := by
    rw [push_equiv]
    refine comp_mem_P I.e.symm (fun x y h => ?_) hx
    have := (I.coh_iff _ _).1 h
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  pull_mem z hz := comp_mem_P I.e (fun x y h => (I.coh_iff x y).2 h) hz

/-! ### Symmetry of the tensor -/

theorem tens_swap_mem {A B : Fm} {z : web (Fm.tens B A) → ℝ≥0∞} (hz : z ∈ P (Fm.tens B A)) :
    (fun p : web A × web B => z p.swap) ∈ P (Fm.tens A B) := by
  have hz' : z ∈ orth (orth {w | ∃ u ∈ P B, ∃ v ∈ P A, w = tvec u v}) := hz
  show _ ∈ orth (orth {w | ∃ u ∈ P A, ∃ v ∈ P B, w = tvec u v})
  intro f hf
  have key : pairing f (fun p : web A × web B => z p.swap) =
      pairing (fun q : web B × web A => f q.swap) z := by
    simp only [pairing]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun p => rfl
  rw [key]
  refine hz' _ ?_
  rintro _ ⟨u, hu, v, hv, rfl⟩
  have : pairing (tvec u v) (fun q : web B × web A => f q.swap) = pairing (tvec v u) f := by
    simp only [pairing, tvec]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun q => by
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]; ring
  rw [this]
  exact hf _ ⟨v, hv, u, hu, rfl⟩

/-- `B ⊗ A` is a retract of `A ⊗ B`. -/
def retractSwap (A B : Fm) : Retract (Fm.tens A B) (Fm.tens B A) where
  j := Equiv.prodComm (web A) (web B)
  inj := (Equiv.prodComm (web A) (web B)).injective
  push_mem x hx := by
    rw [push_equiv (E := web (Fm.tens A B)) (F := web (Fm.tens B A))]
    exact tens_swap_mem hx
  pull_mem z hz := tens_swap_mem hz

/-! ### Codes without four-cycles are forest codes -/

/-- The coherence graph of the code has an induced four-cycle. -/
def HasC4 (a : ACode) : Prop :=
  ∃ p q r s : W a, ACode.coh a p q ∧ ACode.coh a q r ∧ ACode.coh a r s ∧ ACode.coh a s p ∧
    ¬ ACode.coh a p r ∧ ¬ ACode.coh a q s

theorem hasC4_iff (a : ACode) : HasC4 a ↔ Nonempty (C4 a.toFm) := by
  constructor
  · rintro ⟨p, q, r, s, h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨p, q, r, s, (coh_toFm a _ _).2 h1, (coh_toFm a _ _).2 h2, (coh_toFm a _ _).2 h3,
      (coh_toFm a _ _).2 h4, fun h => h5 ((coh_toFm a _ _).1 h),
      fun h => h6 ((coh_toFm a _ _).1 h)⟩⟩
  · rintro ⟨Q⟩
    exact ⟨Q.a, Q.b, Q.c, Q.d, (coh_toFm a _ _).1 Q.hab, (coh_toFm a _ _).1 Q.hbc,
      (coh_toFm a _ _).1 Q.hcd, (coh_toFm a _ _).1 Q.hda, fun h => Q.hac ((coh_toFm a _ _).2 h),
      fun h => Q.hbd ((coh_toFm a _ _).2 h)⟩

theorem HasC4.plusL {a b : ACode} : HasC4 a → HasC4 (ACode.plus a b) :=
  fun ⟨p, q, r, s, h⟩ => ⟨Sum.inl p, Sum.inl q, Sum.inl r, Sum.inl s, h⟩

theorem HasC4.plusR {a b : ACode} : HasC4 b → HasC4 (ACode.plus a b) :=
  fun ⟨p, q, r, s, h⟩ => ⟨Sum.inr p, Sum.inr q, Sum.inr r, Sum.inr s, h⟩

theorem HasC4.wthL {a b : ACode} : HasC4 a → HasC4 (ACode.wth a b) :=
  fun ⟨p, q, r, s, h⟩ => ⟨Sum.inl p, Sum.inl q, Sum.inl r, Sum.inl s, h⟩

theorem HasC4.wthR {a b : ACode} : HasC4 b → HasC4 (ACode.wth a b) :=
  fun ⟨p, q, r, s, h⟩ => ⟨Sum.inr p, Sum.inr q, Sum.inr r, Sum.inr s, h⟩

/-- All points are coherent. -/
def Complete (a : ACode) : Prop := ∀ x y, ACode.coh a x y

theorem nonempty_W : ∀ a : ACode, Nonempty (W a)
  | ACode.one => ⟨pt⟩
  | ACode.wth a _ => let ⟨x⟩ := nonempty_W a; ⟨Sum.inl x⟩
  | ACode.plus a _ => let ⟨x⟩ := nonempty_W a; ⟨Sum.inl x⟩

theorem not_complete_plus (a b : ACode) : ¬ Complete (ACode.plus a b) := fun h => by
  obtain ⟨x⟩ := nonempty_W a
  obtain ⟨y⟩ := nonempty_W b
  exact h (Sum.inl x) (Sum.inr y)

/-- In a `&` without a four-cycle, one side is a clique. -/
theorem complete_or {a b : ACode} (h : ¬ HasC4 (ACode.wth a b)) : Complete a ∨ Complete b := by
  by_contra hc
  obtain ⟨ha, hb⟩ := not_or.1 hc
  simp only [Complete, not_forall] at ha hb
  obtain ⟨x1, x2, hx⟩ := ha
  obtain ⟨y1, y2, hy⟩ := hb
  exact h ⟨Sum.inl x1, Sum.inr y1, Sum.inl x2, Sum.inr y2, trivial, trivial, trivial, trivial,
    hx, hy⟩

/-- A clique joined to a forest code is a forest code. -/
theorem join_complete : ∀ (a : ACode), Complete a → ∀ (b : ACode) (t : TCode), GIso b t.toA →
    ∃ t' : TCode, Nonempty (GIso (ACode.wth a b) t'.toA)
  | ACode.one, _, b, t, I =>
    ⟨TCode.cone t, ⟨(GIso.comm ACode.one b).trans (GIso.wth I (GIso.refl ACode.one))⟩⟩
  | ACode.wth a1 a2, h, b, t, I => by
    obtain ⟨t2, ⟨I2⟩⟩ := join_complete a2 (fun x y => h (Sum.inr x) (Sum.inr y)) b t I
    obtain ⟨t1, ⟨I1⟩⟩ := join_complete a1 (fun x y => h (Sum.inl x) (Sum.inl y)) _ t2 I2
    exact ⟨t1, ⟨(GIso.assoc a1 a2 b).trans I1⟩⟩
  | ACode.plus a1 a2, h, _, _, _ => absurd h (not_complete_plus a1 a2)

/-- **A code without an induced four-cycle is a forest code**, up to isomorphism. -/
theorem tree_of_noC4 : ∀ a : ACode, ¬ HasC4 a → ∃ t : TCode, Nonempty (GIso a t.toA)
  | ACode.one, _ => ⟨TCode.one, ⟨GIso.refl _⟩⟩
  | ACode.plus a b, h => by
    obtain ⟨ta, ⟨Ia⟩⟩ := tree_of_noC4 a fun h' => h h'.plusL
    obtain ⟨tb, ⟨Ib⟩⟩ := tree_of_noC4 b fun h' => h h'.plusR
    exact ⟨TCode.plus ta tb, ⟨GIso.plus Ia Ib⟩⟩
  | ACode.wth a b, h => by
    rcases complete_or h with ha | hb
    · obtain ⟨tb, ⟨Ib⟩⟩ := tree_of_noC4 b fun h' => h h'.wthR
      exact join_complete a ha b tb Ib
    · obtain ⟨ta, ⟨Ia⟩⟩ := tree_of_noC4 a fun h' => h h'.wthL
      obtain ⟨t', ⟨I⟩⟩ := join_complete b hb a ta Ia
      exact ⟨t', ⟨(GIso.comm a b).trans I⟩⟩

/-! ### The exact condition -/

/-- **The exact condition at second order for additive types.** For `X, Y` built from `1` with `&`
and `⊕`, the calculus of `(X ⊗ Y)^⊥` equals its PCS iff the coherence graph of `X` or of `Y` has
no induced four-cycle. -/
theorem second_order_iff (a b : ACode) :
    recipe (Fm.neg (Fm.tens a.toFm b.toFm)) = P (Fm.neg (Fm.tens a.toFm b.toFm)) ↔
      ¬ (HasC4 a ∧ HasC4 b) := by
  constructor
  · rintro h ⟨ha, hb⟩
    obtain ⟨QA⟩ := (hasC4_iff a).1 ha
    obtain ⟨QB⟩ := (hasC4_iff b).1 hb
    exact (gap_of_C4 QA QB).2 (by rw [h])
  · intro h
    by_contra hne
    rcases not_and_or.1 h with ha | hb
    · obtain ⟨t, ⟨I⟩⟩ := tree_of_noC4 a ha
      have R : Retract (Fm.neg (Fm.tens a.toFm b.toFm)) (Fm.neg (Fm.tens t.toA.toFm b.toFm)) :=
        (Retract.tens I.retract (Retract.refl _)).neg
      exact R.recipe_ne hne (second_order_noGap t b)
    · obtain ⟨t, ⟨I⟩⟩ := tree_of_noC4 b hb
      have R : Retract (Fm.neg (Fm.tens a.toFm b.toFm)) (Fm.neg (Fm.tens t.toA.toFm a.toFm)) :=
        ((retractSwap a.toFm b.toFm).trans (Retract.tens I.retract (Retract.refl _))).neg
      exact R.recipe_ne hne (second_order_noGap t a)

end ConstructiveProb.Cograph
