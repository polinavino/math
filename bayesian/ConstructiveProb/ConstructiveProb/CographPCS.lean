/-
# The second-order classification for additive types

`second_order_noGap`: for `X` built from `1` with `⊕` and `- & 1` (coherence graph the comparability
graph of a rooted forest) and `Y` built from `1` with `&` and `⊕` (a cograph), the calculus of
`(X ⊗ Y)^⊥` equals its PCS. With `gap_of_C4` this is the exact condition at second order: for two
such types, every `C4`-free cograph being a forest comparability graph, the gap occurs iff both
coherence graphs have an induced four-cycle.

* `IsPathInd`: paths of a forest code as `{0,1}`-vectors; path sums are sums along them.
* `clique_mem_P`: clique indicators of an additive code are elements of its PCS.
* `recipe_plus`, `recipe_code`: no gap at additive codes.
-/
import ConstructiveProb.CographCore

open scoped ENNReal
open Finset

namespace ConstructiveProb.Cograph

open ACode TCode ConstructiveProb.Linear
open ConstructiveProb.PCS (orth pairing)

/-! ### Paths as vectors -/

/-- The indicator of a path from a root (possibly empty). -/
def IsPathInd : (t : TCode) → (N t → ℝ) → Prop
  | TCode.one, a => a = 0 ∨ a = fun _ => 1
  | TCode.plus s u, a =>
      (∃ a1 : N s → ℝ, IsPathInd s a1 ∧ a = Sum.elim a1 (0 : N u → ℝ)) ∨
        (∃ a2 : N u → ℝ, IsPathInd u a2 ∧ a = Sum.elim (0 : N s → ℝ) a2)
  | TCode.cone u, a => a = 0 ∨
      ∃ a' : N u → ℝ, IsPathInd u a' ∧ a = Sum.elim a' (fun _ : W ACode.one => (1 : ℝ))

theorem sum_cone {M : Type*} [AddCommMonoid M] (u : TCode) (f : N (TCode.cone u) → M) :
    ∑ x, f x = ∑ x, f (Sum.inl x) + f (root u) := by
  rw [show (∑ x, f x) = ∑ x : W (ACode.wth u.toA ACode.one), f x from rfl, ACode.sum_wth,
    ACode.sum_one]; rfl

theorem sum_tplus {M : Type*} [AddCommMonoid M] (s u : TCode) (f : N (TCode.plus s u) → M) :
    ∑ x, f x = ∑ x, f (Sum.inl x) + ∑ x, f (Sum.inr x) :=
  ACode.sum_plus s.toA u.toA f

theorem sum_tone {M : Type*} [AddCommMonoid M] (f : N TCode.one → M) : ∑ x, f x = f ACode.pt :=
  ACode.sum_one f

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem pathInd_of_PathSums : ∀ (t : TCode) (Z : N t → V) (S : V), S ∈ PathSums t Z →
    ∃ a, IsPathInd t a ∧ S = ∑ x, a x • Z x
  | TCode.one, Z, S, hS => by
    rcases hS with rfl | hS
    · exact ⟨0, Or.inl rfl, by simp⟩
    · rw [Set.mem_singleton_iff.1 hS]
      exact ⟨fun _ => 1, Or.inr rfl, by rw [sum_tone]; simp⟩
  | TCode.plus s u, Z, S, hS => by
    rcases hS with hS | hS
    · obtain ⟨a1, h1, rfl⟩ := pathInd_of_PathSums s _ S hS
      refine ⟨Sum.elim a1 0, Or.inl ⟨a1, h1, rfl⟩, ?_⟩
      rw [sum_tplus]; simp
    · obtain ⟨a2, h2, rfl⟩ := pathInd_of_PathSums u _ S hS
      refine ⟨Sum.elim 0 a2, Or.inr ⟨a2, h2, rfl⟩, ?_⟩
      rw [sum_tplus]; simp
  | TCode.cone u, Z, S, hS => by
    rcases hS with rfl | ⟨S', hS', rfl⟩
    · exact ⟨0, Or.inl rfl, by simp⟩
    · obtain ⟨a', h', rfl⟩ := pathInd_of_PathSums u _ S' hS'
      refine ⟨Sum.elim a' (fun _ => 1), Or.inr ⟨a', h', rfl⟩, ?_⟩
      rw [sum_cone]
      show Z (root u) + _ = _
      simp only [Sum.elim_inl]
      rw [add_comm]; congr 1
      show Z (root u) = (1 : ℝ) • Z (root u); rw [one_smul]

theorem PathSums_of_pathInd : ∀ (t : TCode) (Z : N t → V) (a : N t → ℝ), IsPathInd t a →
    ∑ x, a x • Z x ∈ PathSums t Z
  | TCode.one, Z, a, ha => by
    rcases ha with rfl | rfl
    · simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]; exact Set.mem_insert _ _
    · rw [sum_tone, one_smul]; exact Set.mem_insert_of_mem _ rfl
  | TCode.plus s u, Z, a, ha => by
    rcases ha with ⟨a1, h1, rfl⟩ | ⟨a2, h2, rfl⟩
    · rw [sum_tplus]; simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul,
        Finset.sum_const_zero, add_zero]
      exact Or.inl (PathSums_of_pathInd s _ a1 h1)
    · rw [sum_tplus]; simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul,
        Finset.sum_const_zero, zero_add]
      exact Or.inr (PathSums_of_pathInd u _ a2 h2)
  | TCode.cone u, Z, a, ha => by
    rcases ha with rfl | ⟨a', h', rfl⟩
    · simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]; exact Set.mem_insert _ _
    · rw [sum_cone]
      refine Set.mem_insert_of_mem _ ⟨_, PathSums_of_pathInd u _ a' h', ?_⟩
      show Z (root u) + _ = _ + (1 : ℝ) • Z (root u)
      rw [one_smul, add_comm]; rfl

theorem pathInd_01 : ∀ (t : TCode) (a : N t → ℝ), IsPathInd t a → ∀ x, a x = 0 ∨ a x = 1
  | TCode.one, a, ha, x => by rcases ha with rfl | rfl <;> simp
  | TCode.plus s u, a, ha, x => by
    rcases ha with ⟨a1, h1, rfl⟩ | ⟨a2, h2, rfl⟩ <;> rcases x with x | x
    · exact pathInd_01 s a1 h1 x
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact pathInd_01 u a2 h2 x
  | TCode.cone u, a, ha, x => by
    rcases ha with rfl | ⟨a', h', rfl⟩
    · exact Or.inl rfl
    · rcases x with x | x
      · exact pathInd_01 u a' h' x
      · exact Or.inr rfl

theorem pathInd_clique : ∀ (t : TCode) (a : N t → ℝ), IsPathInd t a →
    ∀ x y, a x = 1 → a y = 1 → ACode.coh t.toA x y
  | TCode.one, _, _, _, _, _, _ => by simp [TCode.toA, ACode.coh]
  | TCode.plus s u, a, ha, x, y, hx, hy => by
    rcases ha with ⟨a1, h1, rfl⟩ | ⟨a2, h2, rfl⟩ <;> rcases x with x | x <;> rcases y with y | y
    · exact pathInd_clique s a1 h1 x y hx hy
    · exact absurd hy (by simp)
    · exact absurd hx (by simp)
    · exact absurd hx (by simp)
    · exact absurd hx (by simp)
    · exact absurd hx (by simp)
    · exact absurd hy (by simp)
    · exact pathInd_clique u a2 h2 x y hx hy
  | TCode.cone u, a, ha, x, y, hx, hy => by
    rcases ha with rfl | ⟨a', h', rfl⟩
    · exact absurd hx (by simp)
    · rcases x with x | x <;> rcases y with y | y
      · exact pathInd_clique u a' h' x y hx hy
      · trivial
      · trivial
      · show ACode.coh ACode.one x y; simp [ACode.coh]

/-- **Every clique lies on a path.** -/
theorem clique_le_path : ∀ (t : TCode) (c : N t → ℝ), (∀ x, c x = 0 ∨ c x = 1) →
    (∀ x y, c x = 1 → c y = 1 → ACode.coh t.toA x y) → ∃ a, IsPathInd t a ∧ c ≤ a
  | TCode.one, c, h01, _ => ⟨fun _ => 1, Or.inr rfl, fun x => by
      rcases h01 x with h | h <;> rw [h]; norm_num⟩
  | TCode.plus s u, c, h01, hc => by
    by_cases hA : ∃ x, c (Sum.inl x) = 1
    · obtain ⟨x0, hx0⟩ := hA
      have hB : ∀ y, c (Sum.inr y) = 0 := fun y =>
        (h01 _).resolve_right fun h => hc _ _ hx0 h
      obtain ⟨a1, h1, hle⟩ := clique_le_path s (fun x => c (Sum.inl x)) (fun x => h01 _)
        (fun x y hx hy => hc _ _ hx hy)
      refine ⟨Sum.elim a1 0, Or.inl ⟨a1, h1, rfl⟩, fun x => ?_⟩
      rcases x with x | x
      · exact hle x
      · show c (Sum.inr x) ≤ 0; rw [hB x]
    · push_neg at hA
      have hA' : ∀ x, c (Sum.inl x) = 0 := fun x => (h01 _).resolve_right (hA x)
      obtain ⟨a2, h2, hle⟩ := clique_le_path u (fun x => c (Sum.inr x)) (fun x => h01 _)
        (fun x y hx hy => hc _ _ hx hy)
      refine ⟨Sum.elim 0 a2, Or.inr ⟨a2, h2, rfl⟩, fun x => ?_⟩
      rcases x with x | x
      · show c (Sum.inl x) ≤ 0; rw [hA' x]
      · exact hle x
  | TCode.cone u, c, h01, hc => by
    obtain ⟨a', h', hle⟩ := clique_le_path u (fun x => c (Sum.inl x)) (fun x => h01 _)
      (fun x y hx hy => hc _ _ hx hy)
    refine ⟨Sum.elim a' (fun _ => 1), Or.inr ⟨a', h', rfl⟩, fun x => ?_⟩
    rcases x with x | x
    · exact hle x
    · show c (Sum.inr x) ≤ 1; rcases h01 (Sum.inr x) with h | h <;> rw [h]; norm_num

/-! ### Additive codes have the clique property and no gap -/

/-- The retract of `A` into `A ⊕ B`. -/
def retractInl (A B : Fm) : Retract A (Fm.plus A B) :=
  (Retract.negneg A).trans (Retract.wthL (Fm.neg A) (Fm.neg B)).neg

/-- The retract of `B` into `A ⊕ B`. -/
def retractInr (A B : Fm) : Retract B (Fm.plus A B) :=
  (Retract.negneg B).trans (Retract.wthR (Fm.neg B) (Fm.neg A)).neg

theorem push_inl_apply {A B : Fm} (x : web A → ℝ≥0∞) (p : web (Fm.plus A B)) :
    push (retractInl A B).j x p = match p with | Sum.inl a => x a | Sum.inr _ => 0 := by
  rcases p with a | b
  · exact push_apply_j (retractInl A B).inj x a
  · simp only [push]
    exact Finset.sum_eq_zero fun d _ => if_neg (by
      show (Sum.inl d : web A ⊕ web B) ≠ Sum.inr b; simp)

theorem push_inr_apply {A B : Fm} (x : web B → ℝ≥0∞) (p : web (Fm.plus A B)) :
    push (retractInr A B).j x p = match p with | Sum.inl _ => 0 | Sum.inr b => x b := by
  rcases p with a | b
  · simp only [push]
    exact Finset.sum_eq_zero fun d _ => if_neg (by
      show (Sum.inr d : web A ⊕ web B) ≠ Sum.inl a; simp)
  · exact push_apply_j (retractInr A B).inj x b

/-- **Clique indicators are elements of the PCS.** -/
theorem clique_mem_P : ∀ (a : ACode) (c : W a → ℝ≥0∞), (∀ x, c x = 0 ∨ c x = 1) →
    (∀ x y, c x = 1 → c y = 1 → ACode.coh a x y) → c ∈ P a.toFm
  | ACode.one, c, h01, _ => by
    show (∑ x : Fin 1, c x) ≤ 1
    rw [Fin.sum_univ_one]
    rcases h01 pt with h | h
    · exact (show c pt ≤ 1 by rw [h]; exact zero_le_one)
    · exact (show c pt ≤ 1 by rw [h])
  | ACode.wth a b, c, h01, hc =>
    ⟨clique_mem_P a _ (fun x => h01 _) (fun x y hx hy => hc _ _ hx hy),
     clique_mem_P b _ (fun x => h01 _) (fun x y hx hy => hc _ _ hx hy)⟩
  | ACode.plus a b, c, h01, hc => by
    by_cases hA : ∃ x, c (Sum.inl x) = 1
    · obtain ⟨x0, hx0⟩ := hA
      have hB : ∀ y, c (Sum.inr y) = 0 := fun y =>
        (h01 _).resolve_right fun h => hc _ _ hx0 h
      have hmem := (retractInl a.toFm b.toFm).push_mem _
        (clique_mem_P a (fun x => c (Sum.inl x)) (fun x => h01 _) (fun x y hx hy => hc _ _ hx hy))
      have : push (retractInl a.toFm b.toFm).j (fun x => c (Sum.inl x)) = c := by
        funext p; rw [push_inl_apply]; rcases p with x | x
        · rfl
        · exact (hB x).symm
      rw [this] at hmem; exact hmem
    · push_neg at hA
      have hA' : ∀ x, c (Sum.inl x) = 0 := fun x => (h01 _).resolve_right (hA x)
      have hmem := (retractInr a.toFm b.toFm).push_mem _
        (clique_mem_P b (fun x => c (Sum.inr x)) (fun x => h01 _) (fun x y hx hy => hc _ _ hx hy))
      have : push (retractInr a.toFm b.toFm).j (fun x => c (Sum.inr x)) = c := by
        funext p; rw [push_inr_apply]; rcases p with x | x
        · exact (hA' x).symm
        · rfl
      rw [this] at hmem; exact hmem

theorem push_sharp {E F : Type} [Fintype E] [DecidableEq F] {j : E → F} (hj : Function.Injective j)
    {s : E → ℝ≥0∞} (hs : ∀ d, s d = 0 ∨ s d = 1) : ∀ p, push j s p = 0 ∨ push j s p = 1 := by
  intro p
  by_cases h : ∃ d, j d = p
  · obtain ⟨d, rfl⟩ := h; rw [push_apply_j hj]; exact hs d
  · left; simp only [push]; exact Finset.sum_eq_zero fun d _ => if_neg fun e => h ⟨d, e⟩

/-- An element orthogonal to the calculus of `A` restricts to one orthogonal to the calculus of a
retract. -/
theorem orth_recipe_of_retract {D A : Fm} (R : Retract D A) {u : web A → ℝ≥0∞}
    (hu : u ∈ orth (recipe A)) : (fun d => u (R.j d)) ∈ orth (recipe D) := by
  rw [recipe, orth_Mix]
  intro s hs
  rw [← pairing_push]
  exact hu _ (mem_Mix_self ⟨R.push_mem s hs.1, push_sharp R.inj hs.2⟩)

/-- **No gap at `A ⊕ B`.** -/
theorem recipe_plus {A B : Fm} (hA : recipe A = P A) (hB : recipe B = P B) :
    recipe (Fm.plus A B) = P (Fm.plus A B) := by
  apply le_antisymm (recipe_subset_P _)
  show P (Fm.plus A B) ⊆ recipe (Fm.plus A B)
  rw [← recipe_orth_orth (Fm.plus A B)]
  show orth (P (Fm.wth (Fm.neg A) (Fm.neg B))) ⊆ _
  refine orth_antitone fun u hu => ⟨?_, ?_⟩
  · have := orth_recipe_of_retract (retractInl A B) hu
    rw [hA] at this; exact this
  · have := orth_recipe_of_retract (retractInr A B) hu
    rw [hB] at this; exact this

theorem recipe_one : recipe (Fm.base 1) = P (Fm.base 1) := by
  apply le_antisymm (recipe_subset_P _)
  intro z hz
  have h1 : z (0 : Fin 1) ≤ 1 := by
    have : ∑ x : Fin 1, z x ≤ 1 := hz
    rwa [Fin.sum_univ_one] at this
  have hz' : z = ∑ i : Fin 2, (![z (0 : Fin 1), 1 - z (0 : Fin 1)] i) •
      (![(fun _ => 1 : web (Fm.base 1) → ℝ≥0∞), (0 : web (Fm.base 1) → ℝ≥0∞)] i) := by
    funext x
    rw [Subsingleton.elim (α := Fin 1) x 0]
    simp [Fin.sum_univ_two]
  rw [hz']
  refine ConstructiveProb.mem_Mix_of_fintype _ _ (fun i => ?_) ?_
  · fin_cases i
    · refine ⟨?_, fun _ => Or.inr rfl⟩
      show ∑ x : Fin 1, (1 : ℝ≥0∞) ≤ 1
      simp
    · exact ⟨zero_mem_P _, fun _ => Or.inl rfl⟩
  · simp [Fin.sum_univ_two, add_tsub_cancel_of_le h1]

/-- **No gap at additive codes.** -/
theorem recipe_code : ∀ a : ACode, recipe a.toFm = P a.toFm
  | ACode.one => recipe_one
  | ACode.wth a b => recipe_wth (recipe_code a) (recipe_code b)
  | ACode.plus a b => recipe_plus (recipe_code a) (recipe_code b)

/-! ### Real and extended coordinates -/

theorem ofReal_01 {r : ℝ} (h : r = 0 ∨ r = 1) : ENNReal.ofReal r = 0 ∨ ENNReal.ofReal r = 1 := by
  rcases h with rfl | rfl <;> simp

theorem eq_one_of_ofReal {r : ℝ} (h : r = 0 ∨ r = 1) (h1 : ENNReal.ofReal r = 1) : r = 1 := by
  rcases h with rfl | rfl <;> simp_all

theorem sharp_of_clique (a : ACode) {c : W a → ℝ} (hc : IsClique a c) :
    (fun x => ENNReal.ofReal (c x)) ∈ sharpP a.toFm :=
  ⟨clique_mem_P a _ (fun x => ofReal_01 (hc.1 x)) (fun x y hx hy =>
    hc.2 x y (eq_one_of_ofReal (hc.1 x) hx) (eq_one_of_ofReal (hc.1 y) hy)),
   fun x => ofReal_01 (hc.1 x)⟩

theorem clique_of_sharp (a : ACode) {s : W a → ℝ≥0∞} (hs : s ∈ sharpP a.toFm) :
    IsClique a (fun x => (s x).toReal) ∧ s = fun x => ENNReal.ofReal (s x).toReal := by
  have h1 : ∀ z, (s z).toReal = 1 → s z = 1 := fun z hz => by
    rcases hs.2 z with e | e <;> simp_all
  refine ⟨⟨fun x => by rcases hs.2 x with e | e <;> simp [e], fun x y hx hy => ?_⟩, ?_⟩
  · exact (coh_toFm a x y).1 (sharp_isClique a.toFm hs.1 hs.2 x y (h1 x hx) (h1 y hy))
  · funext x; rcases hs.2 x with e | e <;> simp [e]

theorem pairing_real {X Y : Type} [Fintype X] [Fintype Y] (a : X → ℝ) (c : Y → ℝ)
    (Z : X → Y → ℝ) (ha : ∀ x, 0 ≤ a x) (hc : ∀ k, 0 ≤ c k) (hZ : ∀ x k, 0 ≤ Z x k) :
    pairing (tvec (fun x => ENNReal.ofReal (a x)) (fun k => ENNReal.ofReal (c k)))
      (fun p : X × Y => ENNReal.ofReal (Z p.1 p.2)) =
      ENNReal.ofReal (∑ k, c k * ∑ x, a x * Z x k) := by
  have e : ∀ p : X × Y, ENNReal.ofReal (a p.1) * ENNReal.ofReal (c p.2) *
      ENNReal.ofReal (Z p.1 p.2) = ENNReal.ofReal (a p.1 * c p.2 * Z p.1 p.2) := fun p => by
    rw [ENNReal.ofReal_mul (mul_nonneg (ha _) (hc _)), ENNReal.ofReal_mul (ha _)]
  simp only [pairing, tvec, e]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (mul_nonneg (ha _) (hc _)) (hZ _ _))]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem pathInd_nonneg {t : TCode} {a : N t → ℝ} (ha : IsPathInd t a) (x : N t) : 0 ≤ a x := by
  rcases pathInd_01 t a ha x with e | e <;> simp [e]

/-- **The PCS of `(X ⊗ Y)^⊥` in real coordinates**: a nonnegative `Z` is an element iff every sum of
`Z` along a path has `ω` at most `1`. -/
theorem mem_P_iff (t : TCode) (K : ACode) (Z : N t → W K → ℝ) (hZ : ∀ x k, 0 ≤ Z x k) :
    (fun p : N t × W K => ENNReal.ofReal (Z p.1 p.2)) ∈
        P (Fm.neg (Fm.tens t.toA.toFm K.toFm)) ↔
      ∀ S ∈ PathSums t Z, ω K S ≤ 1 := by
  rw [P_neg_tens_eq (recipe_code t.toA) (recipe_code K)]
  constructor
  · intro h S hS
    obtain ⟨a, ha, rfl⟩ := pathInd_of_PathSums t Z S hS
    obtain ⟨c, hc, hω⟩ := ω_attain K (∑ x, a x • Z x)
    have hc0 : ∀ k, 0 ≤ c k := fun k => by rcases hc.1 k with e | e <;> simp [e]
    have h1 := h _ ⟨_, sharp_of_clique t.toA ⟨pathInd_01 t a ha, pathInd_clique t a ha⟩, _,
      sharp_of_clique K hc, rfl⟩
    have h2 := (pairing_real a c Z (pathInd_nonneg ha) hc0 hZ).symm.trans_le h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hω
    rw [hω]
    exact ENNReal.ofReal_le_one.1 h2
  · intro h
    rintro _ ⟨s, hs, c, hc, rfl⟩
    obtain ⟨hsc, hseq⟩ := clique_of_sharp t.toA hs
    obtain ⟨hcc, hceq⟩ := clique_of_sharp K hc
    obtain ⟨a, ha, hle⟩ := clique_le_path t _ hsc.1 hsc.2
    have hs0 : ∀ x, 0 ≤ (s x).toReal := fun _ => ENNReal.toReal_nonneg
    have hc0 : ∀ k, 0 ≤ (c k).toReal := fun _ => ENNReal.toReal_nonneg
    have hS0 : 0 ≤ ∑ x, a x • Z x := fun k => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (pathInd_nonneg ha x) (hZ x k)
    rw [hseq, hceq]
    refine (pairing_real _ _ Z hs0 hc0 hZ).trans_le ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    calc ∑ k, (c k).toReal * ∑ x, (s x).toReal * Z x k
        ≤ ∑ k, (c k).toReal * ∑ x, a x * Z x k :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hle x) (hZ x k)) (hc0 k)
      _ = ∑ k, (c k).toReal * (∑ x, a x • Z x) k := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ ≤ ω K (∑ x, a x • Z x) := clique_le_ω K hS0 _ hcc
      _ ≤ 1 := h _ (PathSums_of_pathInd t Z a ha)

/-! ### The theorem -/

/-- **No gap at second order for forest and cograph codes.** For `X` built from `1` with `⊕` and
`- & 1` and `Y` built from `1` with `&` and `⊕`, the calculus of `(X ⊗ Y)^⊥` equals its PCS. -/
theorem second_order_noGap (t : TCode) (K : ACode) :
    recipe (Fm.neg (Fm.tens t.toA.toFm K.toFm)) = P (Fm.neg (Fm.tens t.toA.toFm K.toFm)) := by
  apply le_antisymm (recipe_subset_P _)
  intro z hz
  have hz' : z ∈ orth (P (Fm.tens t.toA.toFm K.toFm)) := hz
  have hfin : ∀ p, z p ≠ ⊤ := fun p => ne_top_of_le_ne_top ENNReal.one_ne_top (by
    have := hz' _ (single_mem_P (Fm.tens t.toA.toFm K.toFm) p)
    rwa [pairing_single] at this)
  obtain ⟨Z, hZdef⟩ : ∃ Z : N t → W K → ℝ, Z = fun x k => (z ((x, k) : N t × W K)).toReal :=
    ⟨_, rfl⟩
  have hzZ : z = fun p : N t × W K => ENNReal.ofReal (Z p.1 p.2) := by
    funext p; rw [hZdef]; exact (ENNReal.ofReal_toReal (hfin p)).symm
  have hZ : ∀ x k, 0 ≤ Z x k := fun _ _ => by rw [hZdef]; exact ENNReal.toReal_nonneg
  rw [hzZ] at hz
  obtain ⟨ι, _, w, σ, hw, hw1, hσ, hZeq⟩ :=
    main t K Z (fun x k => hZ x k) ((mem_P_iff t K Z hZ).1 hz)
  have hσ0 : ∀ i x k, 0 ≤ σ i x k := fun i x k => Valid_nonneg (hσ i) x k
  have hmix : (fun p : N t × W K => ENNReal.ofReal (Z p.1 p.2)) =
      ∑ i, ENNReal.ofReal (w i) • (fun p : N t × W K => ENNReal.ofReal (σ i p.1 p.2)) := by
    funext p
    rw [hZeq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i).le (hσ0 i _ _))]
    exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_mul (hw i).le
  rw [hzZ, hmix]
  refine ConstructiveProb.mem_Mix_of_fintype _ _ (fun i => ⟨?_, ?_⟩) ?_
  · exact (mem_P_iff t K (σ i) (hσ0 i)).2 fun S hS => ((hσ i).2 S hS).2
  · intro p; exact ofReal_01 ((hσ i).1 p.1 p.2)
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hw i).le), hw1, ENNReal.ofReal_one]

end ConstructiveProb.Cograph
