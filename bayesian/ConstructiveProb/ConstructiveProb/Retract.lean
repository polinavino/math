/-
# The gap at every formula containing the second-order core

A *coordinate retract* of a formula `D` into a formula `A` is an injective map of webs
`j : |D| → |A|` such that pushing forward along `j` maps `P D` into `P A` and pulling back along `j`
maps `P A` into `P D`. Then:

* `Retract.recipe_ne`: if the recipe's calculus differs from the PCS at `D`, it differs at `A`;
* coordinate retracts compose, pass through negation (`Retract.neg`), and embed `D` into `D ⊗ B`,
  `B ⊗ D`, `D & B`, `B & D` whenever the webs involved are nonempty;
* `occ_retract`: every positive occurrence of `D` in `A` gives a coordinate retract of `D` into
  `A`, and every negative occurrence one of `D^⊥` into `A`;
* `gap_of_occ`: every formula over nonempty data types in which
  `(n ⊸ m) ⊗ (n' ⊸ m')` (all four at least `2`) occurs negatively has calculus strictly smaller
  than its PCS. Examples: `((n ⊸ m) ⊗ (n' ⊸ m'))^⊥` itself, `((n ⊸ m) ⊗ (n' ⊸ m')) ⊸ B` for any
  `B`, and every formula containing one of these positively.
-/
import ConstructiveProb.LinearInstances

open scoped ENNReal
open Finset

namespace ConstructiveProb.Linear

open ConstructiveProb.PCS (orth pairing subset_orth_orth mem_lin_iff)
open Fm

/-! ### Pushforward along a map of webs -/

section Push

variable {E F G : Type} [Fintype E] [Fintype F] [DecidableEq F] [DecidableEq G]

/-- Pushforward of a vector along `j`. -/
noncomputable def push (j : E → F) (x : E → ℝ≥0∞) : F → ℝ≥0∞ :=
  fun a => ∑ d, if j d = a then x d else 0

omit [Fintype F] in
theorem push_apply_j {j : E → F} (hj : Function.Injective j) (x : E → ℝ≥0∞) (d : E) :
    push j x (j d) = x d := by
  simp only [push]
  rw [Finset.sum_eq_single d (fun d' _ h => if_neg fun e => h (hj e)) (by simp)]
  simp

omit [Fintype F] in
theorem pull_push {j : E → F} (hj : Function.Injective j) (x : E → ℝ≥0∞) :
    (fun d => push j x (j d)) = x :=
  funext (push_apply_j hj x)

theorem pairing_comm' {X : Type} [Fintype X] (x y : X → ℝ≥0∞) : pairing x y = pairing y x :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem pairing_push (j : E → F) (u : E → ℝ≥0∞) (z : F → ℝ≥0∞) :
    pairing (push j u) z = pairing u (fun d => z (j d)) := by
  simp only [pairing, push, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single (j d) (fun a _ h => by rw [if_neg (Ne.symm h), zero_mul]) (by simp)]
  simp

omit [Fintype F] in
theorem push_id [DecidableEq E] (x : E → ℝ≥0∞) : push (fun d : E => d) x = x := by
  funext a; simp [push]

omit [Fintype F] in
theorem push_comp [Fintype F] (j1 : E → F) (j2 : F → G) (x : E → ℝ≥0∞) :
    push (fun d => j2 (j1 d)) x = push j2 (push j1 x) := by
  funext c
  simp only [push]
  have h : ∀ a, (if j2 a = c then ∑ d, (if j1 d = a then x d else 0) else 0)
      = ∑ d, if j1 d = a ∧ j2 a = c then x d else 0 := by
    intro a
    by_cases ha : j2 a = c
    · rw [if_pos ha]
      exact Finset.sum_congr rfl fun d _ => by by_cases h' : j1 d = a <;> simp [h', ha]
    · rw [if_neg ha]
      exact (Finset.sum_eq_zero fun d _ => by simp [ha]).symm
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single (j1 d) (fun a _ hne => if_neg fun h' => hne h'.1.symm) (by simp)]
  simp

end Push

/-! ### Coordinate retracts -/

/-- A coordinate retract of `D` into `A`. -/
structure Retract (D A : Fm) where
  j : web D → web A
  inj : Function.Injective j
  push_mem : ∀ x ∈ P D, push j x ∈ P A
  pull_mem : ∀ z ∈ P A, (fun d => z (j d)) ∈ P D

/-- The recipe's calculus at a formula. -/
def recipe (A : Fm) : Set (web A → ℝ≥0∞) :=
  ConstructiveProb.Mix {z | z ∈ P A ∧ ∀ s, z s = 0 ∨ z s = 1}

/-- **Gap transfer.** -/
theorem Retract.recipe_ne {D A : Fm} (R : Retract D A) (h : recipe D ≠ P D) :
    recipe A ≠ P A := by
  intro hA
  apply h
  apply le_antisymm (recipe_subset_P D)
  intro x hx
  have hpx : push R.j x ∈ recipe A := hA ▸ R.push_mem x hx
  obtain ⟨n, w, s, hs, hw, heq⟩ := hpx
  refine ⟨n, w, fun i d => s i (R.j d), fun i => ⟨R.pull_mem _ (hs i).1, fun d => (hs i).2 _⟩, hw,
    ?_⟩
  rw [← pull_push R.inj x, heq]
  funext d
  simp [Finset.sum_apply]

def Retract.refl (D : Fm) : Retract D D where
  j d := d
  inj _ _ h := h
  push_mem x hx := by rw [push_id]; exact hx
  pull_mem z hz := hz

def Retract.trans {D A C : Fm} (R : Retract D A) (S : Retract A C) : Retract D C where
  j d := S.j (R.j d)
  inj _ _ h := R.inj (S.inj h)
  push_mem x hx := by rw [push_comp]; exact S.push_mem _ (R.push_mem x hx)
  pull_mem z hz := R.pull_mem _ (S.pull_mem z hz)

/-- **Retracts pass through negation.** -/
def Retract.neg {D A : Fm} (R : Retract D A) : Retract (Fm.neg D) (Fm.neg A) where
  j := R.j
  inj := R.inj
  push_mem u hu := by
    show push R.j u ∈ orth (P A)
    intro z hz
    rw [pairing_comm', pairing_push, pairing_comm']
    exact hu _ (R.pull_mem z hz)
  pull_mem w hw := by
    show (fun d => w (R.j d)) ∈ orth (P D)
    intro x hx
    rw [← pairing_push]
    exact hw _ (R.push_mem x hx)

/-- `D` is a retract of `D^⊥⊥`. -/
def Retract.negneg (D : Fm) : Retract D (Fm.neg (Fm.neg D)) where
  j d := d
  inj _ _ h := h
  push_mem x hx := by
    rw [push_id]; exact subset_orth_orth _ hx
  pull_mem z hz := by
    have h : z ∈ orth (orth (P D)) := hz
    rw [(isPCS_P D).closed] at h
    exact h

theorem push_tensL {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y] (b : Y)
    (x : X → ℝ≥0∞) : push (fun d => (d, b)) x = tvec x (Pi.single b 1) := by
  funext ⟨d', b'⟩
  simp only [push, tvec, Prod.mk.injEq]
  by_cases hb : b = b'
  · subst hb; simp
  · simp [hb, Pi.single_apply, Ne.symm hb]

theorem push_tensR {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y] (b : Y)
    (x : X → ℝ≥0∞) : push (fun d => (b, d)) x = tvec (Pi.single b 1) x := by
  funext ⟨b', d'⟩
  simp only [push, tvec, Prod.mk.injEq]
  by_cases hb : b = b'
  · subst hb; simp
  · simp [hb, Pi.single_apply, Ne.symm hb]

/-- `D` is a retract of `D ⊗ B` through any point of `B`. -/
def Retract.tensL (D B : Fm) (b : web B) : Retract D (Fm.tens D B) where
  j d := (d, b)
  inj _ _ h := (Prod.mk.injEq _ _ _ _ ▸ h).1
  push_mem x hx := by
    rw [push_tensL]
    exact subset_orth_orth _ ⟨x, hx, _, single_mem_P B b, rfl⟩
  pull_mem z hz := by
    have hz' : z ∈ orth (orth {z | ∃ x ∈ P D, ∃ y ∈ P B, z = tvec x y}) := hz
    rw [← (isPCS_P D).closed]
    intro u hu
    have hmem : tvec u (Pi.single b 1) ∈ orth {z | ∃ x ∈ P D, ∃ y ∈ P B, z = tvec x y} := by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      rw [pairing_tvec, pairing_single']
      exact mul_le_one' (hu x hx) (((invariants B).1 b).2 y hy)
    have := hz' _ hmem
    rw [← push_tensL, pairing_push] at this
    exact this

/-- `D` is a retract of `B ⊗ D` through any point of `B`. -/
def Retract.tensR (D B : Fm) (b : web B) : Retract D (Fm.tens B D) where
  j d := (b, d)
  inj _ _ h := (Prod.mk.injEq _ _ _ _ ▸ h).2
  push_mem x hx := by
    rw [push_tensR]
    exact subset_orth_orth _ ⟨_, single_mem_P B b, x, hx, rfl⟩
  pull_mem z hz := by
    have hz' : z ∈ orth (orth {z | ∃ x ∈ P B, ∃ y ∈ P D, z = tvec x y}) := hz
    rw [← (isPCS_P D).closed]
    intro u hu
    have hmem : tvec (Pi.single b 1) u ∈ orth {z | ∃ x ∈ P B, ∃ y ∈ P D, z = tvec x y} := by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      rw [pairing_tvec, pairing_single']
      exact mul_le_one' (((invariants B).1 b).2 x hx) (hu y hy)
    have := hz' _ hmem
    rw [← push_tensR, pairing_push] at this
    exact this

/-- `D` is a retract of `D & B`. -/
def Retract.wthL (D B : Fm) : Retract D (Fm.wth D B) where
  j := Sum.inl
  inj := Sum.inl_injective
  push_mem x hx := by
    refine ⟨?_, ?_⟩
    · show (fun a => push Sum.inl x (Sum.inl a)) ∈ P D
      rw [pull_push Sum.inl_injective]; exact hx
    · show (fun b => push Sum.inl x (Sum.inr b)) ∈ P B
      have : (fun b => push (Sum.inl : web D → web D ⊕ web B) x (Sum.inr b)) = 0 := by
        funext b; simp [push]
      rw [this]; exact zero_mem_P B
  pull_mem z hz := hz.1

/-- `D` is a retract of `B & D`. -/
def Retract.wthR (D B : Fm) : Retract D (Fm.wth B D) where
  j := Sum.inr
  inj := Sum.inr_injective
  push_mem x hx := by
    refine ⟨?_, ?_⟩
    · show (fun a => push Sum.inr x (Sum.inl a)) ∈ P B
      have : (fun a => push (Sum.inr : web D → web B ⊕ web D) x (Sum.inl a)) = 0 := by
        funext a; simp [push]
      rw [this]; exact zero_mem_P B
    · show (fun b => push Sum.inr x (Sum.inr b)) ∈ P D
      rw [pull_push Sum.inr_injective]; exact hx
  pull_mem z hz := hz.2

/-! ### Functoriality in `⊗` -/

theorem push_tvec {X Y X' Y' : Type} [Fintype X] [Fintype Y] [DecidableEq X'] [DecidableEq Y']
    (j : X → X') (k : Y → Y') (x : X → ℝ≥0∞) (y : Y → ℝ≥0∞) :
    push (fun d : X × Y => (j d.1, k d.2)) (tvec x y) = tvec (push j x) (push k y) := by
  funext ⟨a, b⟩
  simp only [push, tvec, Fintype.sum_prod_type, Prod.mk.injEq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  by_cases h1 : j d = a <;> by_cases h2 : k e = b <;> simp [h1, h2]

/-- **Retracts pass through `⊗`.** -/
def Retract.tens {D A D' A' : Fm} (R : Retract D A) (R' : Retract D' A') :
    Retract (Fm.tens D D') (Fm.tens A A') where
  j d := (R.j d.1, R'.j d.2)
  inj a b h := Prod.ext (R.inj (Prod.mk.inj h).1) (R'.inj (Prod.mk.inj h).2)
  push_mem x hx := by
    have hx' : x ∈ orth (orth {z | ∃ u ∈ P D, ∃ v ∈ P D', z = tvec u v}) := hx
    show _ ∈ orth (orth {z | ∃ u ∈ P A, ∃ v ∈ P A', z = tvec u v})
    intro f hf
    rw [pairing_comm', pairing_push, pairing_comm']
    refine hx' _ ?_
    rintro _ ⟨u, hu, v, hv, rfl⟩
    rw [← pairing_push, push_tvec]
    exact hf _ ⟨_, R.push_mem u hu, _, R'.push_mem v hv, rfl⟩
  pull_mem z hz := by
    have hz' : z ∈ orth (orth {z | ∃ u ∈ P A, ∃ v ∈ P A', z = tvec u v}) := hz
    show _ ∈ orth (orth {z | ∃ u ∈ P D, ∃ v ∈ P D', z = tvec u v})
    intro g hg
    rw [← pairing_push]
    refine hz' _ ?_
    rintro _ ⟨a, ha, a', ha', rfl⟩
    rw [pairing_comm', pairing_push, pairing_comm']
    exact hg _ ⟨_, R.pull_mem a ha, _, R'.pull_mem a' ha', rfl⟩

/-- **The second-order gap, through retracts.** If `n ⊸ m` is a coordinate retract of `X` and
`n' ⊸ m'` one of `Y`, all four at least `2`, the calculus of `(X ⊗ Y)^⊥` is strictly smaller
than its PCS. -/
theorem gap_of_retracts {n m n' m' : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hn' : 2 ≤ n') (hm' : 2 ≤ m')
    {X Y : Fm} (RX : Retract (lolli (base n) (base m)) X)
    (RY : Retract (lolli (base n') (base m')) Y) :
    recipe (Fm.neg (tens X Y)) ⊂ P (Fm.neg (tens X Y)) := by
  have h2 := recipe_second_order_ssubset hn hm hn' hm'
  exact Set.ssubset_iff_subset_ne.2 ⟨recipe_subset_P _, (RX.tens RY).neg.recipe_ne h2.ne⟩

/-! ### Four-cycles of coherence -/

theorem coh_symm : ∀ (A : Fm) {s t : web A}, coh A s t → coh A t s
  | base _, _, _, h => h.symm
  | Fm.neg A, _, _, h =>
    h.elim (fun e => Or.inl e.symm) (fun h' => Or.inr fun h'' => h' (coh_symm A h''))
  | tens A B, _, _, h => ⟨coh_symm A h.1, coh_symm B h.2⟩
  | wth A _, Sum.inl _, Sum.inl _, h => coh_symm A h
  | wth _ B, Sum.inr _, Sum.inr _, h => coh_symm B h
  | wth _ _, Sum.inl _, Sum.inr _, _ => trivial
  | wth _ _, Sum.inr _, Sum.inl _, _ => trivial

/-- An induced four-cycle of the coherence graph: `a ⁀ b ⁀ c ⁀ d ⁀ a`, with `a, c` and `b, d`
incoherent. -/
structure C4 (X : Fm) where
  (a b c d : web X)
  hab : coh X a b
  hbc : coh X b c
  hcd : coh X c d
  hda : coh X d a
  hac : ¬ coh X a c
  hbd : ¬ coh X b d

namespace C4

variable {X : Fm} (Q : C4 X)

theorem a_ne_c : Q.a ≠ Q.c := fun h => Q.hac (h ▸ coh_refl X Q.a)
theorem b_ne_d : Q.b ≠ Q.d := fun h => Q.hbd (h ▸ coh_refl X Q.b)
theorem a_ne_b : Q.a ≠ Q.b := fun h => Q.hbd (h ▸ coh_symm X Q.hda)
theorem a_ne_d : Q.a ≠ Q.d := fun h => Q.hac (coh_symm X (h ▸ Q.hcd))
theorem b_ne_c : Q.b ≠ Q.c := fun h => Q.hac (h ▸ Q.hab)
theorem c_ne_d : Q.c ≠ Q.d := fun h => Q.hbd (h ▸ Q.hbc)

/-- The four points as the web of `2 ⊸ 2`: input `0` goes to `a, c`, input `1` to `b, d`. -/
def j : Fin 2 × Fin 2 → web X := fun p => ![![Q.a, Q.c], ![Q.b, Q.d]] p.1 p.2

theorem j_inj : Function.Injective Q.j := by
  rintro ⟨p1, p2⟩ ⟨q1, q2⟩ h
  have := Q.a_ne_c; have := Q.b_ne_d; have := Q.a_ne_b; have := Q.a_ne_d
  have := Q.b_ne_c; have := Q.c_ne_d
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;> simp_all [j, eq_comm]

theorem edge {u : web X → ℝ≥0∞} (hu : u ∈ orth (P X)) {s t : web X} (hst : s ≠ t)
    (h : coh X s t) : u s + u t ≤ 1 := by
  have := hu _ (pair_mem_P X hst h)
  rwa [pr, pairing_add_left, pairing_single, pairing_single] at this

/-- **A four-cycle of coherence is a copy of `2 ⊸ 2`.** -/
def retract : Retract (lolli (base 2) (base 2)) X where
  j := Q.j
  inj := Q.j_inj
  push_mem x hx := by
    have hx' : ∀ r : Fin 2, ∑ q : Fin 2, x (r, q) ≤ 1 :=
      (mem_lin_iff (X := Fin 2) (Y := Fin 2) x).1 ((P_lolli_base 2 2) ▸ hx)
    rw [← (isPCS_P X).closed]
    intro u hu
    rw [pairing_comm', pairing_push]
    have e1 := edge hu Q.a_ne_b Q.hab
    have e2 := edge hu Q.a_ne_d (coh_symm X Q.hda)
    have e3 := edge hu Q.b_ne_c.symm (coh_symm X Q.hbc)
    have e4 := edge hu Q.c_ne_d Q.hcd
    have r0 := hx' 0
    have r1 := hx' 1
    simp only [Fin.sum_univ_two] at r0 r1
    change (∑ p : Fin 2 × Fin 2, x p * u (Q.j p)) ≤ 1
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, j]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    set M1 := max (u Q.a) (u Q.c)
    set M2 := max (u Q.b) (u Q.d)
    have hM : M1 + M2 ≤ 1 := by
      rcases le_total (u Q.a) (u Q.c) with h1 | h1 <;>
        rcases le_total (u Q.b) (u Q.d) with h2 | h2 <;>
        simp only [M1, M2, max_eq_left, max_eq_right, h1, h2] <;> assumption
    have k1 : x (0, 0) * u Q.a + x (0, 1) * u Q.c ≤ M1 :=
      calc _ ≤ x (0, 0) * M1 + x (0, 1) * M1 :=
            add_le_add (mul_le_mul_left' (le_max_left _ _) _)
              (mul_le_mul_left' (le_max_right _ _) _)
        _ = (x (0, 0) + x (0, 1)) * M1 := (add_mul _ _ _).symm
        _ ≤ 1 * M1 := mul_le_mul_right' r0 _
        _ = M1 := one_mul _
    have k2 : x (1, 0) * u Q.b + x (1, 1) * u Q.d ≤ M2 :=
      calc _ ≤ x (1, 0) * M2 + x (1, 1) * M2 :=
            add_le_add (mul_le_mul_left' (le_max_left _ _) _)
              (mul_le_mul_left' (le_max_right _ _) _)
        _ = (x (1, 0) + x (1, 1)) * M2 := (add_mul _ _ _).symm
        _ ≤ 1 * M2 := mul_le_mul_right' r1 _
        _ = M2 := one_mul _
    calc _ = (x (0, 0) * u Q.a + x (0, 1) * u Q.c) + (x (1, 0) * u Q.b + x (1, 1) * u Q.d) := by
          ring
      _ ≤ M1 + M2 := add_le_add k1 k2
      _ ≤ 1 := hM
  pull_mem z hz := by
    show _ ∈ P (lolli (base 2) (base 2))
    rw [P_lolli_base]
    refine (mem_lin_iff (X := Fin 2) (Y := Fin 2) (fun d => z (Q.j d))).2 fun r => ?_
    fin_cases r
    · simpa [Fin.sum_univ_two, j] using (invariants X).2.2 _ _ Q.a_ne_c Q.hac z hz
    · simpa [Fin.sum_univ_two, j] using (invariants X).2.2 _ _ Q.b_ne_d Q.hbd z hz

end C4

/-- **The gap from two four-cycles.** If the coherence graphs of `X` and `Y` both contain an
induced four-cycle, the calculus of `(X ⊗ Y)^⊥` is strictly smaller than its PCS. -/
theorem gap_of_C4 {X Y : Fm} (QX : C4 X) (QY : C4 Y) :
    recipe (Fm.neg (tens X Y)) ⊂ P (Fm.neg (tens X Y)) :=
  gap_of_retracts le_rfl le_rfl le_rfl le_rfl QX.retract QY.retract

/-! ### Occurrences -/

/-- Every data type in the formula is nonempty. -/
def NE : Fm → Prop
  | base n => 0 < n
  | Fm.neg A => NE A
  | tens A B => NE A ∧ NE B
  | wth A B => NE A ∧ NE B

theorem NE.point : ∀ A : Fm, NE A → Nonempty (web A)
  | base _, h => ⟨⟨0, h⟩⟩
  | Fm.neg A, h => NE.point A h
  | tens A B, h => by
    obtain ⟨a⟩ := NE.point A h.1
    obtain ⟨b⟩ := NE.point B h.2
    exact ⟨(a, b)⟩
  | wth A _, h => by
    obtain ⟨a⟩ := NE.point A h.1
    exact ⟨Sum.inl a⟩

/-- `Occ D p A`: `D` occurs in `A`, positively if `p` and negatively otherwise. -/
inductive Occ (D : Fm) : Bool → Fm → Prop
  | self : Occ D true D
  | neg {p : Bool} {A : Fm} : Occ D p A → Occ D (!p) (Fm.neg A)
  | tensL {p : Bool} {A : Fm} (B : Fm) : Occ D p A → Occ D p (tens A B)
  | tensR {p : Bool} {A : Fm} (B : Fm) : Occ D p A → Occ D p (tens B A)
  | wthL {p : Bool} {A : Fm} (B : Fm) : Occ D p A → Occ D p (wth A B)
  | wthR {p : Bool} {A : Fm} (B : Fm) : Occ D p A → Occ D p (wth B A)

/-- `D` or `D^⊥`, according to polarity. -/
def pol : Bool → Fm → Fm
  | true, D => D
  | false, D => Fm.neg D

/-- **Occurrences give retracts.** -/
theorem occ_retract {D : Fm} : ∀ {p : Bool} {A : Fm}, Occ D p A → NE A →
    Nonempty (Retract (pol p D) A)
  | _, _, Occ.self, _ => ⟨Retract.refl D⟩
  | _, _, Occ.neg (p := p) h, hA => by
    obtain ⟨R⟩ := occ_retract h hA
    cases p
    · exact ⟨(Retract.negneg D).trans R.neg⟩
    · exact ⟨R.neg⟩
  | _, _, Occ.tensL B h, hA => by
    obtain ⟨R⟩ := occ_retract h hA.1
    obtain ⟨b⟩ := NE.point B hA.2
    exact ⟨R.trans (Retract.tensL _ B b)⟩
  | _, _, Occ.tensR B h, hA => by
    obtain ⟨R⟩ := occ_retract h hA.2
    obtain ⟨b⟩ := NE.point B hA.1
    exact ⟨R.trans (Retract.tensR _ B b)⟩
  | _, _, Occ.wthL B h, hA => by
    obtain ⟨R⟩ := occ_retract h hA.1
    exact ⟨R.trans (Retract.wthL _ B)⟩
  | _, _, Occ.wthR B h, hA => by
    obtain ⟨R⟩ := occ_retract h hA.2
    exact ⟨R.trans (Retract.wthR _ B)⟩

/-- The second-order core `(n ⊸ m) ⊗ (n' ⊸ m')`. -/
abbrev core (n m n' m' : ℕ) : Fm := tens (lolli (base n) (base m)) (lolli (base n') (base m'))

/-- **The gap at every formula with a negative occurrence of the core.** -/
theorem gap_of_occ {n m n' m' : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hn' : 2 ≤ n') (hm' : 2 ≤ m')
    {A : Fm} (hocc : Occ (core n m n' m') false A) (hA : NE A) : recipe A ⊂ P A := by
  obtain ⟨R⟩ := occ_retract hocc hA
  have h2 := recipe_second_order_ssubset hn hm hn' hm'
  have hne : recipe (second n m n' m') ≠ P (second n m n' m') := h2.ne
  exact Set.ssubset_iff_subset_ne.2 ⟨recipe_subset_P A, R.recipe_ne hne⟩

/-- **The gap from two four-cycles, anywhere.** If `X ⊗ Y` occurs negatively in `A` and the
coherence graphs of `X` and `Y` both contain an induced four-cycle, the calculus of `A` is strictly
smaller than its PCS. -/
theorem gap_of_C4_occ {X Y A : Fm} (QX : C4 X) (QY : C4 Y) (hocc : Occ (tens X Y) false A)
    (hA : NE A) : recipe A ⊂ P A := by
  obtain ⟨R⟩ := occ_retract hocc hA
  have h2 := recipe_second_order_ssubset (le_refl 2) (le_refl 2) (le_refl 2) (le_refl 2)
  exact Set.ssubset_iff_subset_ne.2
    ⟨recipe_subset_P A, ((QX.retract.tens QY.retract).neg.trans R).recipe_ne h2.ne⟩

/-- The four-cycle of `2 ⊸ 2` itself. -/
def C4.lolli22 : C4 (lolli (base 2) (base 2)) where
  a := (0, 0)
  b := (1, 0)
  c := (0, 1)
  d := (1, 1)
  hab := by simp [coh, lolli]
  hbc := by simp [coh, lolli]
  hcd := by simp [coh, lolli]
  hda := by simp [coh, lolli]
  hac := by simp [coh, lolli]
  hbd := by simp [coh, lolli]

/-- The same four-cycle in `((2 ⊸ 2) ⊸ 2)^⊥`, the second argument type of the curried form. -/
def C4.curried : C4 (Fm.neg (lolli (lolli (base 2) (base 2)) (base 2))) where
  a := ((0, 0), 0)
  b := ((1, 0), 0)
  c := ((0, 1), 0)
  d := ((1, 1), 0)
  hab := by simp [coh, lolli]
  hbc := by simp [coh, lolli]
  hcd := by simp [coh, lolli]
  hda := by simp [coh, lolli]
  hac := by simp [coh, lolli]
  hbd := by simp [coh, lolli]

/-- **The curried form** `(2 ⊸ 2) ⊸ ((2 ⊸ 2) ⊸ 2)` has a gap too. -/
theorem gap_curried :
    recipe (lolli (lolli (base 2) (base 2)) (lolli (lolli (base 2) (base 2)) (base 2)))
      ⊂ P (lolli (lolli (base 2) (base 2)) (lolli (lolli (base 2) (base 2)) (base 2))) :=
  gap_of_C4 C4.lolli22 C4.curried

/-- Example: a program receiving two functions and returning a boolean. -/
example : recipe (lolli (core 2 2 2 2) (base 2)) ⊂ P (lolli (core 2 2 2 2) (base 2)) :=
  gap_of_occ le_rfl le_rfl le_rfl le_rfl (Occ.neg (Occ.tensL _ Occ.self))
    (by simp [NE, lolli])

end ConstructiveProb.Linear
