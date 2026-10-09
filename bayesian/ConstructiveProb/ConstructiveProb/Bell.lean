/-
# Bell's theorem at the core

The core `(2 ⊸ 2) ⊗ (2 ⊸ 2)` is the bipartite scenario with two inputs and two outputs per
party: a point `((x, a), (y, b))` of its web is the event "on inputs `x, y` the outputs are
`a, b`". Its PCS is the calculus of certain states (`recipe_core`), the mixtures of
deterministic product strategies. Its local calculus is cut out by the `{0,1}`-valued elements
of the dual, which are sets of pairwise exclusive events (`sharp_dual_exclusive`).

* `prBox_not_mem_P`: the Popescu–Rohrlich box is not in the PCS of the core, by the CHSH bound
  `chsh_bilinear` on product strategies.
* `prBox_mem_loc`: the PR box is in the local calculus of the core, since no three winning
  events are pairwise exclusive (`no_three_exclusive`).

So the strict inclusion of the PCS in the local calculus at the core is Bell's theorem.
-/
import ConstructiveProb.Categorical

open scoped ENNReal
open Finset

namespace ConstructiveProb.Linear

open ConstructiveProb.PCS (orth pairing det det_row_le_one mem_lin_iff)
open Fm

/-- Events `((x, a), (y, b))` of the CHSH scenario. -/
abbrev BEv := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

/-- Winning events of the CHSH game: `a + b = x y` modulo `2`. -/
def win (e : BEv) : Prop := (e.1.2.val + e.2.2.val) % 2 = e.1.1.val * e.2.1.val

instance : DecidablePred win := fun e => by unfold win; infer_instance

/-- Coherence in the core: two events are coherent iff neither party has equal inputs and
different outputs. -/
def cohE (s t : BEv) : Prop := (s.1 = t.1 ∨ s.1.1 ≠ t.1.1) ∧ (s.2 = t.2 ∨ s.2.1 ≠ t.2.1)

instance : DecidableRel cohE := fun s t => by unfold cohE; infer_instance

theorem coh_core_iff (s t : web (core 2 2 2 2)) : coh (core 2 2 2 2) s t ↔ cohE s t := by
  show coh (lolli (base 2) (base 2)) s.1 t.1 ∧ coh (lolli (base 2) (base 2)) s.2 t.2 ↔ _
  rw [coh_lolli_base, coh_lolli_base]; rfl

/-- Three distinct winning events that are pairwise exclusive. -/
def excl3 (a b c : BEv) : Prop :=
  win a ∧ win b ∧ win c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ cohE a b ∧ ¬ cohE a c ∧ ¬ cohE b c

instance (a b c : BEv) : Decidable (excl3 a b c) := by unfold excl3; infer_instance

/-- No three winning events are pairwise exclusive. -/
theorem no_three_exclusive : ∀ a b c : BEv, ¬ excl3 a b c := by
  decide

/-- The Popescu–Rohrlich box. -/
noncomputable def prBox : web (core 2 2 2 2) → ℝ≥0∞ := fun e => if win e then 2⁻¹ else 0

theorem det_mem_P (f : Fin 2 → Option (Fin 2)) : det f ∈ P (lolli (base 2) (base 2)) := by
  rw [P_lolli_base]; exact (mem_lin_iff _).2 (det_row_le_one f)

/-- A deterministic product strategy hits any two coherent events. -/
theorem exists_det_hit (e e' : BEv) (h : cohE e e') :
    ∃ z ∈ P (core 2 2 2 2), z e = 1 ∧ z e' = 1 := by
  classical
  let f : Fin 2 → Option (Fin 2) := fun u => if u = e.1.1 then some e.1.2 else some e'.1.2
  let g : Fin 2 → Option (Fin 2) := fun u => if u = e.2.1 then some e.2.2 else some e'.2.2
  have hf : det f e.1 = 1 ∧ det f e'.1 = 1 := by
    refine ⟨by simp [det, f], ?_⟩
    by_cases hx : e'.1.1 = e.1.1
    · have : e.1 = e'.1 := h.1.resolve_right (fun hne => hne hx.symm)
      simp [det, f, hx, this]
    · simp [det, f, hx]
  have hg : det g e.2 = 1 ∧ det g e'.2 = 1 := by
    refine ⟨by simp [det, g], ?_⟩
    by_cases hy : e'.2.1 = e.2.1
    · have : e.2 = e'.2 := h.2.resolve_right (fun hne => hne hy.symm)
      simp [det, g, hy, this]
    · simp [det, g, hy]
  refine ⟨tvec (det f) (det g), tvec_mem_P (det_mem_P f) (det_mem_P g), ?_, ?_⟩
  · show det f e.1 * det g e.2 = 1
    rw [hf.1, hg.1, one_mul]
  · show det f e'.1 * det g e'.2 = 1
    rw [hf.2, hg.2, one_mul]

/-- **The certain states of the dual are sets of pairwise exclusive events.** -/
theorem sharp_dual_exclusive {s : web (core 2 2 2 2) → ℝ≥0∞}
    (hs : s ∈ sharpP (Fm.neg (core 2 2 2 2))) {e e' : BEv} (hne : e ≠ e') (he : s e = 1)
    (he' : s e' = 1) : ¬ cohE e e' := by
  classical
  intro hc
  obtain ⟨z, hz, hze, hze'⟩ := exists_det_hit e e' hc
  have h1 : pairing z s ≤ 1 := hs.1 z hz
  have hpair : ∑ x ∈ ({e, e'} : Finset (web (core 2 2 2 2))), z x * s x
      = z e * s e + z e' * s e' := Finset.sum_pair hne
  have h2 : z e * s e + z e' * s e' ≤ pairing z s := by
    rw [← hpair, pairing]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [hze, hze', he, he', one_mul] at h2
  have h3 := h2.trans h1
  norm_num at h3

/-- **The PR box is in the local calculus of the core.** -/
theorem prBox_mem_loc : prBox ∈ loc (core 2 2 2 2) := by
  classical
  intro s hs
  have hS : (univ.filter fun e : BEv => win e ∧ s e = 1).card ≤ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
    exact no_three_exclusive a b c ⟨ha.1, hb.1, hc.1, hab, hac, hbc,
      sharp_dual_exclusive hs hab ha.2 hb.2, sharp_dual_exclusive hs hac ha.2 hc.2,
      sharp_dual_exclusive hs hbc hb.2 hc.2⟩
  have hterm : ∀ e : BEv, s e * prBox e = if win e ∧ s e = 1 then 2⁻¹ else 0 := by
    intro e
    rcases hs.2 e with h | h <;> by_cases hw : win e <;> simp [prBox, h, hw]
  calc pairing s prBox = ∑ e : BEv, (if win e ∧ s e = 1 then (2⁻¹ : ℝ≥0∞) else 0) :=
        Finset.sum_congr rfl fun e _ => hterm e
    _ = (univ.filter fun e : BEv => win e ∧ s e = 1).card * 2⁻¹ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * 2⁻¹ := by gcongr; exact_mod_cast hS
    _ = 1 := ENNReal.mul_inv_cancel two_ne_zero (by norm_num)

/-- The CHSH bound in eight variables. -/
theorem chsh_key (p0 q0 p1 q1 r0 s0 r1 s1 : ℝ≥0∞) (hp0 : p0 + q0 ≤ 1) (hp1 : p1 + q1 ≤ 1)
    (hr0 : r0 + s0 ≤ 1) (hr1 : r1 + s1 ≤ 1) :
    r0 * (p0 + p1) + s0 * (q0 + q1) + (r1 * (p0 + q1) + s1 * (q0 + p1)) ≤ 3 := by
  have hmax : ∀ r s A B : ℝ≥0∞, r + s ≤ 1 → r * A + s * B ≤ max A B := fun r s A B h =>
    calc r * A + s * B ≤ r * max A B + s * max A B :=
          add_le_add (mul_le_mul_right (le_max_left _ _) _) (mul_le_mul_right (le_max_right _ _) _)
      _ = (r + s) * max A B := (add_mul _ _ _).symm
      _ ≤ 1 * max A B := mul_le_mul_left h _
      _ = max A B := one_mul _
  have hp0' : p0 ≤ 1 := le_self_add.trans hp0
  have hq0' : q0 ≤ 1 := le_add_self.trans hp0
  have hp1' : p1 ≤ 1 := le_self_add.trans hp1
  have hq1' : q1 ≤ 1 := le_add_self.trans hp1
  have h3 : (3 : ℝ≥0∞) = 1 + 1 + 1 := by norm_num
  refine (add_le_add (hmax r0 s0 _ _ hr0) (hmax r1 s1 _ _ hr1)).trans ?_
  rcases le_total (p0 + p1) (q0 + q1) with hA | hA <;>
    rcases le_total (p0 + q1) (q0 + p1) with hC | hC <;>
    simp only [max_eq_left, max_eq_right, hA, hC] <;> rw [h3]
  · calc q0 + q1 + (q0 + p1) = q0 + q0 + (p1 + q1) := by ring
      _ ≤ 1 + 1 + 1 := add_le_add (add_le_add hq0' hq0') hp1
  · calc q0 + q1 + (p0 + q1) = (p0 + q0) + q1 + q1 := by ring
      _ ≤ 1 + 1 + 1 := add_le_add (add_le_add hp0 hq1') hq1'
  · calc p0 + p1 + (q0 + p1) = (p0 + q0) + p1 + p1 := by ring
      _ ≤ 1 + 1 + 1 := add_le_add (add_le_add hp0 hp1') hp1'
  · calc p0 + p1 + (p0 + q1) = p0 + p0 + (p1 + q1) := by ring
      _ ≤ 1 + 1 + 1 := add_le_add (add_le_add hp0' hp0') hp1

/-- **The CHSH bound for product strategies.** -/
theorem chsh_bilinear {X Y : Fin 2 × Fin 2 → ℝ≥0∞} (hX : ∀ a, ∑ b, X (a, b) ≤ 1)
    (hY : ∀ a, ∑ b, Y (a, b) ≤ 1) :
    ∑ e : BEv, (if win e then X e.1 * Y e.2 else 0) ≤ 3 := by
  have h0 := hX 0
  have h1 := hX 1
  have k0 := hY 0
  have k1 := hY 1
  simp only [Fin.sum_univ_two] at h0 h1 k0 k1
  refine le_trans (le_of_eq ?_) (chsh_key (X (0, 0)) (X (0, 1)) (X (1, 0)) (X (1, 1))
    (Y (0, 0)) (Y (0, 1)) (Y (1, 0)) (Y (1, 1)) h0 h1 k0 k1)
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, win]
  simp
  ring

/-- The CHSH test, scaled to the dual. -/
noncomputable def chshTest : web (core 2 2 2 2) → ℝ≥0∞ := fun e => if win e then 3⁻¹ else 0

/-- **The PR box is not in the PCS of the core.** -/
theorem prBox_not_mem_P : prBox ∉ P (core 2 2 2 2) := by
  classical
  intro h
  have ht : chshTest ∈ orth {z | ∃ x ∈ P (lolli (base 2) (base 2)),
      ∃ y ∈ P (lolli (base 2) (base 2)), z = tvec x y} := by
    rintro _ ⟨X, hX, Y, hY, rfl⟩
    rw [P_lolli_base] at hX hY
    replace hX := (mem_lin_iff (X := Fin 2) (Y := Fin 2) X).1 hX
    replace hY := (mem_lin_iff (X := Fin 2) (Y := Fin 2) Y).1 hY
    have hterm : ∀ e : BEv, tvec X Y e * chshTest e = 3⁻¹ * (if win e then X e.1 * Y e.2 else 0) := by
      intro e; by_cases hw : win e <;> simp [tvec, chshTest, hw, mul_comm]
    calc pairing (tvec X Y) chshTest
        = ∑ e : BEv, 3⁻¹ * (if win e then X e.1 * Y e.2 else 0) :=
          Finset.sum_congr rfl fun e _ => hterm e
      _ = 3⁻¹ * ∑ e : BEv, (if win e then X e.1 * Y e.2 else 0) := (Finset.mul_sum _ _ _).symm
      _ ≤ 3⁻¹ * 3 := mul_le_mul_right (chsh_bilinear hX hY) _
      _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have h1 : pairing chshTest prBox ≤ 1 := h chshTest ht
  have hcard : (univ.filter win : Finset BEv).card = 8 := by decide
  have hval : pairing chshTest prBox = 8 * (3⁻¹ * 2⁻¹) := by
    have hterm : ∀ e : BEv, chshTest e * prBox e = if win e then 3⁻¹ * 2⁻¹ else 0 := by
      intro e; by_cases hw : win e <;> simp [chshTest, prBox, hw]
    calc pairing chshTest prBox = ∑ e : BEv, (if win e then (3⁻¹ * 2⁻¹ : ℝ≥0∞) else 0) :=
          Finset.sum_congr rfl fun e _ => hterm e
      _ = 8 * (3⁻¹ * 2⁻¹) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            hcard]; norm_num
  rw [hval] at h1
  have h8 : (8 : ℝ≥0∞) * (3⁻¹ * 2⁻¹) = 4 * 3⁻¹ := by
    rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num, mul_assoc, mul_comm (3⁻¹ : ℝ≥0∞) 2⁻¹,
      ← mul_assoc 2, ENNReal.mul_inv_cancel two_ne_zero (by norm_num), one_mul]
  rw [h8] at h1
  have : (1 : ℝ≥0∞) < 4 * 3⁻¹ := by
    rw [← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (by norm_num) (by norm_num)]
    norm_num
  exact absurd h1 (not_le.2 this)

/-- **Bell's theorem at the core.** The PCS of `(2 ⊸ 2) ⊗ (2 ⊸ 2)` is strictly smaller than its
local calculus, with the PR box as witness. -/
theorem P_core_ssubset_loc : P (core 2 2 2 2) ⊂ loc (core 2 2 2 2) :=
  Set.ssubset_iff_subset_ne.2 ⟨(recipe_sub_P_sub_loc _).2,
    fun h => prBox_not_mem_P (h ▸ prBox_mem_loc)⟩

end ConstructiveProb.Linear
