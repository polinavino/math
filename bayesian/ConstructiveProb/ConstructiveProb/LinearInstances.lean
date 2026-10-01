/-
# The concrete results as statements about formulas

The general semantics of `Linear.lean` computes the spaces studied concretely:
`P (base n ⊸ base m) = lin (Fin n) (Fin m)` (`P_lolli_base`) and
`P (((base n ⊸ base m) ⊗ (base n' ⊸ base m'))^⊥) = tD (Fin n) (Fin m) (Fin n') (Fin m')`
(`P_second`). So, as statements about formulas:

* `recipe_first_order`: at `base n ⊸ base m` the recipe equals the PCS;
* `recipe_second_order`: at the second-order formula the recipe is the set of randomized
  sequential programs;
* `recipe_second_order_ssubset`: and it is strictly smaller than the PCS when every data type
  has at least two elements.
-/
import ConstructiveProb.Linear
import ConstructiveProb.GeneralKuhn
import ConstructiveProb.TensorGap

open scoped ENNReal
open Finset

namespace ConstructiveProb.Linear

open ConstructiveProb.PCS (orth pairing flat lin app mem_lin_iff orth_orth_orth det)
open ConstructiveProb.PCS.General (tD sequentialG recipe_eq_sequentialG pentE pentE_mem
  pentE_not_mix)
open Fm

/-- The second-order formula `((base n ⊸ base m) ⊗ (base n' ⊸ base m'))^⊥`. -/
def second (n m n' m' : ℕ) : Fm := neg (tens (lolli (base n) (base m)) (lolli (base n') (base m')))

theorem one_mem_orth_flat (m : ℕ) : (fun _ => 1 : Fin m → ℝ≥0∞) ∈ orth (flat (Fin m)) := by
  intro x hx
  have h : ∑ e, x e ≤ 1 := hx
  simpa [pairing] using h

/-- **First order.** The general semantics of `base n ⊸ base m` is `lin`. -/
theorem P_lolli_base (n m : ℕ) : P (lolli (base n) (base m)) = lin (Fin n) (Fin m) := by
  show orth (orth (orth _)) = _
  rw [orth_orth_orth]
  ext t
  constructor
  · intro ht x hx
    have := ht (tvec x fun _ => 1) ⟨x, hx, _, one_mem_orth_flat m, rfl⟩
    show ∑ b, app t x b ≤ 1
    simpa [pairing, tvec, app, Fintype.sum_prod_type, Finset.sum_comm (γ := Fin m)] using this
  · rintro ht _ ⟨x, hx, y, hy, rfl⟩
    have h1 := hy _ (ht x hx)
    calc pairing (tvec x y) t = pairing (app t x) y := by
          simp only [pairing, tvec, app, Fintype.sum_prod_type, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
      _ ≤ 1 := h1

/-- **Second order.** The general semantics of the second-order formula is `tD`. -/
theorem P_second (n m n' m' : ℕ) :
    P (second n m n' m') = tD (Fin n) (Fin m) (Fin n') (Fin m') := by
  show orth (orth (orth _)) = _
  rw [orth_orth_orth]
  ext t
  have key : ∀ y z, pairing (tvec y z) t = ∑ p, ∑ q, y p * t (p, q) * z q := fun y z => by
    simp only [pairing, tvec, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  constructor
  · intro ht y hy z hz
    have := ht _ ⟨y, (P_lolli_base n m).symm ▸ hy, z, (P_lolli_base n' m').symm ▸ hz, rfl⟩
    exact (key y z).symm.le.trans this
  · rintro ht _ ⟨y, hy, z, hz, rfl⟩
    exact (key y z).le.trans (ht y ((P_lolli_base n m) ▸ hy) z ((P_lolli_base n' m') ▸ hz))

/-- At first order the recipe equals the PCS. -/
theorem recipe_first_order (n m : ℕ) :
    P (lolli (base n) (base m)) = ConstructiveProb.Mix (Set.range
      (det : (Fin n → Option (Fin m)) → Fin n × Fin m → ℝ≥0∞)) := by
  rw [P_lolli_base]; exact ConstructiveProb.PCS.pcs_recipe

/-- At the second-order formula the recipe is the set of randomized sequential programs. -/
theorem recipe_second_order {n m n' m' : ℕ} (hn : 0 < n) (hn' : 0 < n') :
    ConstructiveProb.Mix {z | z ∈ P (second n m n' m') ∧ ∀ u, z u = 0 ∨ z u = 1}
      = sequentialG (Fin n) (Fin m) (Fin n') (Fin m') := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (Fin n') := ⟨⟨0, hn'⟩⟩
  rw [P_second]; exact recipe_eq_sequentialG

/-- An injection `Bool → Fin k` for `k ≥ 2`. -/
def boolFin {k : ℕ} (hk : 2 ≤ k) : Bool → Fin k := fun b => if b then ⟨1, hk⟩ else ⟨0, by omega⟩

theorem boolFin_inj {k : ℕ} (hk : 2 ≤ k) : Function.Injective (boolFin hk) := by
  intro a b h; cases a <;> cases b <;> simp_all [boolFin, Fin.ext_iff]

/-- At the second-order formula over data types with at least two elements, the recipe is
strictly smaller than the PCS. -/
theorem recipe_second_order_ssubset {n m n' m' : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hn' : 2 ≤ n')
    (hm' : 2 ≤ m') :
    ConstructiveProb.Mix {z | z ∈ P (second n m n' m') ∧ ∀ u, z u = 0 ∨ z u = 1}
      ⊂ P (second n m n' m') := by
  refine ⟨recipe_subset_P _, fun h => ?_⟩
  have hmem := pentE_mem (boolFin_inj hn) (boolFin_inj hm) (boolFin_inj hn') (boolFin_inj hm')
  rw [← P_second] at hmem
  obtain ⟨k, w, s, hs, hw, heq⟩ := h hmem
  exact pentE_not_mix (boolFin_inj hn) (boolFin_inj hm) (boolFin_inj hn') (boolFin_inj hm') w hw s
    (fun i => P_second n m n' m' ▸ (hs i).1) (fun i => (hs i).2) heq

/-! ### The inclusion of `sharp_isClique` is strict at a formula -/

open ConstructiveProb.PCS.General (emb cp cp_emb emb_inj)
open ConstructiveProb.PCS (W pent compat2 shannon shannon_card shannon_sub shannon_pairwise)

/-- The formula `T = ((base 2 ⊸ base 2) ⊗ (base 2 ⊸ base 2))^⊥`. -/
abbrev S2 : Fm := second 2 2 2 2

/-- `(T ⊗ T)^⊥`. -/
abbrev TT : Fm := neg (tens S2 S2)

theorem coh_lolli_base {n m : ℕ} (p q : Fin n × Fin m) :
    coh (lolli (base n) (base m)) p q ↔ cp p q := by
  show (p = q ∨ ¬ (p.1 = q.1 ∧ (p.2 = q.2 ∨ ¬ p.2 = q.2))) ↔ (p = q ∨ p.1 ≠ q.1)
  tauto

/-- The embedding of the `Bool` web of `T` into the web of `S2`. -/
def φ : W × W → web S2 := emb (boolFin le_rfl) (boolFin le_rfl) (boolFin le_rfl) (boolFin le_rfl)

theorem φ_inj : Function.Injective φ :=
  emb_inj (boolFin_inj le_rfl) (boolFin_inj le_rfl) (boolFin_inj le_rfl) (boolFin_inj le_rfl)

theorem coh_S2_φ (s t : W × W) : coh S2 (φ s) (φ t) ↔ s = t ∨ ¬ compat2 s t := by
  show (φ s = φ t ∨ ¬ (coh (lolli (base 2) (base 2)) (φ s).1 (φ t).1 ∧
    coh (lolli (base 2) (base 2)) (φ s).2 (φ t).2)) ↔ _
  rw [coh_lolli_base, coh_lolli_base, φ_inj.eq_iff]
  simp only [φ, emb]
  rw [cp_emb (boolFin_inj le_rfl) (boolFin_inj le_rfl),
    cp_emb (boolFin_inj le_rfl) (boolFin_inj le_rfl)]
  rfl

/-- Shannon's set in the web of `T ⊗ T`. -/
noncomputable def shannonF : Finset (web (tens S2 S2)) := shannon.image fun u => (φ u.1, φ u.2)

/-- **Shannon's set is a clique of the coherence space `(T ⊗ T)^⊥`.** -/
theorem shannonF_clique : ∀ u ∈ shannonF, ∀ v ∈ shannonF, coh TT u v := by
  intro u hu v hv
  obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨v', hv', rfl⟩ := Finset.mem_image.1 hv
  show (φ u'.1, φ u'.2) = (φ v'.1, φ v'.2) ∨
    ¬ (coh S2 (φ u'.1) (φ v'.1) ∧ coh S2 (φ u'.2) (φ v'.2))
  rw [coh_S2_φ, coh_S2_φ]
  rcases shannon_pairwise u' hu' v' hv' with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr h

/-- The pentagon element of `T`. -/
noncomputable def pentS2 : web S2 → ℝ≥0∞ :=
  pentE (boolFin le_rfl) (boolFin le_rfl) (boolFin le_rfl) (boolFin le_rfl)

theorem pentS2_mem : pentS2 ∈ P S2 := by
  have := pentE_mem (boolFin_inj (le_refl 2)) (boolFin_inj (le_refl 2)) (boolFin_inj (le_refl 2))
    (boolFin_inj (le_refl 2))
  rw [← P_second] at this
  exact this

/-- **The indicator of Shannon's clique is not an element of the PCS `(T ⊗ T)^⊥`.** So the
inclusion of `sharp_isClique` is strict at `(T ⊗ T)^⊥`. -/
theorem shannonF_not_mem : (fun u => if u ∈ shannonF then (1 : ℝ≥0∞) else 0) ∉ P TT := by
  intro h
  have hg : tvec pentS2 pentS2 ∈ P (tens S2 S2) :=
    ConstructiveProb.PCS.subset_orth_orth _ ⟨_, pentS2_mem, _, pentS2_mem, rfl⟩
  have := h _ hg
  have hval : ∀ u ∈ shannonF, tvec pentS2 pentS2 u = 2⁻¹ * 2⁻¹ := by
    intro u hu
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
    have h1 : φ u'.1 ∈ pent.image φ := Finset.mem_image_of_mem _ (shannon_sub u' hu').1
    have h2 : φ u'.2 ∈ pent.image φ := Finset.mem_image_of_mem _ (shannon_sub u' hu').2
    show (if φ u'.1 ∈ pent.image φ then (2⁻¹ : ℝ≥0∞) else 0) *
      (if φ u'.2 ∈ pent.image φ then (2⁻¹ : ℝ≥0∞) else 0) = _
    rw [if_pos h1, if_pos h2]
  have hcard : shannonF.card = 5 := by
    rw [shannonF, Finset.card_image_of_injective _ (fun a b h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext (φ_inj h.1) (φ_inj h.2)), shannon_card]
  simp only [pairing, mul_ite, mul_one, mul_zero] at this
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_congr rfl hval, Finset.sum_const, hcard, nsmul_eq_mul] at this
  have h4 : (2⁻¹ : ℝ≥0∞) * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]; norm_num
  rw [h4, ← div_eq_mul_inv, ENNReal.div_le_iff (by norm_num) (by norm_num)] at this
  norm_num at this

end ConstructiveProb.Linear
