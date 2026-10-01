/-
# A coherence-space clique that is not a PCS element

At `T = ((Bool ⊸ Bool) ⊗ (Bool ⊸ Bool))^⊥` the certain elements of the PCS are the cliques of
the coherence space (`sharp_tensDual_iff_clique`). One tensor further this fails. On the five
pentagon points the incoherence graph of `T` is a `5`-cycle, so an anticlique of `T ⊗ T` on the
pentagon is a stable set of the strong product `C₅ ⊠ C₅`, which has Shannon's five-element stable
set `{(cᵢ, c₂ᵢ)}`. That set `w` is a clique of the coherence space `(T ⊗ T)^⊥`
(`shannon_clique`), but `pentElt ⊗ pentElt ∈ P(T ⊗ T)` pairs with its indicator to `5/4 > 1`, so
the indicator is not an element of the PCS `(T ⊗ T)^⊥` (`shannon_not_mem`).
-/
import ConstructiveProb.Coherence

open scoped ENNReal
open Finset

namespace ConstructiveProb.PCS

/-- Web of `T ⊗ T`. -/
abbrev W2 := (W × W) × (W × W)

/-- Tensor of two elements of `T`. -/
noncomputable def tens2 (t t' : W × W → ℝ≥0∞) : W2 → ℝ≥0∞ := fun u => t u.1 * t' u.2

/-- Generators of the PCS `T ⊗ T`. -/
def gensTT : Set (W2 → ℝ≥0∞) := {u | ∃ t ∈ tensDual, ∃ t' ∈ tensDual, u = tens2 t t'}

/-- The PCS `T ⊗ T` and its dual `(T ⊗ T)^⊥`. -/
def PTT : Set (W2 → ℝ≥0∞) := orth (orth gensTT)
def PTTdual : Set (W2 → ℝ≥0∞) := orth gensTT

theorem PTTdual_eq : PTTdual = orth PTT := (orth_orth_orth gensTT).symm

/-- Coherence of `T ⊗ T` and of `(T ⊗ T)^⊥`. -/
def cohTT : W2 → W2 → Prop := tensC secondC secondC
def cohTTdual : W2 → W2 → Prop := dualC cohTT

/-- Shannon's set `{(cᵢ, c₂ᵢ)}`, for the pentagon in the cyclic order `c` of its exclusivity
graph: `c = (((t,t),(t,t)), ((f,t),(f,t)), ((f,t),(t,f)), ((t,f),(f,f)), ((f,f),(f,f)))`. -/
def shannon : Finset W2 :=
  {(((true, true), (true, true)), ((true, true), (true, true))),
   (((false, true), (false, true)), ((false, true), (true, false))),
   (((false, true), (true, false)), ((false, false), (false, false))),
   (((true, false), (false, false)), ((false, true), (false, true))),
   (((false, false), (false, false)), ((true, false), (false, false)))}

theorem shannon_card : shannon.card = 5 := by decide

theorem shannon_sub : ∀ u ∈ shannon, u.1 ∈ pent ∧ u.2 ∈ pent := by
  intro u hu; fin_cases hu <;> decide

theorem shannon_pairwise : ∀ u ∈ shannon, ∀ v ∈ shannon,
    u = v ∨ ¬ ((u.1 = v.1 ∨ ¬ compat2 u.1 v.1) ∧ (u.2 = v.2 ∨ ¬ compat2 u.2 v.2)) := by
  intro u hu v hv; fin_cases hu <;> fin_cases hv <;> decide

/-- **Shannon's set is a clique of the coherence space `(T ⊗ T)^⊥`.** -/
theorem shannon_clique : IsClique cohTTdual (· ∈ shannon) := by
  intro u v hu hv
  simp only [cohTTdual, cohTT, dualC, tensC, secondC_iff]
  exact shannon_pairwise u hu v hv

/-- `pentElt ⊗ pentElt` is an element of `T ⊗ T`. -/
theorem pent_tens_mem : tens2 pentElt pentElt ∈ PTT :=
  subset_orth_orth _ ⟨pentElt, pentElt_mem, pentElt, pentElt_mem, rfl⟩

/-- **The indicator of Shannon's clique is not an element of the PCS `(T ⊗ T)^⊥`.** -/
theorem shannon_not_mem :
    (fun u => if u ∈ shannon then (1 : ℝ≥0∞) else 0) ∉ PTTdual := by
  intro h
  have := h _ ⟨pentElt, pentElt_mem, pentElt, pentElt_mem, rfl⟩
  simp only [pairing, tens2, mul_ite, mul_one, mul_zero] at this
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_congr rfl fun u hu => show pentElt u.1 * pentElt u.2 = 2⁻¹ * 2⁻¹ by
      rw [pentElt, pentElt, if_pos (shannon_sub u hu).1, if_pos (shannon_sub u hu).2],
    Finset.sum_const, shannon_card, nsmul_eq_mul] at this
  have h4 : (2⁻¹ : ℝ≥0∞) * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]; norm_num
  rw [h4, ← div_eq_mul_inv, ENNReal.div_le_iff (by norm_num) (by norm_num)] at this
  norm_num at this

end ConstructiveProb.PCS
