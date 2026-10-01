/-
# The exponential `!Bool`

The web of `!Bool` is the set of finite multisets over `{t, f}`, i.e. pairs of counts `(i, j)`.
The PCS `!Bool` is the biorthogonal closure of the promotions `x^! (i, j) = x_t^i · x_f^j` of the
elements `x` of `Bool` (Danos–Ehrhard), with the pairing an infinite sum.

* `prom_mem`: every promotion is an element of `!Bool`.
* `sharp_bang_mixed_zero`: every certain (`{0,1}`-valued) element of `!Bool` vanishes on every
  mixed multiset `[t^i f^j]`, `i, j ≥ 1`. So certain elements live on the multisets whose support
  is a clique of `Bool`, which is Girard's web of `!Bool`.
* `prom_half_not_mix`: the promotion of `(1/2, 1/2)` gives `[t, f]` weight `1/4`, so it is no
  mixture of certain elements. The recipe fails at `!Bool`, without any second-order type.
-/
import ConstructiveProb.Recipe

open scoped ENNReal

namespace ConstructiveProb.PCS.Bang

/-- Orthogonal over an arbitrary (countable) web, with the pairing an infinite sum. -/
def orthI {E : Type*} (S : Set (E → ℝ≥0∞)) : Set (E → ℝ≥0∞) := {y | ∀ x ∈ S, ∑' e, x e * y e ≤ 1}

theorem subset_orthI_orthI {E : Type*} (S : Set (E → ℝ≥0∞)) : S ⊆ orthI (orthI S) := by
  intro x hx y hy
  simpa [mul_comm] using hy x hx

theorem orthI_anti {E : Type*} {S T : Set (E → ℝ≥0∞)} (h : S ⊆ T) : orthI T ⊆ orthI S :=
  fun _ hy x hx => hy x (h hx)

theorem orthI_triple {E : Type*} (S : Set (E → ℝ≥0∞)) : orthI (orthI (orthI S)) = orthI S :=
  le_antisymm (orthI_anti (subset_orthI_orthI S)) (subset_orthI_orthI _)

/-- Promotion `x^! (i, j) = x_t^i · x_f^j`. -/
noncomputable def prom (x : Bool → ℝ≥0∞) : ℕ × ℕ → ℝ≥0∞ := fun m => x true ^ m.1 * x false ^ m.2

/-- The generators of `!Bool`. -/
def gens : Set (ℕ × ℕ → ℝ≥0∞) := {u | ∃ x ∈ flat Bool, u = prom x}

/-- The PCS `!Bool`. -/
def bang : Set (ℕ × ℕ → ℝ≥0∞) := orthI (orthI gens)

theorem bang_closed : orthI (orthI bang) = bang := by
  unfold bang; rw [orthI_triple]

theorem prom_mem {x : Bool → ℝ≥0∞} (hx : x ∈ flat Bool) : prom x ∈ bang :=
  subset_orthI_orthI _ ⟨x, hx, rfl⟩

/-- `a + b ≤ 1` forces `4ab ≤ 1`. -/
theorem four_mul_le {a b : ℝ≥0∞} (h : a + b ≤ 1) : 4 * (a * b) ≤ 1 := by
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans h)
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans h)
  lift a to NNReal using ha
  lift b to NNReal using hb
  have h' : (a : ℝ) + b ≤ 1 := by exact_mod_cast h
  have : (4 : ℝ) * (a * b) ≤ 1 := by
    nlinarith [sq_nonneg ((a : ℝ) - b), NNReal.coe_nonneg a, NNReal.coe_nonneg b]
  exact_mod_cast this

theorem tsum_single_mul {E : Type*} [DecidableEq E] (f : E → ℝ≥0∞) (e₀ : E) (c : ℝ≥0∞) :
    ∑' e, f e * (Pi.single e₀ c : E → ℝ≥0∞) e = f e₀ * c := by
  rw [show (fun e => f e * (Pi.single e₀ c : E → ℝ≥0∞) e) = fun e => if e = e₀ then f e₀ * c else 0
    from funext fun e => by by_cases h : e = e₀ <;> simp [h, Pi.single_apply]]
  exact tsum_ite_eq e₀ _

/-- `4 · δ_(i,j)` is in the dual of `!Bool` for every mixed multiset. -/
theorem four_delta_mem {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (Pi.single (i, j) 4 : ℕ × ℕ → ℝ≥0∞) ∈ orthI gens := by
  rintro _ ⟨x, hx, rfl⟩
  rw [tsum_single_mul]
  have hsum : x true + x false ≤ 1 := by simpa [flat, Fintype.sum_bool] using hx
  have ht : x true ≤ 1 := le_self_add.trans hsum
  have hf : x false ≤ 1 := le_add_self.trans hsum
  calc prom x (i, j) * 4 = 4 * (x true ^ i * x false ^ j) := by simp [prom, mul_comm]
    _ ≤ 4 * (x true * x false) := by
        gcongr
        · exact pow_le_of_le_one bot_le ht (by omega)
        · exact pow_le_of_le_one bot_le hf (by omega)
    _ ≤ 1 := four_mul_le hsum

/-- **Certain elements of `!Bool` vanish on mixed multisets.** -/
theorem sharp_bang_mixed_zero {z : ℕ × ℕ → ℝ≥0∞} (hz : z ∈ bang) (h01 : ∀ m, z m = 0 ∨ z m = 1)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) : z (i, j) = 0 := by
  rcases h01 (i, j) with h | h
  · exact h
  · exfalso
    have := hz _ (four_delta_mem hi hj)
    rw [show (∑' e, (Pi.single (i, j) 4 : ℕ × ℕ → ℝ≥0∞) e * z e) = ∑' e, z e * (Pi.single (i, j) 4 :
      ℕ × ℕ → ℝ≥0∞) e from tsum_congr fun e => mul_comm _ _, tsum_single_mul, h, one_mul] at this
    norm_num at this

/-- The fair coin of `Bool`. -/
noncomputable def half : Bool → ℝ≥0∞ := fun _ => 2⁻¹

theorem half_mem : half ∈ flat Bool := by
  simp only [flat, Set.mem_setOf_eq, Fintype.sum_bool, half]
  rw [ENNReal.inv_two_add_inv_two]

/-- **The recipe fails at `!Bool`.** The promotion of the fair coin is an element of `!Bool`
but no mixture of certain elements: every such mixture vanishes at `[t, f]`, the promotion gives
it `1/4`. -/
theorem prom_half_not_mix : prom half ∈ bang ∧
    prom half ∉ Mix {z | z ∈ bang ∧ ∀ m, z m = 0 ∨ z m = 1} := by
  refine ⟨prom_mem half_mem, ?_⟩
  rintro ⟨n, w, s, hs, hw, heq⟩
  have h1 := congrFun heq (1, 1)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [Finset.sum_eq_zero fun i _ => by rw [sharp_bang_mixed_zero (hs i).1 (hs i).2 le_rfl le_rfl,
    mul_zero]] at h1
  simp [prom, half] at h1

end ConstructiveProb.PCS.Bang
