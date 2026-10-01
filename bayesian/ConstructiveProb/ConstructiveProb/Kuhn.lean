/-
# Randomized sequential strategies are mixtures of deterministic ones

The direction of Kuhn's theorem needed here: a behavioural strategy (coin flips at each decision
node) is a mixture of deterministic strategies (`FFirst.den_mem_Mix`, `GFirst.den_mem_Mix`). The
weight of a deterministic strategy is the product of the probabilities of its choices, with
divergence completing each node to a probability.

Consequence (`recipe_second_order_eq_hull_sequential`): at second order the recipe's calculus,
`Mix` of the certain elements of the PCS, is exactly the convex hull of the randomized sequential
programs.
-/
import ConstructiveProb.Recipe

open scoped ENNReal
open Finset

namespace ConstructiveProb.PCS

/-- Marginal of a product weight: summing `∏ i, q i (σ i)` over all choice functions `σ`, with
`σ i₀ = k₀` imposed, leaves `q i₀ k₀`. -/
theorem marg {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (q : I → K → ℝ≥0∞) (hq : ∀ i, ∑ k, q i k = 1) (i₀ : I) (k₀ : K) :
    ∑ σ : I → K, (∏ i, q i (σ i)) * (if σ i₀ = k₀ then 1 else 0) = q i₀ k₀ := by
  let f : I → K → ℝ≥0∞ := fun i k => q i k * (if i = i₀ then (if k = k₀ then 1 else 0) else 1)
  have h1 : ∀ σ : I → K, (∏ i, q i (σ i)) * (if σ i₀ = k₀ then 1 else 0) = ∏ i, f i (σ i) := by
    intro σ
    simp only [f, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' univ i₀, if_pos (Finset.mem_univ _)]
  simp only [h1]
  rw [← Fintype.prod_sum f]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  have h2 : ∑ k, f i₀ k = q i₀ k₀ := by
    simp only [f, if_true, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']; simp
  have h3 : ∏ i ∈ univ.erase i₀, ∑ k, f i k = 1 :=
    Finset.prod_eq_one fun i hi => by
      simp only [f, Finset.ne_of_mem_erase hi, if_false, mul_one]; exact hq i
  rw [h2, h3, mul_one]

theorem total {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]
    (q : I → K → ℝ≥0∞) (hq : ∀ i, ∑ k, q i k = 1) : ∑ σ : I → K, ∏ i, q i (σ i) = 1 := by
  rw [← Fintype.prod_sum q]; exact Finset.prod_eq_one fun i _ => hq i

/-- Completion of a sub-distribution on `Bool` to a distribution on `Option Bool`. -/
noncomputable def comp (m : Bool → ℝ≥0∞) : Option Bool → ℝ≥0∞
  | none => 1 - (m true + m false)
  | some b => m b

theorem comp_sum (m : Bool → ℝ≥0∞) (h : m true + m false ≤ 1) : ∑ o, comp m o = 1 := by
  rw [Fintype.sum_option]; simp only [comp, Fintype.sum_bool]
  rw [add_comm (m true)]; exact tsub_add_cancel_of_le (by simpa [add_comm] using h)

/-- Completion of a probability `r ≤ 1` to a distribution on `Bool`. -/
noncomputable def bern (r : ℝ≥0∞) : Bool → ℝ≥0∞
  | true => r
  | false => 1 - r

theorem bern_sum (r : ℝ≥0∞) (h : r ≤ 1) : ∑ b, bern r b = 1 := by
  simp only [Fintype.sum_bool, bern]; exact add_tsub_cancel_of_le h

/-- A deterministic choice of every node: first input (or divergence), second input after each
first answer (or divergence), and halt/diverge after each pair of answers. -/
abbrev Choice := (Unit → Option Bool) × (Bool × Bool → Option Bool) × (Bool × Bool × Bool × Bool → Bool)

/-- The `{0,1}`-valued core `[first = a] · [second = c] · [halt]`. -/
noncomputable def detCore (σ : Choice) (a b c d : Bool) : ℝ≥0∞ :=
  (if σ.1 () = some a then 1 else 0) * (if σ.2.1 (a, b) = some c then 1 else 0) *
    (if σ.2.2 (a, b, c, d) = true then 1 else 0)

/-- **Behavioural = mixed (core form).** The behavioural core `μ a · κ a b c · ρ a b c d` is the
mixture of deterministic cores with product weights. -/
theorem core_eq_mix (μ : Bool → ℝ≥0∞) (κ : Bool → Bool → Bool → ℝ≥0∞)
    (ρ : Bool → Bool → Bool → Bool → ℝ≥0∞) (hμ : μ true + μ false ≤ 1)
    (hκ : ∀ a b, κ a b true + κ a b false ≤ 1) (hρ : ∀ a b c d, ρ a b c d ≤ 1) :
    ∃ W : Choice → ℝ≥0∞, ∑ σ, W σ = 1 ∧
      ∀ a b c d, μ a * κ a b c * ρ a b c d = ∑ σ, W σ * detCore σ a b c d := by
  classical
  let q1 : Unit → Option Bool → ℝ≥0∞ := fun _ => comp μ
  let q2 : Bool × Bool → Option Bool → ℝ≥0∞ := fun ab => comp (κ ab.1 ab.2)
  let q3 : Bool × Bool × Bool × Bool → Bool → ℝ≥0∞ := fun x => bern (ρ x.1 x.2.1 x.2.2.1 x.2.2.2)
  have h1 : ∀ i, ∑ k, q1 i k = 1 := fun _ => comp_sum μ hμ
  have h2 : ∀ i, ∑ k, q2 i k = 1 := fun ab => comp_sum _ (hκ ab.1 ab.2)
  have h3 : ∀ i, ∑ k, q3 i k = 1 := fun x => bern_sum _ (hρ _ _ _ _)
  refine ⟨fun σ => (∏ i, q1 i (σ.1 i)) * (∏ i, q2 i (σ.2.1 i)) * (∏ i, q3 i (σ.2.2 i)), ?_, ?_⟩
  · rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun σ1 _ => Fintype.sum_prod_type _]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [total q1 h1, total q2 h2, total q3 h3]; simp
  · intro a b c d
    have e1 := marg q1 h1 () (some a)
    have e2 := marg q2 h2 (a, b) (some c)
    have e3 := marg q3 h3 (a, b, c, d) true
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun σ1 _ => Fintype.sum_prod_type _]
    calc μ a * κ a b c * ρ a b c d = q1 () (some a) * q2 (a, b) (some c) * q3 (a, b, c, d) true :=
          rfl
      _ = _ := by rw [← e1, ← e2, ← e3]
      _ = _ := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ1 _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ2 _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ3 _ => ?_
          simp only [detCore]
          ring

/-- The deterministic `f`-first strategy of a choice. -/
noncomputable def detF (σ : Choice) : FFirst where
  μ a := if σ.1 () = some a then 1 else 0
  κ a b c := if σ.2.1 (a, b) = some c then 1 else 0
  ρ a b c d := if σ.2.2 (a, b, c, d) = true then 1 else 0
  hμ := by cases h : σ.1 () with
    | none => simp
    | some v => cases v <;> simp
  hκ a b := by cases h : σ.2.1 (a, b) with
    | none => simp [h]
    | some v => cases v <;> simp [h]
  hρ _ _ _ _ := by split_ifs <;> simp

/-- The deterministic `g`-first strategy of a choice (roles of `f` and `g` swapped). -/
noncomputable def detG (σ : Choice) : GFirst where
  μ c := if σ.1 () = some c then 1 else 0
  κ c d a := if σ.2.1 (c, d) = some a then 1 else 0
  ρ c d a b := if σ.2.2 (c, d, a, b) = true then 1 else 0
  hμ := by cases h : σ.1 () with
    | none => simp
    | some v => cases v <;> simp
  hκ c d := by cases h : σ.2.1 (c, d) with
    | none => simp [h]
    | some v => cases v <;> simp [h]
  hρ _ _ _ _ := by split_ifs <;> simp

theorem detF_den (σ : Choice) (pq : W × W) :
    (detF σ).den pq = detCore σ pq.1.1 pq.1.2 pq.2.1 pq.2.2 := rfl

theorem detG_den (σ : Choice) (pq : W × W) :
    (detG σ).den pq = detCore σ pq.2.1 pq.2.2 pq.1.1 pq.1.2 := rfl

theorem detCore_sharp (σ : Choice) (a b c d : Bool) :
    detCore σ a b c d = 0 ∨ detCore σ a b c d = 1 := by
  unfold detCore; split_ifs <;> simp

/-- Deterministic sequential strategies are certain sequential denotations. -/
theorem detF_mem (σ : Choice) :
    (detF σ).den ∈ {z | z ∈ sequential ∧ ∀ pq, z pq = 0 ∨ z pq = 1} :=
  ⟨⟨1, 0, detF σ, idleG, by simp, by funext pq; simp⟩, fun pq => detCore_sharp σ _ _ _ _⟩

theorem detG_mem (σ : Choice) :
    (detG σ).den ∈ {z | z ∈ sequential ∧ ∀ pq, z pq = 0 ∨ z pq = 1} :=
  ⟨⟨0, 1, idleF, detG σ, by simp, by funext pq; simp⟩, fun pq => detCore_sharp σ _ _ _ _⟩

/-- The certain sequential denotations. -/
def sharpSeq : Set (W × W → ℝ≥0∞) := {z | z ∈ sequential ∧ ∀ pq, z pq = 0 ∨ z pq = 1}

/-- **Kuhn, `f`-first.** Every randomized `f`-first strategy is a mixture of deterministic ones. -/
theorem FFirst.den_mem_Mix (F : FFirst) : F.den ∈ Mix sharpSeq := by
  obtain ⟨Wt, hW, heq⟩ := core_eq_mix F.μ F.κ F.ρ F.hμ F.hκ F.hρ
  have : F.den = ∑ σ, Wt σ • (detF σ).den := by
    funext pq
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, detF_den]
    exact heq _ _ _ _
  rw [this]
  exact mem_Mix_of_fintype Wt _ detF_mem hW

/-- **Kuhn, `g`-first.** -/
theorem GFirst.den_mem_Mix (G : GFirst) : G.den ∈ Mix sharpSeq := by
  obtain ⟨Wt, hW, heq⟩ := core_eq_mix G.μ G.κ G.ρ G.hμ G.hκ G.hρ
  have : G.den = ∑ σ, Wt σ • (detG σ).den := by
    funext pq
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, detG_den]
    exact heq _ _ _ _
  rw [this]
  exact mem_Mix_of_fintype Wt _ detG_mem hW

/-- **Every randomized sequential program is a mixture of deterministic sequential programs.** -/
theorem sequential_subset_Mix : sequential ⊆ Mix sharpSeq := by
  rintro _ ⟨α, β, F, G, hαβ, rfl⟩
  rw [← Mix_Mix]
  have h0 : (0 : W × W → ℝ≥0∞) ∈ Mix sharpSeq := by
    have := (idleF).den_mem_Mix
    have hz : idleF.den = 0 := by funext pq; simp [FFirst.den, idleF]
    rwa [hz] at this
  let w : Fin 3 → ℝ≥0∞ := ![α, β, 1 - (α + β)]
  let s : Fin 3 → W × W → ℝ≥0∞ := ![F.den, G.den, 0]
  refine ⟨3, w, s, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact F.den_mem_Mix
    · exact G.den_mem_Mix
    · exact h0
  · simp only [w, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact add_tsub_cancel_of_le hαβ
  · simp [w, s, Fin.sum_univ_three]

/-- **The recipe at second order is the convex hull of randomized sequential programs.** -/
theorem recipe_second_order_eq_hull_sequential :
    Mix {z | z ∈ tensDual ∧ ∀ pq, z pq = 0 ∨ z pq = 1} = Mix sequential := by
  rw [sharp_tensDual_eq_sharp_sequential]
  apply le_antisymm
  · rintro _ ⟨n, w, s, hs, hw, rfl⟩
    exact ⟨n, w, s, fun i => (hs i).1, hw, rfl⟩
  · calc Mix sequential ⊆ Mix (Mix sharpSeq) := by
          rintro _ ⟨n, w, s, hs, hw, rfl⟩
          exact ⟨n, w, s, fun i => sequential_subset_Mix (hs i), hw, rfl⟩
      _ = Mix sharpSeq := Mix_Mix _
      _ = _ := rfl

/-! ### The converse: mixtures of sequential strategies are sequential -/

/-- **Mixing behavioural strategies (core form).** A weighted sum of behavioural cores is again
a behavioural core: the first-node weights add up, and the later nodes use the conditional
probabilities given the history. -/
theorem core_mix {n : ℕ} (w : Fin n → ℝ≥0∞) (μ : Fin n → Bool → ℝ≥0∞)
    (κ : Fin n → Bool → Bool → Bool → ℝ≥0∞) (ρ : Fin n → Bool → Bool → Bool → Bool → ℝ≥0∞)
    (hfin : ∀ i a, w i * μ i a ≠ ⊤) (hκ : ∀ i a b, κ i a b true + κ i a b false ≤ 1)
    (hρ : ∀ i a b c d, ρ i a b c d ≤ 1) :
    ∃ (κ' : Bool → Bool → Bool → ℝ≥0∞) (ρ' : Bool → Bool → Bool → Bool → ℝ≥0∞),
      (∀ a b, κ' a b true + κ' a b false ≤ 1) ∧ (∀ a b c d, ρ' a b c d ≤ 1) ∧
      ∀ a b c d, (∑ i, w i * μ i a) * κ' a b c * ρ' a b c d
        = ∑ i, w i * (μ i a * κ i a b c * ρ i a b c d) := by
  let m : Bool → ℝ≥0∞ := fun a => ∑ i, w i * μ i a
  let nn : Bool → Bool → Bool → ℝ≥0∞ := fun a b c => ∑ i, w i * μ i a * κ i a b c
  let num : Bool → Bool → Bool → Bool → ℝ≥0∞ :=
    fun a b c d => ∑ i, w i * μ i a * κ i a b c * ρ i a b c d
  have hm_fin : ∀ a, m a ≠ ⊤ := fun a => ENNReal.sum_ne_top.2 fun i _ => hfin i a
  have hnn_le : ∀ a b, nn a b true + nn a b false ≤ m a := by
    intro a b
    simp only [nn, m, ← Finset.sum_add_distrib, ← mul_add]
    exact Finset.sum_le_sum fun i _ => (mul_le_mul_left' (hκ i a b) _).trans (by rw [mul_one])
  have hnn_le' : ∀ a b c, nn a b c ≤ m a := fun a b c => by
    cases c
    · exact le_add_self.trans (hnn_le a b)
    · exact le_self_add.trans (hnn_le a b)
  have hnum_le : ∀ a b c d, num a b c d ≤ nn a b c := fun a b c d =>
    Finset.sum_le_sum fun i _ => (mul_le_mul_left' (hρ i a b c d) _).trans (by rw [mul_one])
  refine ⟨fun a b c => nn a b c / m a, fun a b c d => num a b c d / nn a b c, ?_, ?_, ?_⟩
  · intro a b
    rw [ENNReal.div_add_div_same]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hnn_le a b)
  · intro a b c d
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hnum_le a b c d)
  · intro a b c d
    have hrhs : ∑ i, w i * (μ i a * κ i a b c * ρ i a b c d) = num a b c d :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [hrhs]
    change m a * (nn a b c / m a) * (num a b c d / nn a b c) = num a b c d
    by_cases hm0 : m a = 0
    · have hn : nn a b c = 0 := le_antisymm (hm0 ▸ hnn_le' a b c) bot_le
      have hu : num a b c d = 0 := le_antisymm (hn ▸ hnum_le a b c d) bot_le
      rw [hm0, hu]; simp
    · rw [ENNReal.mul_div_cancel hm0 (hm_fin a)]
      by_cases hn0 : nn a b c = 0
      · have hu : num a b c d = 0 := le_antisymm (hn0 ▸ hnum_le a b c d) bot_le
        rw [hn0, hu]; simp
      · exact ENNReal.mul_div_cancel hn0
          (ne_top_of_le_ne_top (hm_fin a) (hnn_le' a b c))

/-- A behavioural core without the first-node normalization. -/
structure Beh where
  μ : Bool → ℝ≥0∞
  κ : Bool → Bool → Bool → ℝ≥0∞
  ρ : Bool → Bool → Bool → Bool → ℝ≥0∞
  hκ : ∀ a b, κ a b true + κ a b false ≤ 1
  hρ : ∀ a b c d, ρ a b c d ≤ 1

noncomputable def Beh.val (B : Beh) (a b c d : Bool) : ℝ≥0∞ := B.μ a * B.κ a b c * B.ρ a b c d

noncomputable def Beh.mass (B : Beh) : ℝ≥0∞ := B.μ true + B.μ false

theorem Beh.μ_le_mass (B : Beh) (a : Bool) : B.μ a ≤ B.mass := by
  cases a
  · exact le_add_self
  · exact le_self_add

/-- Sequential denotations with the first choice (which function, which input) unnormalized. -/
def seqU : Set (W × W → ℝ≥0∞) :=
  {t | ∃ BF BG : Beh, BF.mass + BG.mass ≤ 1 ∧
    t = fun pq => BF.val pq.1.1 pq.1.2 pq.2.1 pq.2.2 + BG.val pq.2.1 pq.2.2 pq.1.1 pq.1.2}

/-- Normalizing an unnormalized core: `B.mass • (normalized B) = B`. -/
theorem Beh.normalize (B : Beh) (h : B.mass ≤ 1) :
    ∃ μ' : Bool → ℝ≥0∞, μ' true + μ' false ≤ 1 ∧ ∀ a, B.mass * μ' a = B.μ a := by
  by_cases h0 : B.mass = 0
  · refine ⟨fun _ => 0, by simp, fun a => ?_⟩
    have := B.μ_le_mass a
    rw [h0] at this
    rw [h0, zero_mul]; exact (le_antisymm this bot_le).symm
  · have hT : B.mass ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h
    refine ⟨fun a => B.μ a / B.mass, ?_, fun a => ENNReal.mul_div_cancel h0 hT⟩
    rw [ENNReal.div_add_div_same]; exact ENNReal.div_self_le_one

theorem sequential_eq_seqU : sequential = seqU := by
  ext t
  constructor
  · rintro ⟨α, β, F, G, hαβ, rfl⟩
    refine ⟨⟨fun a => α * F.μ a, F.κ, F.ρ, F.hκ, F.hρ⟩, ⟨fun c => β * G.μ c, G.κ, G.ρ, G.hκ, G.hρ⟩,
      ?_, ?_⟩
    · simp only [Beh.mass, ← mul_add]
      calc α * (F.μ true + F.μ false) + β * (G.μ true + G.μ false) ≤ α * 1 + β * 1 := by
            gcongr
            · exact F.hμ
            · exact G.hμ
        _ ≤ 1 := by simpa using hαβ
    · funext pq; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, FFirst.den, GFirst.den,
        Beh.val]; ring
  · rintro ⟨BF, BG, hm, rfl⟩
    obtain ⟨μF, hμF, eF⟩ := BF.normalize (le_self_add.trans hm)
    obtain ⟨μG, hμG, eG⟩ := BG.normalize (le_add_self.trans hm)
    refine ⟨BF.mass, BG.mass, ⟨μF, BF.κ, BF.ρ, hμF, BF.hκ, BF.hρ⟩,
      ⟨μG, BG.κ, BG.ρ, hμG, BG.hκ, BG.hρ⟩, hm, ?_⟩
    funext pq
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, FFirst.den, GFirst.den, Beh.val,
      ← eF, ← eG]
    ring

/-- **Mixtures of sequential strategies are sequential.** -/
theorem Mix_seqU : Mix seqU = seqU := by
  apply le_antisymm
  · rintro _ ⟨n, w, t, ht, hw, rfl⟩
    choose BF BG hm ht using ht
    have hw1 : ∀ i, w i ≤ 1 := fun i => hw ▸ Finset.single_le_sum (fun _ _ => bot_le)
      (Finset.mem_univ i)
    have hfinF : ∀ i a, w i * (BF i).μ a ≠ ⊤ := fun i a => ENNReal.mul_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hw1 i))
      (ne_top_of_le_ne_top ENNReal.one_ne_top (((BF i).μ_le_mass a).trans (le_self_add.trans (hm i))))
    have hfinG : ∀ i a, w i * (BG i).μ a ≠ ⊤ := fun i a => ENNReal.mul_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hw1 i))
      (ne_top_of_le_ne_top ENNReal.one_ne_top (((BG i).μ_le_mass a).trans (le_add_self.trans (hm i))))
    obtain ⟨κF, ρF, hκF, hρF, eF⟩ := core_mix w (fun i => (BF i).μ) (fun i => (BF i).κ)
      (fun i => (BF i).ρ) hfinF (fun i => (BF i).hκ) (fun i => (BF i).hρ)
    obtain ⟨κG, ρG, hκG, hρG, eG⟩ := core_mix w (fun i => (BG i).μ) (fun i => (BG i).κ)
      (fun i => (BG i).ρ) hfinG (fun i => (BG i).hκ) (fun i => (BG i).hρ)
    refine ⟨⟨fun a => ∑ i, w i * (BF i).μ a, κF, ρF, hκF, hρF⟩,
      ⟨fun c => ∑ i, w i * (BG i).μ c, κG, ρG, hκG, hρG⟩, ?_, ?_⟩
    · simp only [Beh.mass, ← Finset.sum_add_distrib, ← mul_add]
      calc ∑ i, w i * ((BF i).μ true + (BF i).μ false + ((BG i).μ true + (BG i).μ false))
          ≤ ∑ i, w i * 1 := by
            refine Finset.sum_le_sum fun i _ => mul_le_mul_left' ?_ _
            have := hm i; simp only [Beh.mass] at this; exact this
        _ = 1 := by simp [hw]
    · funext pq
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Beh.val, eF, eG]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ht i]; simp only [Beh.val]; ring
  · intro t ht
    exact ⟨1, fun _ => 1, fun _ => t, fun _ => ht, by simp, by simp⟩

/-- **The randomized sequential programs are convex.** -/
theorem Mix_sequential : Mix sequential = sequential := by
  rw [sequential_eq_seqU, Mix_seqU]

/-- **The recipe at second order is exactly the set of randomized sequential programs.** -/
theorem recipe_second_order_eq_sequential' :
    Mix {z | z ∈ tensDual ∧ ∀ pq, z pq = 0 ∨ z pq = 1} = sequential := by
  rw [recipe_second_order_eq_hull_sequential, Mix_sequential]

end ConstructiveProb.PCS
