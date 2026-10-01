/-
# Kuhn's theorem over arbitrary finite data types

For finite data types `X, Y, X', Y'` and `T = ((X ⊸ Y) ⊗ (X' ⊸ Y'))^⊥`, the recipe's calculus is
exactly the set of randomized sequential programs (`recipe_eq_sequentialG`):

* every randomized sequential program is an element of `T` (`sequentialG_subset_tD`);
* behavioural = mixed: every randomized sequential program is a mixture of deterministic ones
  (`sequentialG_subset_Mix`);
* mixed = behavioural: mixtures of randomized sequential programs are randomized sequential
  programs (`Mix_sequentialG`);
* the certain elements of `T` are the deterministic sequential programs (`General.sharp_tD_iff`).
-/
import ConstructiveProb.General
import ConstructiveProb.Kuhn

open scoped ENNReal
open Finset

namespace ConstructiveProb.PCS.General

variable {X Y X' Y' : Type} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
  [DecidableEq X] [DecidableEq Y] [DecidableEq X'] [DecidableEq Y']

/-! ### Behavioural strategies -/

/-- A behavioural core: first input `μ` (sub-probability), then a sub-probability `κ a b` over the
second input after the first answer, then a halting probability `ρ`. Read for either order. -/
structure Core (A B C D : Type) [Fintype A] [Fintype C] where
  μ : A → ℝ≥0∞
  κ : A → B → C → ℝ≥0∞
  ρ : A → B → C → D → ℝ≥0∞
  hκ : ∀ a b, ∑ c, κ a b c ≤ 1
  hρ : ∀ a b c d, ρ a b c d ≤ 1

variable {A B C D : Type} [Fintype A] [Fintype C]

noncomputable def Core.val (K : Core A B C D) (a : A) (b : B) (c : C) (d : D) : ℝ≥0∞ :=
  K.μ a * K.κ a b c * K.ρ a b c d

noncomputable def Core.mass (K : Core A B C D) : ℝ≥0∞ := ∑ a, K.μ a

theorem Core.μ_le_mass (K : Core A B C D) (a : A) : K.μ a ≤ K.mass :=
  Finset.single_le_sum (f := K.μ) (fun _ _ => bot_le) (Finset.mem_univ a)

/-- Randomized sequential programs: an `f`-first core plus a `g`-first core, of total first-node
mass at most `1`. -/
def sequentialG (X Y X' Y' : Type) [Fintype X] [Fintype X'] : Set ((X × Y) × (X' × Y') → ℝ≥0∞) :=
  {t | ∃ (F : Core X Y X' Y') (G : Core X' Y' X Y), F.mass + G.mass ≤ 1 ∧
    t = fun pq => F.val pq.1.1 pq.1.2 pq.2.1 pq.2.2 + G.val pq.2.1 pq.2.2 pq.1.1 pq.1.2}

/-! ### Sequential programs are elements of the PCS -/

theorem Core.pair_le {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq C] (K : Core A B C D)
    (f : A → Option B) (g : C → Option D) :
    ∑ p : A × B, ∑ q : C × D, det f p * K.val p.1 p.2 q.1 q.2 * det g q ≤ K.mass := by
  classical
  have step : ∀ a b, ∑ q : C × D, det f (a, b) * K.val a b q.1 q.2 * det g q
      ≤ det f (a, b) * K.μ a := by
    intro a b
    calc ∑ q : C × D, det f (a, b) * K.val a b q.1 q.2 * det g q
        ≤ ∑ q : C × D, det f (a, b) * K.μ a * (K.κ a b q.1 * det g q) := by
          refine Finset.sum_le_sum fun q _ => ?_
          simp only [Core.val]
          calc det f (a, b) * (K.μ a * K.κ a b q.1 * K.ρ a b q.1 q.2) * det g q
              ≤ det f (a, b) * (K.μ a * K.κ a b q.1 * 1) * det g q := by
                gcongr; exact K.hρ _ _ _ _
            _ = _ := by ring
      _ = det f (a, b) * K.μ a * ∑ c, K.κ a b c * ∑ d, det g (c, d) := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type]
          simp only [Finset.mul_sum]
      _ ≤ det f (a, b) * K.μ a * ∑ c, K.κ a b c * 1 := by
          gcongr with c; exact det_row_le_one g c
      _ ≤ det f (a, b) * K.μ a * 1 := by gcongr; simpa using K.hκ a b
      _ = _ := mul_one _
  calc ∑ p : A × B, ∑ q : C × D, det f p * K.val p.1 p.2 q.1 q.2 * det g q
      ≤ ∑ p : A × B, det f p * K.μ p.1 := Finset.sum_le_sum fun p _ => step p.1 p.2
    _ = ∑ a, K.μ a * ∑ b, det f (a, b) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    _ ≤ ∑ a, K.μ a * 1 := by gcongr with a; exact det_row_le_one f a
    _ = K.mass := by simp [Core.mass]

theorem sequentialG_subset_tD : sequentialG X Y X' Y' ⊆ tD X Y X' Y' := by
  rintro _ ⟨F, G, hm, rfl⟩
  refine mem_tD_of_det _ fun f g => ?_
  rw [← pair_det']
  have hF := F.pair_le f g
  have hG := G.pair_le g f
  calc ∑ p, ∑ q, det f p * (F.val p.1 p.2 q.1 q.2 + G.val q.1 q.2 p.1 p.2) * det g q
      = ∑ p, ∑ q, det f p * F.val p.1 p.2 q.1 q.2 * det g q
        + ∑ q, ∑ p, det g q * G.val q.1 q.2 p.1 p.2 * det f p := by
        rw [Finset.sum_comm (f := fun q p => det g q * G.val q.1 q.2 p.1 p.2 * det f p),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ ≤ F.mass + G.mass := add_le_add hF hG
    _ ≤ 1 := hm

/-! ### Certain elements are deterministic sequential programs -/

theorem sharp_mem_sequentialG [Nonempty X] [Nonempty X'] {z : (X × Y) × (X' × Y') → ℝ≥0∞}
    (hz : z ∈ tD X Y X' Y') (h01 : ∀ u, z u = 0 ∨ z u = 1) : z ∈ sequentialG X Y X' Y' := by
  classical
  have hρ : ∀ u, z u ≤ 1 := fun u => by rcases h01 u with h | h <;> simp [h]
  let zero' : Core X' Y' X Y := ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩
  let zeroF : Core X Y X' Y' := ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩
  rcases (sharp_tD_iff h01).1 hz with ⟨a, cf, hT⟩ | ⟨c, af, hT⟩
  · let F : Core X Y X' Y' := ⟨fun x => if x = a then 1 else 0, fun _ b c => if c = cf b then 1 else 0,
      fun a b c d => z ((a, b), (c, d)), fun _ b => by simp, fun _ _ _ _ => hρ _⟩
    refine ⟨F, zero', by simp [Core.mass, F, zero'], ?_⟩
    funext pq
    simp only [Core.val, F, zero', mul_zero, add_zero]
    rcases h01 pq with h | h
    · simp [h]
    · rw [if_pos (hT pq h).1, if_pos (hT pq h).2]; simp
  · let G : Core X' Y' X Y := ⟨fun x => if x = c then 1 else 0, fun _ d a => if a = af d then 1 else 0,
      fun c d a b => z ((a, b), (c, d)), fun _ d => by simp, fun _ _ _ _ => hρ _⟩
    refine ⟨zeroF, G, by simp [Core.mass, G, zeroF], ?_⟩
    funext pq
    simp only [Core.val, G, zeroF, zero_mul, zero_add]
    rcases h01 pq with h | h
    · simp [h]
    · rw [if_pos (hT pq h).1, if_pos (hT pq h).2]; simp

/-! ### Behavioural = mixed -/

/-- Completion of a sub-probability on `A` to a probability on `Option A`. -/
noncomputable def compl' (m : A → ℝ≥0∞) : Option A → ℝ≥0∞
  | none => 1 - ∑ a, m a
  | some a => m a

theorem compl'_sum (m : A → ℝ≥0∞) (h : ∑ a, m a ≤ 1) : ∑ o, compl' m o = 1 := by
  rw [Fintype.sum_option]; simp only [compl']; exact tsub_add_cancel_of_le h

/-- A deterministic choice at every node. -/
abbrev ChoiceG (A B C D : Type) := (Unit → Option A) × (A × B → Option C) × (A × B × C × D → Bool)

/-- The deterministic core of a choice. -/
noncomputable def detCoreG [DecidableEq A] [DecidableEq C] (σ : ChoiceG A B C D) : Core A B C D :=
  ⟨fun a => if σ.1 () = some a then 1 else 0, fun a b c => if σ.2.1 (a, b) = some c then 1 else 0,
    fun a b c d => if σ.2.2 (a, b, c, d) = true then 1 else 0,
    fun a b => by cases h : σ.2.1 (a, b) with
      | none => simp
      | some v => simp [Finset.sum_ite_eq'],
    fun _ _ _ _ => by split_ifs <;> simp⟩

theorem detCoreG_mass [DecidableEq A] [DecidableEq C] (σ : ChoiceG A B C D) :
    (detCoreG σ).mass ≤ 1 := by
  simp only [Core.mass, detCoreG]
  cases h : σ.1 () with
  | none => simp
  | some v => simp [Finset.sum_ite_eq']

theorem core_eq_mixG [DecidableEq A] [DecidableEq C] [Fintype B] [Fintype D] [DecidableEq B]
    [DecidableEq D] (K : Core A B C D) (hK : K.mass ≤ 1) :
    ∃ W : ChoiceG A B C D → ℝ≥0∞, ∑ σ, W σ = 1 ∧
      ∀ a b c d, K.val a b c d = ∑ σ, W σ * (detCoreG σ).val a b c d := by
  classical
  let q1 : Unit → Option A → ℝ≥0∞ := fun _ => compl' K.μ
  let q2 : A × B → Option C → ℝ≥0∞ := fun ab => compl' (K.κ ab.1 ab.2)
  let q3 : A × B × C × D → Bool → ℝ≥0∞ := fun x => bern (K.ρ x.1 x.2.1 x.2.2.1 x.2.2.2)
  have h1 : ∀ i, ∑ k, q1 i k = 1 := fun _ => compl'_sum K.μ hK
  have h2 : ∀ i, ∑ k, q2 i k = 1 := fun ab => compl'_sum _ (K.hκ ab.1 ab.2)
  have h3 : ∀ i, ∑ k, q3 i k = 1 := fun x => bern_sum _ (K.hρ _ _ _ _)
  refine ⟨fun σ => (∏ i, q1 i (σ.1 i)) * (∏ i, q2 i (σ.2.1 i)) * (∏ i, q3 i (σ.2.2 i)), ?_, ?_⟩
  · rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun σ1 _ => Fintype.sum_prod_type _]
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [total q1 h1, total q2 h2, total q3 h3]; simp
  · intro a b c d
    have e1 := marg q1 h1 () (some a)
    have e2 := marg q2 h2 (a, b) (some c)
    have e3 := marg q3 h3 (a, b, c, d) true
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun σ1 _ => Fintype.sum_prod_type _]
    calc K.val a b c d = q1 () (some a) * q2 (a, b) (some c) * q3 (a, b, c, d) true := rfl
      _ = _ := by rw [← e1, ← e2, ← e3]
      _ = _ := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ1 _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ2 _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ3 _ => ?_
          simp only [detCoreG, Core.val]
          ring

/-! ### Mixed = behavioural -/

theorem core_mixG {n : ℕ} (w : Fin n → ℝ≥0∞) (K : Fin n → Core A B C D)
    (hfin : ∀ i a, w i * (K i).μ a ≠ ⊤) :
    ∃ K' : Core A B C D, K'.μ = (fun a => ∑ i, w i * (K i).μ a) ∧
      ∀ a b c d, K'.val a b c d = ∑ i, w i * (K i).val a b c d := by
  let m : A → ℝ≥0∞ := fun a => ∑ i, w i * (K i).μ a
  let nn : A → B → C → ℝ≥0∞ := fun a b c => ∑ i, w i * (K i).μ a * (K i).κ a b c
  let num : A → B → C → D → ℝ≥0∞ :=
    fun a b c d => ∑ i, w i * (K i).μ a * (K i).κ a b c * (K i).ρ a b c d
  have hm_fin : ∀ a, m a ≠ ⊤ := fun a => ENNReal.sum_ne_top.2 fun i _ => hfin i a
  have hnn_le : ∀ a b, ∑ c, nn a b c ≤ m a := by
    intro a b
    simp only [nn, m]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.mul_sum]
    exact (mul_le_mul_left' ((K i).hκ a b) _).trans (by rw [mul_one])
  have hnn_le' : ∀ a b c, nn a b c ≤ m a := fun a b c =>
    (Finset.single_le_sum (f := fun c => nn a b c) (fun _ _ => bot_le) (Finset.mem_univ c)).trans
      (hnn_le a b)
  have hnum_le : ∀ a b c d, num a b c d ≤ nn a b c := fun a b c d =>
    Finset.sum_le_sum fun i _ => (mul_le_mul_left' ((K i).hρ a b c d) _).trans (by rw [mul_one])
  refine ⟨⟨m, fun a b c => nn a b c / m a, fun a b c d => num a b c d / nn a b c, ?_, ?_⟩, rfl, ?_⟩
  · intro a b
    simp only [div_eq_mul_inv]; rw [← Finset.sum_mul, ← div_eq_mul_inv]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hnn_le a b)
  · intro a b c d
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hnum_le a b c d)
  · intro a b c d
    have hrhs : ∑ i, w i * (K i).val a b c d = num a b c d :=
      Finset.sum_congr rfl fun i _ => by simp only [Core.val]; ring
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
      · exact ENNReal.mul_div_cancel hn0 (ne_top_of_le_ne_top (hm_fin a) (hnn_le' a b c))

/-- **Mixtures of randomized sequential programs are randomized sequential programs.** -/
theorem Mix_sequentialG : Mix (sequentialG X Y X' Y') = sequentialG X Y X' Y' := by
  apply le_antisymm
  · rintro _ ⟨n, w, t, ht, hw, rfl⟩
    choose F G hm ht using ht
    have hw1 : ∀ i, w i ≤ 1 := fun i => hw ▸ Finset.single_le_sum (fun _ _ => bot_le)
      (Finset.mem_univ i)
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
        _ = 1 := by simp [hw]
    · funext pq
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eF, eG]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ht i, mul_add]
  · intro t ht
    exact ⟨1, fun _ => 1, fun _ => t, fun _ => ht, by simp, by simp⟩

/-- Normalizing a core by its mass. -/
theorem Core.normalize (K : Core A B C D) (hK : K.mass ≤ 1) :
    ∃ K' : Core A B C D, K'.mass ≤ 1 ∧ ∀ a b c d, K.val a b c d = K.mass * K'.val a b c d := by
  by_cases h0 : K.mass = 0
  · refine ⟨K, hK, fun a b c d => ?_⟩
    have : K.μ a = 0 := le_antisymm (h0 ▸ K.μ_le_mass a) bot_le
    simp [Core.val, this, h0]
  · have hT : K.mass ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hK
    refine ⟨⟨fun a => K.μ a / K.mass, K.κ, K.ρ, K.hκ, K.hρ⟩, ?_, fun a b c d => ?_⟩
    · simp only [Core.mass, div_eq_mul_inv]; rw [← Finset.sum_mul, ← div_eq_mul_inv]
      exact ENNReal.div_self_le_one
    · simp only [Core.val]
      rw [← mul_assoc, ← mul_assoc, ENNReal.mul_div_cancel h0 hT]

/-- The certain sequential programs. -/
def sharpSeqG (X Y X' Y' : Type) [Fintype X] [Fintype X'] : Set ((X × Y) × (X' × Y') → ℝ≥0∞) :=
  {z | z ∈ sequentialG X Y X' Y' ∧ ∀ u, z u = 0 ∨ z u = 1}

theorem zeroCore_mass {A B C D : Type} [Fintype A] [Fintype C] :
    (⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩ : Core A B C D).mass = 0 := by
  simp [Core.mass]

theorem detCoreG_val01 {A B C D : Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
    (σ : ChoiceG A B C D) (a : A) (b : B) (c : C) (d : D) :
    (detCoreG σ).val a b c d = 0 ∨ (detCoreG σ).val a b c d = 1 := by
  simp only [Core.val, detCoreG]; split_ifs <;> simp

/-- An `f`-first core of mass at most `1` is a mixture of certain sequential programs. -/
theorem coreF_mem_Mix (K : Core X Y X' Y') (hK : K.mass ≤ 1) :
    (fun pq : (X × Y) × (X' × Y') => K.val pq.1.1 pq.1.2 pq.2.1 pq.2.2) ∈ Mix (sharpSeqG X Y X' Y') := by
  obtain ⟨Wt, hW, e⟩ := core_eq_mixG K hK
  let z0 : Core X' Y' X Y := ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩
  have hd : ∀ σ, (fun pq : (X × Y) × (X' × Y') => (detCoreG σ).val pq.1.1 pq.1.2 pq.2.1 pq.2.2)
      ∈ sharpSeqG X Y X' Y' := fun σ =>
    ⟨⟨detCoreG σ, z0, by rw [zeroCore_mass, add_zero]; exact detCoreG_mass σ,
      by funext pq; simp [Core.val, z0]⟩, fun pq => detCoreG_val01 σ _ _ _ _⟩
  have : (fun pq : (X × Y) × (X' × Y') => K.val pq.1.1 pq.1.2 pq.2.1 pq.2.2)
      = ∑ σ, Wt σ • (fun pq : (X × Y) × (X' × Y') =>
          (detCoreG σ).val pq.1.1 pq.1.2 pq.2.1 pq.2.2) := by
    funext pq; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; exact e _ _ _ _
  rw [this]; exact mem_Mix_of_fintype Wt _ hd hW

/-- A `g`-first core of mass at most `1` is a mixture of certain sequential programs. -/
theorem coreG_mem_Mix (K : Core X' Y' X Y) (hK : K.mass ≤ 1) :
    (fun pq : (X × Y) × (X' × Y') => K.val pq.2.1 pq.2.2 pq.1.1 pq.1.2) ∈ Mix (sharpSeqG X Y X' Y') := by
  obtain ⟨Wt, hW, e⟩ := core_eq_mixG K hK
  let z0 : Core X Y X' Y' := ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩
  have hd : ∀ σ, (fun pq : (X × Y) × (X' × Y') => (detCoreG σ).val pq.2.1 pq.2.2 pq.1.1 pq.1.2)
      ∈ sharpSeqG X Y X' Y' := fun σ =>
    ⟨⟨z0, detCoreG σ, by rw [zeroCore_mass, zero_add]; exact detCoreG_mass σ,
      by funext pq; simp [Core.val, z0]⟩, fun pq => detCoreG_val01 σ _ _ _ _⟩
  have : (fun pq : (X × Y) × (X' × Y') => K.val pq.2.1 pq.2.2 pq.1.1 pq.1.2)
      = ∑ σ, Wt σ • (fun pq : (X × Y) × (X' × Y') =>
          (detCoreG σ).val pq.2.1 pq.2.2 pq.1.1 pq.1.2) := by
    funext pq; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; exact e _ _ _ _
  rw [this]; exact mem_Mix_of_fintype Wt _ hd hW

/-- **Behavioural = mixed.** Every randomized sequential program is a mixture of deterministic
sequential programs. -/
theorem sequentialG_subset_Mix : sequentialG X Y X' Y' ⊆ Mix (sharpSeqG X Y X' Y') := by
  rintro _ ⟨F, G, hm, rfl⟩
  obtain ⟨F', hF', eF⟩ := F.normalize (le_self_add.trans hm)
  obtain ⟨G', hG', eG⟩ := G.normalize (le_add_self.trans hm)
  have h0 : (0 : (X × Y) × (X' × Y') → ℝ≥0∞) ∈ Mix (sharpSeqG X Y X' Y') := by
    let z0 : Core X Y X' Y' := ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, by simp, by simp⟩
    have := coreF_mem_Mix z0 (by rw [zeroCore_mass]; exact zero_le_one)
    have hz : (fun pq : (X × Y) × (X' × Y') => z0.val pq.1.1 pq.1.2 pq.2.1 pq.2.2) = 0 := by
      funext pq; simp [Core.val, z0]
    rwa [hz] at this
  rw [← Mix_Mix]
  let w : Fin 3 → ℝ≥0∞ := ![F.mass, G.mass, 1 - (F.mass + G.mass)]
  let s : Fin 3 → (X × Y) × (X' × Y') → ℝ≥0∞ :=
    ![fun pq => F'.val pq.1.1 pq.1.2 pq.2.1 pq.2.2, fun pq => G'.val pq.2.1 pq.2.2 pq.1.1 pq.1.2, 0]
  refine ⟨3, w, s, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact coreF_mem_Mix F' hF'
    · exact coreG_mem_Mix G' hG'
    · exact h0
  · simp only [w, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact add_tsub_cancel_of_le hm
  · funext pq
    simp [w, s, Fin.sum_univ_three, eF, eG]

/-- **The recipe is exactly the randomized sequential programs, for all finite data types.** -/
theorem recipe_eq_sequentialG [Nonempty X] [Nonempty X'] :
    Mix {z | z ∈ tD X Y X' Y' ∧ ∀ u, z u = 0 ∨ z u = 1} = sequentialG X Y X' Y' := by
  have hS : {z | z ∈ tD X Y X' Y' ∧ ∀ u, z u = 0 ∨ z u = 1} = sharpSeqG X Y X' Y' := by
    ext z
    exact ⟨fun ⟨hz, h⟩ => ⟨sharp_mem_sequentialG hz h, h⟩,
      fun ⟨hz, h⟩ => ⟨sequentialG_subset_tD hz, h⟩⟩
  rw [hS]
  apply le_antisymm
  · rw [← Mix_sequentialG]
    rintro _ ⟨n, w, s, hs, hw, rfl⟩
    exact ⟨n, w, s, fun i => (hs i).1, hw, rfl⟩
  · calc sequentialG X Y X' Y' ⊆ Mix (sharpSeqG X Y X' Y') := sequentialG_subset_Mix
      _ = _ := rfl

end ConstructiveProb.PCS.General
