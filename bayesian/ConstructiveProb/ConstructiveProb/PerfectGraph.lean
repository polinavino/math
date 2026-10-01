/-
# The perfect-graph criterion, necessary direction

For a finite graph `G`, `STAB G` is the set of mixtures of indicators of stable sets and `QSTAB G`
the set of weightings with total at most `1` on every clique. Always `STAB ⊆ QSTAB`
(`stab_subset_qstab`). An induced odd hole or odd antihole of length `2k+1 ≥ 5` separates them
(`oddHole_gap`, `oddAntihole_gap`), so `STAB G = QSTAB G` forces `G` to be Berge
(`berge_of_stab_eq_qstab`). The converse, Berge ⟹ `STAB = QSTAB`, is the strong perfect graph
theorem (Chudnovsky–Robertson–Seymour–Thomas) together with Lovász–Chvátal; it is not formalized.

For the second-order PCS `T`, `T = QSTAB` and recipe `= STAB` of its exclusivity graph
(`General.tD_iff_qstab`, `recipe_eq_stab`), so the recipe agrees with the PCS only if that graph
is Berge.
-/
import ConstructiveProb.Recipe

open scoped ENNReal
open Finset

namespace ConstructiveProb.Graph

/-! ### Cycles -/

/-- Adjacency in the cycle `ZMod n`. -/
def cyc {n : ℕ} (i j : ZMod n) : Prop := j = i + 1 ∨ i = j + 1

theorem small_ne {n : ℕ} (hn : 4 ≤ n) {m : ℕ} (hm0 : 0 < m) (hm : m < n) : (m : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h; exact absurd (Nat.le_of_dvd hm0 h) (by omega)

/-- A clique of a cycle of length at least `4` has at most two vertices. -/
theorem cyc_clique_le_two {n : ℕ} [NeZero n] (hn : 4 ≤ n) (S : Finset (ZMod n))
    (hS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → cyc i j) : S.card ≤ 2 := by
  by_contra hc
  obtain ⟨a, b, c, ha, hb, hc', hab', hac', hbc'⟩ := Finset.two_lt_card_iff.1 (by omega : 2 < S.card)
  have z1 : ((1 : ℕ) : ZMod n) ≠ 0 := small_ne hn (by norm_num) (by omega)
  have z2 : ((2 : ℕ) : ZMod n) ≠ 0 := small_ne hn (by norm_num) (by omega)
  have z3 : ((3 : ℕ) : ZMod n) ≠ 0 := small_ne hn (by norm_num) (by omega)
  push_cast at z1 z2 z3
  rcases hS a ha b hb hab' with h1 | h1 <;> rcases hS a ha c hc' hac' with h2 | h2 <;>
    rcases hS b hb c hc' hbc' with h3 | h3 <;>
    first
    | exact hbc' (by linear_combination h1 - h2)
    | exact hbc' (by linear_combination h2 - h1)
    | exact z3 (by linear_combination -(h1 + h2 + h3))
    | exact z1 (by linear_combination h3 - h1 - h2)

/-- An independent set of the cycle `ZMod n` has at most `n / 2` vertices. -/
theorem cyc_indep_card {n : ℕ} [NeZero n] (I : Finset (ZMod n))
    (hI : ∀ i ∈ I, ∀ j ∈ I, ¬ cyc i j) : 2 * I.card ≤ n := by
  have hdisj : Disjoint I (I.image (· + 1)) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj'
    exact hI i hi _ hj (Or.inl rfl)
  have hcard : (I.image (· + 1)).card = I.card :=
    Finset.card_image_of_injective _ (add_left_injective 1)
  have := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ (I ∪ I.image (· + 1))
  rw [ZMod.card] at hle
  omega

/-! ### Stable-set and clique polytopes -/

variable {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop)

def IsCliqueG (C : Finset V) : Prop := ∀ u ∈ C, ∀ v ∈ C, u ≠ v → adj u v

def IsStableG (I : Finset V) : Prop := ∀ u ∈ I, ∀ v ∈ I, ¬ adj u v

noncomputable def ind (I : Finset V) : V → ℝ≥0∞ := fun v => if v ∈ I then 1 else 0

/-- The clique-constrained polytope. -/
def QSTAB : Set (V → ℝ≥0∞) := {x | ∀ C, IsCliqueG adj C → ∑ v ∈ C, x v ≤ 1}

/-- The stable-set polytope: mixtures of indicators of stable sets. -/
def STAB : Set (V → ℝ≥0∞) := Mix {x | ∃ I, IsStableG adj I ∧ x = ind I}

variable {adj}

theorem sum_ind (I C : Finset V) : ∑ v ∈ C, ind I v = ((C ∩ I).card : ℝ≥0∞) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_filter_add_sum_filter_not C (· ∈ I)]
  simp only [ind]
  rw [Finset.sum_congr rfl (fun v hv => if_pos (Finset.mem_filter.1 hv).2),
    Finset.sum_congr rfl (fun v hv => if_neg (Finset.mem_filter.1 hv).2)]
  simp [Finset.filter_mem_eq_inter]

/-- The mixture bound: a linear functional bounded on the stable sets is bounded on `STAB`. -/
theorem stab_sum_le {x : V → ℝ≥0∞} (hx : x ∈ STAB adj) (C : Finset V) (k : ℝ≥0∞)
    (h : ∀ I, IsStableG adj I → ((C ∩ I).card : ℝ≥0∞) ≤ k) : ∑ v ∈ C, x v ≤ k := by
  obtain ⟨n, w, s, hs, hw, rfl⟩ := hx
  choose I hI hsI using hs
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  calc ∑ i, ∑ v ∈ C, w i * s i v = ∑ i, w i * ∑ v ∈ C, s i v := by simp [Finset.mul_sum]
    _ ≤ ∑ i, w i * k := Finset.sum_le_sum fun i _ => mul_le_mul_left' (by
        rw [hsI i, sum_ind]; exact h _ (hI i)) _
    _ = k := by rw [← Finset.sum_mul, hw, one_mul]

theorem stab_subset_qstab : STAB adj ⊆ QSTAB adj := by
  intro x hx C hC
  refine stab_sum_le hx C 1 fun I hI => ?_
  have : (C ∩ I).card ≤ 1 := Finset.card_le_one.2 fun u hu v hv => by
    by_contra hne
    exact hI u (Finset.mem_inter.1 hu).2 v (Finset.mem_inter.1 hv).2
      (hC u (Finset.mem_inter.1 hu).1 v (Finset.mem_inter.1 hv).1 hne)
  exact_mod_cast this

/-! ### Odd holes and antiholes -/

/-- An induced cycle of length `n` in `G`. -/
structure Hole (adj : V → V → Prop) (n : ℕ) where
  h : ZMod n → V
  inj : Function.Injective h
  adj_iff : ∀ i j, i ≠ j → (adj (h i) (h j) ↔ cyc i j)

/-- An induced complement of a cycle of length `n` in `G`. -/
structure Antihole (adj : V → V → Prop) (n : ℕ) where
  h : ZMod n → V
  inj : Function.Injective h
  adj_iff : ∀ i j, i ≠ j → (adj (h i) (h j) ↔ ¬ cyc i j)

theorem card_preimage {n : ℕ} [NeZero n] {h : ZMod n → V} (hinj : Function.Injective h)
    (C : Finset V) :
    (C ∩ Finset.univ.image h).card = (Finset.univ.filter (fun i => h i ∈ C)).card := by
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext v
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨hv, i, rfl⟩; exact ⟨i, hv, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨hi, i, rfl⟩

/-- **An odd hole separates `STAB` from `QSTAB`.** -/
theorem oddHole_gap {k : ℕ} (hk : 2 ≤ k) [NeZero (2 * k + 1)] (H : Hole adj (2 * k + 1)) :
    STAB adj ≠ QSTAB adj := by
  intro heq
  set n := 2 * k + 1
  let C := Finset.univ.image H.h
  let x : V → ℝ≥0∞ := fun v => if v ∈ C then 2⁻¹ else 0
  have hxq : x ∈ QSTAB adj := by
    intro D hD
    have hS : (Finset.univ.filter (fun i => H.h i ∈ D)).card ≤ 2 :=
      cyc_clique_le_two (by omega) _ fun i hi j hj hij =>
        (H.adj_iff i j hij).1 (hD _ (Finset.mem_filter.1 hi).2 _ (Finset.mem_filter.1 hj).2
          (fun e => hij (H.inj e)))
    calc ∑ v ∈ D, x v = ∑ v ∈ D ∩ C, (2⁻¹ : ℝ≥0∞) := by
          rw [← Finset.sum_filter_add_sum_filter_not D (· ∈ C)]
          simp only [x]
          rw [Finset.sum_congr rfl (fun v hv => if_pos (Finset.mem_filter.1 hv).2),
            Finset.sum_congr rfl (fun v hv => if_neg (Finset.mem_filter.1 hv).2)]
          simp [Finset.filter_mem_eq_inter]
      _ = (D ∩ C).card * 2⁻¹ := by simp
      _ ≤ 2 * 2⁻¹ := by
          gcongr; rw [card_preimage H.inj]; exact_mod_cast hS
      _ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hxs := heq ▸ hxq
  have z1 : (1 : ZMod n) ≠ 0 := by
    have := small_ne (n := n) (by omega) (m := 1) (by norm_num) (by omega); simpa using this
  have hb := stab_sum_le hxs C k fun I hI => by
    rw [Finset.inter_comm, card_preimage H.inj]
    have := cyc_indep_card (Finset.univ.filter (fun i => H.h i ∈ I)) fun i hi j hj hc => by
      by_cases hij : i = j
      · subst hij
        rcases hc with h | h
        · exact z1 (by linear_combination -h)
        · exact z1 (by linear_combination -h)
      · exact hI _ (Finset.mem_filter.1 hi).2 _ (Finset.mem_filter.1 hj).2
          ((H.adj_iff i j hij).2 hc)
    exact_mod_cast (by omega : (Finset.univ.filter (fun i => H.h i ∈ I)).card ≤ k)
  have hsum : ∑ v ∈ C, x v = (n : ℝ≥0∞) * 2⁻¹ := by
    rw [Finset.sum_congr rfl fun v hv => (if_pos hv : x v = 2⁻¹), Finset.sum_const,
      Finset.card_image_of_injective _ H.inj, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [hsum] at hb
  have := mul_le_mul_right' hb 2
  rw [mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one] at this
  have : (n : ℝ≥0∞) ≤ ((k * 2 : ℕ) : ℝ≥0∞) := by exact_mod_cast this
  have := (Nat.cast_le (α := ℝ≥0∞)).1 this
  omega

/-- **An odd antihole separates `STAB` from `QSTAB`.** -/
theorem oddAntihole_gap {k : ℕ} (hk : 2 ≤ k) [NeZero (2 * k + 1)] (H : Antihole adj (2 * k + 1)) :
    STAB adj ≠ QSTAB adj := by
  intro heq
  set n := 2 * k + 1
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hkt : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
  have z1 : (1 : ZMod n) ≠ 0 := by
    have := small_ne (n := n) (by omega) (m := 1) (by norm_num) (by omega); simpa using this
  let C := Finset.univ.image H.h
  let x : V → ℝ≥0∞ := fun v => if v ∈ C then (k : ℝ≥0∞)⁻¹ else 0
  have hxq : x ∈ QSTAB adj := by
    intro D hD
    have hS := cyc_indep_card (Finset.univ.filter (fun i => H.h i ∈ D)) fun i hi j hj hc => by
      by_cases hij : i = j
      · subst hij
        rcases hc with h | h
        · exact z1 (by linear_combination -h)
        · exact z1 (by linear_combination -h)
      · exact ((H.adj_iff i j hij).1 (hD _ (Finset.mem_filter.1 hi).2 _ (Finset.mem_filter.1 hj).2
          (fun e => hij (H.inj e)))) hc
    calc ∑ v ∈ D, x v = ∑ v ∈ D ∩ C, (k : ℝ≥0∞)⁻¹ := by
          rw [← Finset.sum_filter_add_sum_filter_not D (· ∈ C)]
          simp only [x]
          rw [Finset.sum_congr rfl (fun v hv => if_pos (Finset.mem_filter.1 hv).2),
            Finset.sum_congr rfl (fun v hv => if_neg (Finset.mem_filter.1 hv).2)]
          simp [Finset.filter_mem_eq_inter]
      _ = (D ∩ C).card * (k : ℝ≥0∞)⁻¹ := by simp
      _ ≤ k * (k : ℝ≥0∞)⁻¹ := by
          gcongr; rw [card_preimage H.inj]; exact_mod_cast (by omega)
      _ = 1 := ENNReal.mul_inv_cancel hk0 hkt
  have hxs := heq ▸ hxq
  have hb := stab_sum_le hxs C 2 fun I hI => by
    rw [Finset.inter_comm, card_preimage H.inj]
    have := cyc_clique_le_two (by omega) (Finset.univ.filter (fun i => H.h i ∈ I))
      fun i hi j hj hij => by
        by_contra hc
        exact hI _ (Finset.mem_filter.1 hi).2 _ (Finset.mem_filter.1 hj).2
          ((H.adj_iff i j hij).2 hc)
    exact_mod_cast this
  have hsum : ∑ v ∈ C, x v = (n : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ := by
    rw [Finset.sum_congr rfl fun v hv => (if_pos hv : x v = (k : ℝ≥0∞)⁻¹), Finset.sum_const,
      Finset.card_image_of_injective _ H.inj, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [hsum] at hb
  have := mul_le_mul_right' hb k
  rw [mul_assoc, ENNReal.inv_mul_cancel hk0 hkt, mul_one] at this
  have : (n : ℝ≥0∞) ≤ ((2 * k : ℕ) : ℝ≥0∞) := by exact_mod_cast this
  have := (Nat.cast_le (α := ℝ≥0∞)).1 this
  omega

/-- **The perfect-graph criterion, necessary direction.** If the stable-set polytope equals the
clique-constrained polytope, the graph has no induced odd hole and no induced odd antihole of
length at least `5`: it is Berge. -/
theorem berge_of_stab_eq_qstab (heq : STAB adj = QSTAB adj) (k : ℕ) (hk : 2 ≤ k)
    [NeZero (2 * k + 1)] : IsEmpty (Hole adj (2 * k + 1)) ∧ IsEmpty (Antihole adj (2 * k + 1)) :=
  ⟨⟨fun H => oddHole_gap hk H heq⟩, ⟨fun H => oddAntihole_gap hk H heq⟩⟩

end ConstructiveProb.Graph
