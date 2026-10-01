/-
# Sequential randomized strategies cannot reach the pentagon

A program of type `(Bool ⊸ Bool) ⊗ (Bool ⊸ Bool) ⊸ ⊥` in a sequential, linear, probabilistic
language receives two functions `f`, `g` and must query each exactly once. Its arguments are
ground booleans, so its behaviour is a decision tree with coin flips: choose which function to
query first; choose (randomly) its input; on seeing the answer, choose (randomly) the input to the
other function; on seeing that answer, terminate with some probability. Divergence is the missing
mass at every stage. These are the *behavioural strategies* `FFirst`, `GFirst`, and their
denotation on the web `W × W` is the probability of terminating along each pair of answers.

* `FFirst.den_mem`, `GFirst.den_mem`: every such denotation is an element of the PCS `tensDual`.
* `seq_pent_le_two`: every sequential strategy has total weight at most `2` on the pentagon.
* `pentElt_not_sequential`: so the pentagon element (weight `5/2`) is not the denotation of any
  sequential strategy.
* `seq_pent_tight`: the bound `2` is attained by a deterministic strategy.

What is *not* formalized: that every program of the language denotes such a strategy. That step
is the modelling assumption described above.
-/
import ConstructiveProb.PCSMixture

open scoped ENNReal
open Finset

namespace ConstructiveProb.PCS

/-- A behavioural strategy that queries `f` first: input distribution `μ` for `f`, then, having
seen `f a = b`, a distribution `κ a b` over the input to `g`, then, having seen `g c = d`,
termination probability `ρ a b c d`. -/
structure FFirst where
  μ : Bool → ℝ≥0∞
  κ : Bool → Bool → Bool → ℝ≥0∞
  ρ : Bool → Bool → Bool → Bool → ℝ≥0∞
  hμ : μ true + μ false ≤ 1
  hκ : ∀ a b, κ a b true + κ a b false ≤ 1
  hρ : ∀ a b c d, ρ a b c d ≤ 1

/-- The symmetric strategy that queries `g` first. -/
structure GFirst where
  μ : Bool → ℝ≥0∞
  κ : Bool → Bool → Bool → ℝ≥0∞
  ρ : Bool → Bool → Bool → Bool → ℝ≥0∞
  hμ : μ true + μ false ≤ 1
  hκ : ∀ c d, κ c d true + κ c d false ≤ 1
  hρ : ∀ c d a b, ρ c d a b ≤ 1

/-- Termination probability of an `f`-first strategy along `f a = b`, `g c = d`. -/
noncomputable def FFirst.den (S : FFirst) : W × W → ℝ≥0∞ := fun pq =>
  S.μ pq.1.1 * S.κ pq.1.1 pq.1.2 pq.2.1 * S.ρ pq.1.1 pq.1.2 pq.2.1 pq.2.2

/-- Termination probability of a `g`-first strategy along `g c = d`, `f a = b`. -/
noncomputable def GFirst.den (S : GFirst) : W × W → ℝ≥0∞ := fun pq =>
  S.μ pq.2.1 * S.κ pq.2.1 pq.2.2 pq.1.1 * S.ρ pq.2.1 pq.2.2 pq.1.1 pq.1.2

/-- Denotations of sequential strategies: a sub-probabilistic choice of which argument to query
first, followed by a behavioural strategy. -/
def sequential : Set (W × W → ℝ≥0∞) :=
  {t | ∃ (α β : ℝ≥0∞) (F : FFirst) (G : GFirst), α + β ≤ 1 ∧ t = α • F.den + β • G.den}

theorem sum_bool (h : Bool → ℝ≥0∞) : ∑ b, h b = h true + h false := by
  simp [Fintype.sum_bool]

/-! ### Sanity check: the denotations are elements of the PCS -/

/-- The pairing of a deterministic pair with an `f`-first strategy is at most `1`. -/
theorem FFirst.pair_le (S : FFirst) (f g : Bool → Option Bool) :
    ∑ p, ∑ q, det f p * S.den (p, q) * det g q ≤ 1 := by
  classical
  -- bound `ρ` by `1`, then sum over `d`, then over `c`, then over `b`, then over `a`
  have step : ∀ a b : Bool, ∑ q : W, det f (a, b) * S.den ((a, b), q) * det g q
      ≤ det f (a, b) * S.μ a := by
    intro a b
    calc ∑ q : W, det f (a, b) * S.den ((a, b), q) * det g q
        ≤ ∑ q : W, det f (a, b) * S.μ a * (S.κ a b q.1 * det g q) := by
          refine Finset.sum_le_sum fun q _ => ?_
          simp only [FFirst.den]
          calc det f (a, b) * (S.μ a * S.κ a b q.1 * S.ρ a b q.1 q.2) * det g q
              ≤ det f (a, b) * (S.μ a * S.κ a b q.1 * 1) * det g q := by
                gcongr; exact S.hρ _ _ _ _
            _ = _ := by ring
      _ = det f (a, b) * S.μ a * ∑ c, S.κ a b c * ∑ d, det g (c, d) := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type]
          simp [Fintype.sum_bool]; ring
      _ ≤ det f (a, b) * S.μ a * ∑ c, S.κ a b c * 1 := by
          gcongr with c; exact det_row_le_one g c
      _ ≤ det f (a, b) * S.μ a * 1 := by
          gcongr; rw [sum_bool]; simpa using S.hκ a b
      _ = _ := mul_one _
  calc ∑ p, ∑ q, det f p * S.den (p, q) * det g q
      ≤ ∑ p : W, det f p * S.μ p.1 := Finset.sum_le_sum fun p _ => step p.1 p.2
    _ = ∑ a, S.μ a * ∑ b, det f (a, b) := by
        rw [Fintype.sum_prod_type]; simp [Fintype.sum_bool]; ring
    _ ≤ ∑ a, S.μ a * 1 := by gcongr with a; exact det_row_le_one f a
    _ ≤ 1 := by rw [sum_bool]; simpa using S.hμ

/-- The pairing of a deterministic pair with a `g`-first strategy is at most `1`. -/
theorem GFirst.pair_le (S : GFirst) (f g : Bool → Option Bool) :
    ∑ p, ∑ q, det f p * S.den (p, q) * det g q ≤ 1 := by
  classical
  rw [Finset.sum_comm]
  have step : ∀ c d : Bool, ∑ p : W, det f p * S.den (p, (c, d)) * det g (c, d)
      ≤ det g (c, d) * S.μ c := by
    intro c d
    calc ∑ p : W, det f p * S.den (p, (c, d)) * det g (c, d)
        ≤ ∑ p : W, det g (c, d) * S.μ c * (S.κ c d p.1 * det f p) := by
          refine Finset.sum_le_sum fun p _ => ?_
          simp only [GFirst.den]
          calc det f p * (S.μ c * S.κ c d p.1 * S.ρ c d p.1 p.2) * det g (c, d)
              ≤ det f p * (S.μ c * S.κ c d p.1 * 1) * det g (c, d) := by
                gcongr; exact S.hρ _ _ _ _
            _ = _ := by ring
      _ = det g (c, d) * S.μ c * ∑ a, S.κ c d a * ∑ b, det f (a, b) := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type]
          simp [Fintype.sum_bool]; ring
      _ ≤ det g (c, d) * S.μ c * ∑ a, S.κ c d a * 1 := by
          gcongr with a; exact det_row_le_one f a
      _ ≤ det g (c, d) * S.μ c * 1 := by
          gcongr; rw [sum_bool]; simpa using S.hκ c d
      _ = _ := mul_one _
  calc ∑ q, ∑ p, det f p * S.den (p, q) * det g q
      ≤ ∑ q : W, det g q * S.μ q.1 := Finset.sum_le_sum fun q _ => step q.1 q.2
    _ = ∑ c, S.μ c * ∑ d, det g (c, d) := by
        rw [Fintype.sum_prod_type]; simp [Fintype.sum_bool]; ring
    _ ≤ ∑ c, S.μ c * 1 := by gcongr with c; exact det_row_le_one g c
    _ ≤ 1 := by rw [sum_bool]; simpa using S.hμ

theorem FFirst.den_mem (S : FFirst) : S.den ∈ tensDual :=
  mem_tensDual_of_det _ S.pair_le

theorem GFirst.den_mem (S : GFirst) : S.den ∈ tensDual :=
  mem_tensDual_of_det _ S.pair_le

/-! ### The pentagon bound -/

theorem sum_pent (t : W × W → ℝ≥0∞) : ∑ pq ∈ pent, t pq =
    t ((true, true), (true, true)) + (t ((true, false), (false, false)) +
    (t ((false, true), (true, false)) + (t ((false, true), (false, true)) +
    t ((false, false), (false, false))))) := by
  simp [pent]

/-- An `f`-first strategy puts weight at most `2` on the pentagon. Along `f true`, the two
pentagon points read different answers `b`, so they use different rows of `κ`; along
`f false`, two of the three points share the row `κ false true`. -/
theorem FFirst.pent_le_two (S : FFirst) : ∑ pq ∈ pent, S.den pq ≤ 2 := by
  rw [sum_pent]
  simp only [FFirst.den]
  have r := S.hρ
  have k1 := S.hκ false true
  calc S.μ true * S.κ true true true * S.ρ true true true true +
        (S.μ true * S.κ true false false * S.ρ true false false false +
        (S.μ false * S.κ false true true * S.ρ false true true false +
        (S.μ false * S.κ false true false * S.ρ false true false true +
        S.μ false * S.κ false false false * S.ρ false false false false)))
      ≤ S.μ true * 1 * 1 + (S.μ true * 1 * 1 + (S.μ false * S.κ false true true * 1 +
        (S.μ false * S.κ false true false * 1 + S.μ false * 1 * 1))) := by
        gcongr
        all_goals first
          | exact r _ _ _ _
          | exact le_self_add.trans (S.hκ _ _)
          | exact le_add_self.trans (S.hκ _ _)
    _ = 2 * S.μ true + S.μ false * (S.κ false true true + S.κ false true false) + S.μ false := by
        ring
    _ ≤ 2 * S.μ true + S.μ false * 1 + S.μ false := by gcongr
    _ = 2 * (S.μ true + S.μ false) := by ring
    _ ≤ 2 * 1 := by gcongr; exact S.hμ
    _ = 2 := mul_one _

/-- A `g`-first strategy puts weight at most `2` on the pentagon. -/
theorem GFirst.pent_le_two (S : GFirst) : ∑ pq ∈ pent, S.den pq ≤ 2 := by
  rw [sum_pent]
  simp only [GFirst.den]
  have r := S.hρ
  have k1 := S.hκ false false
  calc S.μ true * S.κ true true true * S.ρ true true true true +
        (S.μ false * S.κ false false true * S.ρ false false true false +
        (S.μ true * S.κ true false false * S.ρ true false false true +
        (S.μ false * S.κ false true false * S.ρ false true false true +
        S.μ false * S.κ false false false * S.ρ false false false false)))
      ≤ S.μ true * 1 * 1 + (S.μ false * S.κ false false true * 1 +
        (S.μ true * 1 * 1 + (S.μ false * 1 * 1 + S.μ false * S.κ false false false * 1))) := by
        gcongr
        all_goals first
          | exact r _ _ _ _
          | exact le_self_add.trans (S.hκ _ _)
          | exact le_add_self.trans (S.hκ _ _)
    _ = 2 * S.μ true + S.μ false * (S.κ false false true + S.κ false false false) + S.μ false := by
        ring
    _ ≤ 2 * S.μ true + S.μ false * 1 + S.μ false := by gcongr
    _ = 2 * (S.μ true + S.μ false) := by ring
    _ ≤ 2 * 1 := by gcongr; exact S.hμ
    _ = 2 := mul_one _

/-- **Every sequential strategy puts weight at most `2` on the pentagon.** -/
theorem seq_pent_le_two {t : W × W → ℝ≥0∞} (ht : t ∈ sequential) : ∑ pq ∈ pent, t pq ≤ 2 := by
  obtain ⟨α, β, F, G, hαβ, rfl⟩ := ht
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  calc α * ∑ pq ∈ pent, F.den pq + β * ∑ pq ∈ pent, G.den pq ≤ α * 2 + β * 2 := by
        gcongr
        · exact F.pent_le_two
        · exact G.pent_le_two
    _ = (α + β) * 2 := by ring
    _ ≤ 1 * 2 := by gcongr
    _ = 2 := one_mul _

/-- **The pentagon is not the denotation of any sequential strategy.** -/
theorem pentElt_not_sequential : pentElt ∉ sequential := by
  intro h
  have hle := seq_pent_le_two h
  have h2 : ∀ pq ∈ pent, pentElt pq = 2⁻¹ := fun pq hpq => if_pos hpq
  have hc : pent.card = 5 := by decide
  rw [Finset.sum_congr rfl h2, Finset.sum_const, hc, nsmul_eq_mul] at hle
  have : (5 : ℝ≥0∞) * 2⁻¹ = 5 / 2 := (div_eq_mul_inv _ _).symm
  rw [Nat.cast_ofNat, this, ENNReal.div_le_iff two_ne_zero ENNReal.ofNat_ne_top] at hle
  norm_num at hle

/-- The deterministic strategy "query `f` at `true`, query `g` at the answer, terminate when `g`
returns the same answer". -/
noncomputable def copyStrategy : FFirst where
  μ a := if a then 1 else 0
  κ _ b c := if c = b then 1 else 0
  ρ _ b _ d := if d = b then 1 else 0
  hμ := by simp
  hκ a b := by cases b <;> simp
  hρ a b c d := by split_ifs <;> simp

/-- The strategy that queries `g` first and always diverges. -/
def idleG : GFirst where
  μ _ := 0
  κ _ _ _ := 0
  ρ _ _ _ _ := 0
  hμ := by simp
  hκ _ _ := by simp
  hρ _ _ _ _ := by simp

/-- **The bound `2` is tight**: `copyStrategy` reaches it. -/
theorem seq_pent_tight : ∃ t ∈ sequential, ∑ pq ∈ pent, t pq = 2 := by
  refine ⟨copyStrategy.den, ⟨1, 0, copyStrategy, idleG, by simp, ?_⟩, ?_⟩
  · funext pq; simp
  · rw [sum_pent]; simp [FFirst.den, copyStrategy]; norm_num

/-! ### The certain elements of the PCS are exactly the deterministic sequential strategies -/

/-- The strategy that queries `f` first and always diverges. -/
def idleF : FFirst where
  μ _ := 0
  κ _ _ _ := 0
  ρ _ _ _ _ := 0
  hμ := by simp
  hκ _ _ := by simp
  hρ _ _ _ _ := by simp

/-- Every sequential denotation is an element of the PCS. -/
theorem sequential_subset_tensDual : sequential ⊆ tensDual := by
  rintro _ ⟨α, β, F, G, hαβ, rfl⟩
  refine mem_tensDual_of_det _ fun f g => ?_
  have hF := F.pair_le f g
  have hG := G.pair_le f g
  calc ∑ p, ∑ q, det f p * (α • F.den + β • G.den) (p, q) * det g q
      = α * ∑ p, ∑ q, det f p * F.den (p, q) * det g q
        + β * ∑ p, ∑ q, det f p * G.den (p, q) * det g q := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    _ ≤ α * 1 + β * 1 := by gcongr
    _ ≤ 1 := by simpa using hαβ

/-- Two distinct support points of a certain element of the PCS lie in no common
deterministic pair. -/
theorem sharp_excl {z : W × W → ℝ≥0∞} (hz : z ∈ tensDual) {s t : W × W} (hs : z s = 1)
    (ht : z t = 1) (hne : s ≠ t) : ¬ compat2 s t := by
  intro hc
  obtain ⟨f, g, hfs, hft⟩ := covers_of_compat2 hc
  have h1 := hz _ (det_mem_lin f) _ (det_mem_lin g)
  rw [pair_det] at h1
  have h2 : z s + z t ≤ ∑ pq ∈ univ.filter (covers f g), z pq := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hfs, hft])
  rw [hs, ht] at h2
  have := h2.trans h1
  norm_num at this

theorem not_compat2 {s t : W × W} (h : ¬ compat2 s t) :
    (s.1.1 = t.1.1 ∧ s.1 ≠ t.1) ∨ (s.2.1 = t.2.1 ∧ s.2 ≠ t.2) := by
  simp only [compat2, compat, not_and_or, not_or, ne_eq, not_not] at h
  tauto

/-- In a certain element, either all `f`-inputs agree or all `g`-inputs agree. -/
theorem sharp_one_side {z : W × W → ℝ≥0∞} (hz : z ∈ tensDual) :
    (∀ s t, z s = 1 → z t = 1 → s.1.1 = t.1.1) ∨ (∀ s t, z s = 1 → z t = 1 → s.2.1 = t.2.1) := by
  by_contra hcon
  simp only [not_or, not_forall] at hcon
  obtain ⟨⟨s, t, hs, ht, hst⟩, ⟨u, v, hu, hv, huv⟩⟩ := hcon
  -- `s, t` differ on the `f`-input, so they share the `g`-input
  have hsg : s.2.1 = t.2.1 := by
    rcases not_compat2 (sharp_excl hz hs ht (fun h => hst (by rw [h]))) with h | h
    · exact absurd h.1 hst
    · exact h.1
  -- `u, v` differ on the `g`-input, so they share the `f`-input
  have huf : u.1.1 = v.1.1 := by
    rcases not_compat2 (sharp_excl hz hu hv (fun h => huv (by rw [h]))) with h | h
    · exact h.1
    · exact absurd h.1 huv
  have pick : ∀ x y w : Bool, x ≠ y → x ≠ w ∨ y ≠ w := by decide
  -- a point of `{s, t}` and a point of `{u, v}` differing on both inputs
  obtain ⟨s', hs', hs'f, hs'g⟩ : ∃ s', z s' = 1 ∧ s'.1.1 ≠ u.1.1 ∧ s'.2.1 = s.2.1 := by
    rcases pick _ _ u.1.1 hst with h | h
    · exact ⟨s, hs, h, rfl⟩
    · exact ⟨t, ht, h, hsg.symm⟩
  obtain ⟨u', hu', hu'f, hu'g⟩ : ∃ u', z u' = 1 ∧ u'.1.1 = u.1.1 ∧ u'.2.1 ≠ s.2.1 := by
    rcases pick _ _ s.2.1 huv with h | h
    · exact ⟨u, hu, rfl, h⟩
    · exact ⟨v, hv, huf.symm, h⟩
  have hne : s' ≠ u' := fun h => hs'f (by rw [h, hu'f])
  rcases not_compat2 (sharp_excl hz hs' hu' hne) with h | h
  · exact hs'f (h.1.trans hu'f)
  · exact hu'g (h.1.symm.trans hs'g)

/-- **Every certain element of the PCS is a deterministic sequential strategy.** -/
theorem sharp_mem_sequential {z : W × W → ℝ≥0∞} (hz : z ∈ tensDual)
    (h01 : ∀ pq, z pq = 0 ∨ z pq = 1) : z ∈ sequential := by
  classical
  have hρ : ∀ pq, z pq ≤ 1 := fun pq => by rcases h01 pq with h | h <;> simp [h]
  by_cases hne : ∃ s, z s = 1
  swap
  · push_neg at hne
    refine ⟨0, 0, idleF, idleG, by simp, ?_⟩
    funext pq; rcases h01 pq with h | h
    · simp [h]
    · exact absurd h (hne pq)
  obtain ⟨s0, hs0⟩ := hne
  rcases sharp_one_side hz with hA | hB
  · -- `f`-first: query `f` at `a`; on answer `b`, query `g` at `cf b`
    let cf : Bool → Bool := fun b =>
      if h : ∃ t, z t = 1 ∧ t.1.2 = b then (Classical.choose h).2.1 else true
    have hcf : ∀ p, z p = 1 → cf p.1.2 = p.2.1 := by
      intro p hp
      have hex : ∃ t, z t = 1 ∧ t.1.2 = p.1.2 := ⟨p, hp, rfl⟩
      simp only [cf, dif_pos hex]
      obtain ⟨ht, htb⟩ := Classical.choose_spec hex
      set t := Classical.choose hex
      have h1 : t.1 = p.1 := Prod.ext (hA t p ht hp) htb
      by_cases htp : t = p
      · rw [htp]
      · rcases not_compat2 (sharp_excl hz ht hp htp) with h | h
        · exact absurd h1 h.2
        · exact h.1
    let F : FFirst := ⟨fun a => if a = s0.1.1 then 1 else 0,
      fun _ b c => if c = cf b then 1 else 0, fun a b c d => z ((a, b), (c, d)),
      by cases s0.1.1 <;> simp, fun _ b => by cases cf b <;> simp, fun _ _ _ _ => hρ _⟩
    refine ⟨1, 0, F, idleG, by simp, ?_⟩
    funext pq
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, zero_mul, add_zero,
      FFirst.den, F]
    rcases h01 pq with h | h
    · simp [h]
    · rw [if_pos (hA pq s0 h hs0), if_pos (hcf pq h).symm]; simp
  · -- `g`-first: query `g` at `c`; on answer `d`, query `f` at `af d`
    let af : Bool → Bool := fun d =>
      if h : ∃ t, z t = 1 ∧ t.2.2 = d then (Classical.choose h).1.1 else true
    have haf : ∀ p, z p = 1 → af p.2.2 = p.1.1 := by
      intro p hp
      have hex : ∃ t, z t = 1 ∧ t.2.2 = p.2.2 := ⟨p, hp, rfl⟩
      simp only [af, dif_pos hex]
      obtain ⟨ht, htd⟩ := Classical.choose_spec hex
      set t := Classical.choose hex
      have h1 : t.2 = p.2 := Prod.ext (hB t p ht hp) htd
      by_cases htp : t = p
      · rw [htp]
      · rcases not_compat2 (sharp_excl hz ht hp htp) with h | h
        · exact h.1
        · exact absurd h1 h.2
    let G : GFirst := ⟨fun c => if c = s0.2.1 then 1 else 0,
      fun _ d a => if a = af d then 1 else 0, fun c d a b => z ((a, b), (c, d)),
      by cases s0.2.1 <;> simp, fun _ d => by cases af d <;> simp, fun _ _ _ _ => hρ _⟩
    refine ⟨0, 1, idleF, G, by simp, ?_⟩
    funext pq
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, zero_mul, zero_add,
      GFirst.den, G]
    rcases h01 pq with h | h
    · simp [h]
    · rw [if_pos (hB pq s0 h hs0), if_pos (haf pq h).symm]; simp

/-- **The certain elements of the PCS are exactly the certain sequential denotations.** -/
theorem sharp_tensDual_eq_sharp_sequential :
    {z | z ∈ tensDual ∧ ∀ pq, z pq = 0 ∨ z pq = 1}
      = {z | z ∈ sequential ∧ ∀ pq, z pq = 0 ∨ z pq = 1} := by
  ext z
  exact ⟨fun ⟨hz, h⟩ => ⟨sharp_mem_sequential hz h, h⟩,
    fun ⟨hz, h⟩ => ⟨sequential_subset_tensDual hz, h⟩⟩

end ConstructiveProb.PCS
