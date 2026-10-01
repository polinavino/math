/-
# Second order over arbitrary finite data types

For finite data types `X, Y, X', Y'`, the PCS `T = ((X ⊸ Y) ⊗ (X' ⊸ Y'))^⊥` (`tD`) is a program
that receives `f : X ⊸ Y` and `g : X' ⊸ Y'` and may halt. Everything proved for `Bool` holds in
general:

* `tD_iff_qstab`: `T` is `QSTAB` of its exclusivity graph (total weight at most `1` on every
  pairwise-compatible set of web points);
* `sharp_tD_iff`: the certain (`{0,1}`-valued) elements of `T` are exactly the deterministic
  sequential strategies, i.e. the support is the tree of an `f`-first strategy (query `f` at `a`,
  then `g` at `cf b` on answer `b`) or of a `g`-first one.
-/
import ConstructiveProb.PCSMixture

open scoped ENNReal
open Finset

namespace ConstructiveProb.PCS.General

variable {X Y X' Y' : Type} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
  [DecidableEq X] [DecidableEq Y] [DecidableEq X'] [DecidableEq Y']

/-- The PCS `((X ⊸ Y) ⊗ (X' ⊸ Y'))^⊥`. -/
def tD (X Y X' Y' : Type) [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y'] :
    Set ((X × Y) × (X' × Y') → ℝ≥0∞) :=
  {t | ∀ y ∈ lin X Y, ∀ z ∈ lin X' Y', ∑ p, ∑ q, y p * t (p, q) * z q ≤ 1}

/-- `(f, g)` covers `(p, q)`. -/
def cov (f : X → Option Y) (g : X' → Option Y') (pq : (X × Y) × (X' × Y')) : Prop :=
  f pq.1.1 = some pq.1.2 ∧ g pq.2.1 = some pq.2.2

instance (f : X → Option Y) (g : X' → Option Y') : DecidablePred (cov f g) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Two points of `X ⊸ Y` lie in a common deterministic program. -/
def cp {X Y : Type} (p q : X × Y) : Prop := p = q ∨ p.1 ≠ q.1

/-- Two web points of `T` lie in a common deterministic pair. -/
def cp2 (s t : (X × Y) × (X' × Y')) : Prop := cp s.1 t.1 ∧ cp s.2 t.2

theorem det_mem_lin' (f : X → Option Y) : det f ∈ lin X Y :=
  (mem_lin_iff _).2 (det_row_le_one f)

theorem pair_det' (f : X → Option Y) (g : X' → Option Y') (t : (X × Y) × (X' × Y') → ℝ≥0∞) :
    ∑ p, ∑ q, det f p * t (p, q) * det g q = ∑ pq ∈ univ.filter (cov f g), t pq := by
  classical
  rw [← Fintype.sum_prod_type', Finset.sum_filter]
  refine Finset.sum_congr rfl fun pq _ => ?_
  unfold det cov
  by_cases h1 : f pq.1.1 = some pq.1.2 <;> by_cases h2 : g pq.2.1 = some pq.2.2 <;>
    simp [h1, h2]

theorem mem_tD_of_det (t : (X × Y) × (X' × Y') → ℝ≥0∞)
    (h : ∀ f g, ∑ pq ∈ univ.filter (cov f g), t pq ≤ 1) : t ∈ tD X Y X' Y' := by
  intro y hy z hz
  obtain ⟨u, hu, rfl⟩ := (mem_lin_iff_mix y).1 hy
  obtain ⟨v, hv, rfl⟩ := (mem_lin_iff_mix z).1 hz
  have hexp : ∑ p, ∑ q, (∑ f, u f • det f) p * t (p, q) * (∑ g, v g • det g) q
      = ∑ f, ∑ g, u f * v g * ∑ p, ∑ q, det f p * t (p, q) * det g q := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => enter [2, p, 2, q]; rw [Finset.sum_comm]
    conv_lhs => enter [2, p]; rw [Finset.sum_comm]
    conv_lhs => enter [2, p, 2, f]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => enter [2, f]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ =>
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [hexp]
  calc ∑ f, ∑ g, u f * v g * ∑ p, ∑ q, det f p * t (p, q) * det g q
      ≤ ∑ f, ∑ g, u f * v g * 1 := Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun g _ =>
        mul_le_mul_left' (by rw [pair_det']; exact h f g) _
    _ = 1 := by simp [← Finset.mul_sum, hu, hv]

theorem cp_of_some {X Y : Type} {f : X → Option Y} {p q : X × Y} (hp : f p.1 = some p.2)
    (hq : f q.1 = some q.2) : cp p q := by
  by_cases h : p.1 = q.1
  · left; rw [h] at hp; exact Prod.ext h (Option.some_injective _ (hp.symm.trans hq))
  · exact Or.inr h

theorem cp2_of_cov {f : X → Option Y} {g : X' → Option Y'} {s t : (X × Y) × (X' × Y')} (hs : cov f g s)
    (ht : cov f g t) : cp2 s t :=
  ⟨cp_of_some hs.1 ht.1, cp_of_some hs.2 ht.2⟩

/-- A deterministic program through every point of a pairwise-compatible family. -/
noncomputable def thru {X Y : Type} [DecidableEq X] (C : Finset (X × Y)) : X → Option Y :=
  fun a => if h : ∃ p ∈ C, p.1 = a then some (Classical.choose h).2 else none

theorem thru_spec {X Y : Type} [DecidableEq X] {C : Finset (X × Y)}
    (hC : ∀ p ∈ C, ∀ q ∈ C, cp p q) {p : X × Y} (hp : p ∈ C) : thru C p.1 = some p.2 := by
  have hex : ∃ q ∈ C, q.1 = p.1 := ⟨p, hp, rfl⟩
  simp only [thru, dif_pos hex]
  obtain ⟨hq, hq1⟩ := Classical.choose_spec hex
  rcases hC _ hq p hp with h | h
  · rw [h]
  · exact absurd hq1 h

theorem cov_of_pairwise {C : Finset ((X × Y) × (X' × Y'))} (hC : ∀ s ∈ C, ∀ t ∈ C, cp2 s t) :
    ∃ f g, ∀ s ∈ C, cov f g s := by
  refine ⟨thru (C.image Prod.fst), thru (C.image Prod.snd), fun s hs => ⟨?_, ?_⟩⟩
  · refine thru_spec ?_ (Finset.mem_image_of_mem _ hs)
    intro p hp q hq
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hq
    exact (hC _ hs' _ ht').1
  · refine thru_spec ?_ (Finset.mem_image_of_mem _ hs)
    intro p hp q hq
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hq
    exact (hC _ hs' _ ht').2

/-- **`T` is `QSTAB` of its exclusivity graph.** -/
theorem tD_iff_qstab (t : (X × Y) × (X' × Y') → ℝ≥0∞) :
    t ∈ tD X Y X' Y' ↔ ∀ C : Finset ((X × Y) × (X' × Y')),
      (∀ s ∈ C, ∀ u ∈ C, cp2 s u) → ∑ s ∈ C, t s ≤ 1 := by
  constructor
  · intro ht C hC
    obtain ⟨f, g, hfg⟩ := cov_of_pairwise hC
    have h1 := ht _ (det_mem_lin' f) _ (det_mem_lin' g)
    rw [pair_det'] at h1
    exact le_trans (Finset.sum_le_sum_of_subset fun s hs =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hfg s hs⟩) h1
  · intro h
    exact mem_tD_of_det _ fun f g => h _ fun s hs u hu =>
      cp2_of_cov (Finset.mem_filter.1 hs).2 (Finset.mem_filter.1 hu).2

/-! ### Certain elements are deterministic sequential strategies -/

theorem sum_le_one_of_sharp {ι : Type*} {s : Finset ι} {z : ι → ℝ≥0∞}
    (h01 : ∀ i, z i = 0 ∨ z i = 1) (h : ∀ i ∈ s, ∀ j ∈ s, z i = 1 → z j = 1 → i = j) :
    ∑ i ∈ s, z i ≤ 1 := by
  classical
  have : ∑ i ∈ s, z i = ((s.filter (z · = 1)).card : ℝ≥0∞) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases h01 i with h' | h' <;> simp [h']
  rw [this]
  have hc : (s.filter (z · = 1)).card ≤ 1 := Finset.card_le_one.2 fun i hi j hj => by
    simp only [Finset.mem_filter] at hi hj; exact h i hi.1 j hj.1 hi.2 hj.2
  exact_mod_cast hc

/-- Distinct support points of a certain element are not jointly coverable. -/
theorem sharp_excl' {z : (X × Y) × (X' × Y') → ℝ≥0∞} (hz : z ∈ tD X Y X' Y') {s t : (X × Y) × (X' × Y')}
    (hs : z s = 1) (ht : z t = 1) (hne : s ≠ t) : ¬ cp2 s t := by
  intro hc
  have := (tD_iff_qstab z).1 hz {s, t} (by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact hc
    · exact ⟨(hc.1.elim (fun h => Or.inl h.symm) fun h => Or.inr (Ne.symm h)),
        (hc.2.elim (fun h => Or.inl h.symm) fun h => Or.inr (Ne.symm h))⟩
    · exact ⟨Or.inl rfl, Or.inl rfl⟩)
  rw [Finset.sum_pair hne, hs, ht] at this
  norm_num at this

theorem not_cp2 {s t : (X × Y) × (X' × Y')} (h : ¬ cp2 s t) :
    (s.1.1 = t.1.1 ∧ s.1 ≠ t.1) ∨ (s.2.1 = t.2.1 ∧ s.2 ≠ t.2) := by
  simp only [cp2, cp, not_and_or, not_or, ne_eq, not_not] at h
  tauto

/-- An `f`-first deterministic tree: `f` is queried at `a`, then `g` at `cf b`. -/
def FTree (a : X) (cf : Y → X') (pq : (X × Y) × (X' × Y')) : Prop :=
  pq.1.1 = a ∧ pq.2.1 = cf pq.1.2

/-- A `g`-first deterministic tree: `g` is queried at `c`, then `f` at `af d`. -/
def GTree (c : X') (af : Y' → X) (pq : (X × Y) × (X' × Y')) : Prop :=
  pq.2.1 = c ∧ pq.1.1 = af pq.2.2

/-- Points of one tree that are jointly coverable coincide. -/
theorem FTree_inj {a : X} {cf : Y → X'} {s t : (X × Y) × (X' × Y')} (hs : FTree a cf s) (ht : FTree a cf t)
    (hc : cp2 s t) : s = t := by
  have h1 : s.1 = t.1 := by
    rcases hc.1 with h | h
    · exact h
    · exact absurd (hs.1.trans ht.1.symm) h
  have h2 : s.2 = t.2 := by
    rcases hc.2 with h | h
    · exact h
    · exact absurd (by rw [hs.2, ht.2, h1]) h
  exact Prod.ext h1 h2

theorem GTree_inj {c : X'} {af : Y' → X} {s t : (X × Y) × (X' × Y')} (hs : GTree c af s) (ht : GTree c af t)
    (hc : cp2 s t) : s = t := by
  have h2 : s.2 = t.2 := by
    rcases hc.2 with h | h
    · exact h
    · exact absurd (hs.1.trans ht.1.symm) h
  have h1 : s.1 = t.1 := by
    rcases hc.1 with h | h
    · exact h
    · exact absurd (by rw [hs.2, ht.2, h2]) h
  exact Prod.ext h1 h2

/-- **The certain elements of `T` are exactly the deterministic sequential strategies**: a
`{0,1}`-valued `z` lies in `T` iff its support is contained in an `f`-first or a `g`-first tree
(the strategy halts exactly on the support). -/
theorem sharp_tD_iff [Nonempty X] [Nonempty X'] {z : (X × Y) × (X' × Y') → ℝ≥0∞}
    (h01 : ∀ pq, z pq = 0 ∨ z pq = 1) :
    z ∈ tD X Y X' Y' ↔
      (∃ a cf, ∀ pq, z pq = 1 → FTree a cf pq) ∨ (∃ c af, ∀ pq, z pq = 1 → GTree c af pq) := by
  classical
  constructor
  · intro hz
    -- either all `f`-inputs agree or all `g`-inputs agree
    have side : (∀ s t, z s = 1 → z t = 1 → s.1.1 = t.1.1) ∨
        (∀ s t, z s = 1 → z t = 1 → s.2.1 = t.2.1) := by
      by_contra hcon
      simp only [not_or, not_forall] at hcon
      obtain ⟨⟨s, t, hs, ht, hst⟩, ⟨u, v, hu, hv, huv⟩⟩ := hcon
      have hsg : s.2.1 = t.2.1 := by
        rcases not_cp2 (sharp_excl' hz hs ht (fun h => hst (by rw [h]))) with h | h
        · exact absurd h.1 hst
        · exact h.1
      have huf : u.1.1 = v.1.1 := by
        rcases not_cp2 (sharp_excl' hz hu hv (fun h => huv (by rw [h]))) with h | h
        · exact h.1
        · exact absurd h.1 huv
      have pick : ∀ {α : Type} (x y w : α), x ≠ y → x ≠ w ∨ y ≠ w := fun x y w h => by
        by_contra hc; push_neg at hc; exact h (hc.1.trans hc.2.symm)
      obtain ⟨s', hs', hs'f, hs'g⟩ : ∃ s', z s' = 1 ∧ s'.1.1 ≠ u.1.1 ∧ s'.2.1 = s.2.1 := by
        rcases pick _ _ u.1.1 hst with h | h
        · exact ⟨s, hs, h, rfl⟩
        · exact ⟨t, ht, h, hsg.symm⟩
      obtain ⟨u', hu', hu'f, hu'g⟩ : ∃ u', z u' = 1 ∧ u'.1.1 = u.1.1 ∧ u'.2.1 ≠ s.2.1 := by
        rcases pick _ _ s.2.1 huv with h | h
        · exact ⟨u, hu, rfl, h⟩
        · exact ⟨v, hv, huf.symm, h⟩
      have hne : s' ≠ u' := fun h => hs'f (by rw [h, hu'f])
      rcases not_cp2 (sharp_excl' hz hs' hu' hne) with h | h
      · exact hs'f (h.1.trans hu'f)
      · exact hu'g (h.1.symm.trans hs'g)
    rcases side with hA | hB
    · left
      by_cases hne : ∃ s, z s = 1
      · obtain ⟨s0, hs0⟩ := hne
        let cf : Y → X' := fun b =>
          if h : ∃ t, z t = 1 ∧ t.1.2 = b then (Classical.choose h).2.1 else s0.2.1
        refine ⟨s0.1.1, cf, fun p hp => ⟨hA p s0 hp hs0, ?_⟩⟩
        have hex : ∃ t, z t = 1 ∧ t.1.2 = p.1.2 := ⟨p, hp, rfl⟩
        simp only [cf, dif_pos hex]
        obtain ⟨ht, htb⟩ := Classical.choose_spec hex
        set t := Classical.choose hex
        have h1 : t.1 = p.1 := Prod.ext (hA t p ht hp) htb
        by_cases htp : t = p
        · rw [htp]
        · rcases not_cp2 (sharp_excl' hz ht hp htp) with h | h
          · exact absurd h1 h.2
          · exact h.1.symm
      · push_neg at hne
        exact ⟨Classical.arbitrary X, fun _ => Classical.arbitrary X', fun pq hpq =>
          absurd hpq (hne pq)⟩
    · right
      by_cases hne : ∃ s, z s = 1
      · obtain ⟨s0, hs0⟩ := hne
        let af : Y' → X := fun d =>
          if h : ∃ t, z t = 1 ∧ t.2.2 = d then (Classical.choose h).1.1 else s0.1.1
        refine ⟨s0.2.1, af, fun p hp => ⟨hB p s0 hp hs0, ?_⟩⟩
        have hex : ∃ t, z t = 1 ∧ t.2.2 = p.2.2 := ⟨p, hp, rfl⟩
        simp only [af, dif_pos hex]
        obtain ⟨ht, htd⟩ := Classical.choose_spec hex
        set t := Classical.choose hex
        have h1 : t.2 = p.2 := Prod.ext (hB t p ht hp) htd
        by_cases htp : t = p
        · rw [htp]
        · rcases not_cp2 (sharp_excl' hz ht hp htp) with h | h
          · exact h.1.symm
          · exact absurd h1 h.2
      · push_neg at hne
        exact ⟨Classical.arbitrary X', fun _ => Classical.arbitrary X, fun pq hpq =>
          absurd hpq (hne pq)⟩
  · intro h
    rw [tD_iff_qstab]
    intro C hC
    refine sum_le_one_of_sharp h01 fun s hs t ht hzs hzt => ?_
    rcases h with ⟨a, cf, hT⟩ | ⟨c, af, hT⟩
    · exact FTree_inj (hT s hzs) (hT t hzt) (hC s hs t ht)
    · exact GTree_inj (hT s hzs) (hT t hzt) (hC s hs t ht)

/-! ### The strict gap for all types with at least two elements -/

section Gap

variable (ex : Bool → X) (ey : Bool → Y) (ex' : Bool → X') (ey' : Bool → Y')

/-- Embedding of the `Bool` web into the general web. -/
def emb (s : W × W) : (X × Y) × (X' × Y') :=
  ((ex s.1.1, ey s.1.2), (ex' s.2.1, ey' s.2.2))

variable {ex ey ex' ey'}

theorem cp_emb {X Y : Type} {ex : Bool → X} {ey : Bool → Y} (hx : Function.Injective ex)
    (hy : Function.Injective ey) (p q : W) : cp (ex p.1, ey p.2) (ex q.1, ey q.2) ↔ compat p q := by
  simp only [cp, compat, Prod.ext_iff, hx.eq_iff, hy.eq_iff, ne_eq]

theorem cp2_emb (hx : Function.Injective ex) (hy : Function.Injective ey)
    (hx' : Function.Injective ex') (hy' : Function.Injective ey') (s t : W × W) :
    cp2 (emb ex ey ex' ey' s) (emb ex ey ex' ey' t) ↔ compat2 s t := by
  simp only [cp2, emb, compat2]
  rw [cp_emb hx hy, cp_emb hx' hy']

theorem emb_inj (hx : Function.Injective ex) (hy : Function.Injective ey)
    (hx' : Function.Injective ex') (hy' : Function.Injective ey') :
    Function.Injective (emb ex ey ex' ey') := by
  intro s t h
  simp only [emb, Prod.mk.injEq] at h
  exact Prod.ext (Prod.ext (hx h.1.1) (hy h.1.2)) (Prod.ext (hx' h.2.1) (hy' h.2.2))

/-- The embedded pentagon element. -/
noncomputable def pentE (ex : Bool → X) (ey : Bool → Y) (ex' : Bool → X') (ey' : Bool → Y') :
    (X × Y) × (X' × Y') → ℝ≥0∞ :=
  fun u => if u ∈ pent.image (emb ex ey ex' ey') then 2⁻¹ else 0

theorem pentE_mem (hx : Function.Injective ex) (hy : Function.Injective ey)
    (hx' : Function.Injective ex') (hy' : Function.Injective ey') :
    pentE ex ey ex' ey' ∈ tD X Y X' Y' := by
  classical
  rw [tD_iff_qstab]
  intro C hC
  set φ := emb ex ey ex' ey'
  let B := pent.filter (fun s => φ s ∈ C)
  have hB : B.card ≤ 2 := pent_clique_le_two B (Finset.mem_powerset.2 (Finset.filter_subset _ _))
    fun s hs t ht => (cp2_emb hx hy hx' hy' s t).1
      (hC _ (Finset.mem_filter.1 hs).2 _ (Finset.mem_filter.1 ht).2)
  calc ∑ u ∈ C, pentE ex ey ex' ey' u = ∑ u ∈ C.filter (· ∈ pent.image φ), (2⁻¹ : ℝ≥0∞) := by
        rw [Finset.sum_filter]; rfl
    _ = (C.filter (· ∈ pent.image φ)).card * 2⁻¹ := by simp
    _ ≤ 2 * 2⁻¹ := by
        gcongr
        have : C.filter (· ∈ pent.image φ) = B.image φ := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_image, B]
          constructor
          · rintro ⟨hu, s, hs, rfl⟩; exact ⟨s, ⟨hs, hu⟩, rfl⟩
          · rintro ⟨s, ⟨hs, hu⟩, rfl⟩; exact ⟨hu, s, hs, rfl⟩
        rw [this]
        exact_mod_cast (Finset.card_image_le).trans hB
    _ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

theorem sharp_pentE_le (hx : Function.Injective ex) (hy : Function.Injective ey)
    (hx' : Function.Injective ex') (hy' : Function.Injective ey')
    {z : (X × Y) × (X' × Y') → ℝ≥0∞} (hz : z ∈ tD X Y X' Y') (h01 : ∀ u, z u = 0 ∨ z u = 1) :
    ∑ s ∈ pent, z (emb ex ey ex' ey' s) ≤ 2 := by
  classical
  set φ := emb ex ey ex' ey'
  let B := pent.filter (fun s => z (φ s) = 1)
  have hB : B.card ≤ 2 := pent_indep_le_two B (Finset.mem_powerset.2 (Finset.filter_subset _ _))
    fun s hs t ht hst => by
      by_contra hne
      exact sharp_excl' hz (Finset.mem_filter.1 hs).2 (Finset.mem_filter.1 ht).2
        (fun h => hne (emb_inj hx hy hx' hy' h)) ((cp2_emb hx hy hx' hy' s t).2 hst)
  have : ∑ s ∈ pent, z (φ s) = B.card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases h01 (φ s) with h | h <;> simp [h]
  rw [this]; exact_mod_cast hB

/-- **The strict gap, for all finite data types with at least two elements.** The embedded
pentagon lies in `((X ⊸ Y) ⊗ (X' ⊸ Y'))^⊥` but is no mixture of its certain elements. -/
theorem pentE_not_mix (hx : Function.Injective ex) (hy : Function.Injective ey)
    (hx' : Function.Injective ex') (hy' : Function.Injective ey')
    {n : ℕ} (w : Fin n → ℝ≥0∞) (hw : ∑ i, w i = 1) (z : Fin n → (X × Y) × (X' × Y') → ℝ≥0∞)
    (hz : ∀ i, z i ∈ tD X Y X' Y') (h01 : ∀ i u, z i u = 0 ∨ z i u = 1) :
    pentE ex ey ex' ey' ≠ ∑ i, w i • z i := by
  intro h
  set φ := emb ex ey ex' ey'
  have lhs : ∑ s ∈ pent, pentE ex ey ex' ey' (φ s) = 5 * 2⁻¹ := by
    have h2 : ∀ s ∈ pent, pentE ex ey ex' ey' (φ s) = 2⁻¹ := fun s hs =>
      if_pos (Finset.mem_image_of_mem _ hs)
    have hc : pent.card = 5 := by decide
    rw [Finset.sum_congr rfl h2, Finset.sum_const, hc, nsmul_eq_mul]; norm_num
  have rhs : ∑ s ∈ pent, (∑ i, w i • z i) (φ s) ≤ 2 := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    calc ∑ i, ∑ s ∈ pent, w i * z i (φ s) = ∑ i, w i * ∑ s ∈ pent, z i (φ s) := by
          simp [Finset.mul_sum]
      _ ≤ ∑ i, w i * 2 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_left' (sharp_pentE_le hx hy hx' hy' (hz i) (h01 i)) _
      _ = 2 := by rw [← Finset.sum_mul, hw, one_mul]
  rw [← h, lhs] at rhs
  have : (5 : ℝ≥0∞) * 2⁻¹ = 5 / 2 := (div_eq_mul_inv _ _).symm
  rw [this, ENNReal.div_le_iff two_ne_zero ENNReal.ofNat_ne_top] at rhs
  norm_num at rhs

end Gap

end ConstructiveProb.PCS.General
