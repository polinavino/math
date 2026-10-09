/-
# The decomposition: absorption, the root step, and the forest induction

For a forest code `t` and an additive code `K`, every `z : nodes → W K → ℝ` with
`ω K (path sum) ≤ 1` along every path is a mixture of assignments whose path sums are
stable sets of `K` (`main`). Equivalently, the clique-constrained polytope of the strong product
of a forest comparability graph and a cograph has only `{0,1}`-vertices.

* `exact_absorb`: part of a vector raises `ω` to exactly a given level.
* `absorb`: along a forest, split `y = p + q` so that `p` fits under level `L` on top of a base
  `m`, and `q` costs no more than what exceeds `L`.
* `root`: the law of the root's stable set and the conditional weights of the subforest.
* `main`: induction on the forest.
-/
import ConstructiveProb.CographBasic

open Finset

namespace ConstructiveProb.Cograph

open ACode TCode

/-! ### Joining vectors on the two summands -/

/-- A vector on the web of `a & b` from vectors on the two summands. -/
def jn {a b : ACode} (f : W a → ℝ) (g : W b → ℝ) : W (ACode.wth a b) → ℝ := Sum.elim f g

/-- A vector on the web of `a ⊕ b` from vectors on the two summands. -/
def jp {a b : ACode} (f : W a → ℝ) (g : W b → ℝ) : W (ACode.plus a b) → ℝ := Sum.elim f g

theorem ω_jn {a b : ACode} (f : W a → ℝ) (g : W b → ℝ) : ω (ACode.wth a b) (jn f g) = ω a f + ω b g :=
  rfl

theorem ω_jp {a b : ACode} (f : W a → ℝ) (g : W b → ℝ) :
    ω (ACode.plus a b) (jp f g) = max (ω a f) (ω b g) := rfl

theorem jn_add {a b : ACode} (f f' : W a → ℝ) (g g' : W b → ℝ) :
    jn f g + jn f' g' = jn (f + f') (g + g') := by
  funext x; rcases x with x | x <;> rfl

theorem jp_add {a b : ACode} (f f' : W a → ℝ) (g g' : W b → ℝ) :
    jp f g + jp f' g' = jp (f + f') (g + g') := by
  funext x; rcases x with x | x <;> rfl

theorem jn_split {a b : ACode} (v : W (ACode.wth a b) → ℝ) :
    v = jn (fun x => v (Sum.inl x)) (fun x => v (Sum.inr x)) := by
  funext x; rcases x with x | x <;> rfl

theorem jp_split {a b : ACode} (v : W (ACode.plus a b) → ℝ) :
    v = jp (fun x => v (Sum.inl x)) (fun x => v (Sum.inr x)) := by
  funext x; rcases x with x | x <;> rfl

theorem jn_nonneg {a b : ACode} {f : W a → ℝ} {g : W b → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    0 ≤ jn f g := by
  intro x; rcases x with x | x
  · exact hf x
  · exact hg x

theorem jp_nonneg {a b : ACode} {f : W a → ℝ} {g : W b → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    0 ≤ jp f g := by
  intro x; rcases x with x | x
  · exact hf x
  · exact hg x

/-! ### Exact absorption -/

theorem exact_absorb : ∀ (K : ACode) {b v : W K → ℝ} {L : ℝ}, 0 ≤ b → 0 ≤ v → ω K b ≤ L →
    L ≤ ω K (b + v) → ∃ a : W K → ℝ, 0 ≤ a ∧ a ≤ v ∧ ω K (b + a) = L
  | ACode.one, b, v, L, _, _, h1, h2 => by
    refine ⟨fun _ => L - b pt, fun x => ?_, fun x => ?_, ?_⟩
    · have : b pt ≤ L := h1
      show 0 ≤ L - b pt; linarith
    · have : L ≤ b pt + v pt := h2
      rw [eq_pt x]; show L - b pt ≤ v pt; linarith
    · show b pt + (L - b pt) = L; ring
  | ACode.wth K1 K2, b, v, L, hb, hv, h1, h2 => by
    set b1 : W K1 → ℝ := fun x => b (Sum.inl x)
    set b2 : W K2 → ℝ := fun x => b (Sum.inr x)
    set v1 : W K1 → ℝ := fun x => v (Sum.inl x)
    set v2 : W K2 → ℝ := fun x => v (Sum.inr x)
    have e1 : ω K1 b1 + ω K2 b2 ≤ L := h1
    have e2 : L ≤ ω K1 (b1 + v1) + ω K2 (b2 + v2) := h2
    have m1 : ω K1 b1 ≤ ω K1 (b1 + v1) :=
      ω_mono K1 fun x => le_add_of_nonneg_right (hv (Sum.inl x))
    have m2 : ω K2 b2 ≤ ω K2 (b2 + v2) :=
      ω_mono K2 fun x => le_add_of_nonneg_right (hv (Sum.inr x))
    set L1 := max (ω K1 b1) (L - ω K2 (b2 + v2))
    obtain ⟨a1, ha1, ha1v, ha1L⟩ := exact_absorb K1 (b := b1) (v := v1) (L := L1)
      (fun x => hb _) (fun x => hv _) (le_max_left _ _) (max_le m1 (by linarith))
    obtain ⟨a2, ha2, ha2v, ha2L⟩ := exact_absorb K2 (b := b2) (v := v2) (L := L - L1)
      (fun x => hb _) (fun x => hv _) (by
        have : L1 ≤ L - ω K2 b2 := max_le (by linarith) (by linarith)
        linarith) (by
        have : L - ω K2 (b2 + v2) ≤ L1 := le_max_right _ _
        linarith)
    refine ⟨jn a1 a2, jn_nonneg ha1 ha2, ?_, ?_⟩
    · intro x; rcases x with x | x
      · exact ha1v x
      · exact ha2v x
    · rw [jn_split b, jn_add, ω_jn, ha1L, ha2L]; ring
  | ACode.plus K1 K2, b, v, L, hb, hv, h1, h2 => by
    set b1 : W K1 → ℝ := fun x => b (Sum.inl x)
    set b2 : W K2 → ℝ := fun x => b (Sum.inr x)
    set v1 : W K1 → ℝ := fun x => v (Sum.inl x)
    set v2 : W K2 → ℝ := fun x => v (Sum.inr x)
    have e1 : max (ω K1 b1) (ω K2 b2) ≤ L := h1
    have e2 : L ≤ max (ω K1 (b1 + v1)) (ω K2 (b2 + v2)) := h2
    have m1 : ω K1 b1 ≤ ω K1 (b1 + v1) :=
      ω_mono K1 fun x => le_add_of_nonneg_right (hv (Sum.inl x))
    have m2 : ω K2 b2 ≤ ω K2 (b2 + v2) :=
      ω_mono K2 fun x => le_add_of_nonneg_right (hv (Sum.inr x))
    obtain ⟨a1, ha1, ha1v, ha1L⟩ := exact_absorb K1 (b := b1) (v := v1)
      (L := min L (ω K1 (b1 + v1))) (fun x => hb _) (fun x => hv _)
      (le_min (le_trans (le_max_left _ _) e1) m1) (min_le_right _ _)
    obtain ⟨a2, ha2, ha2v, ha2L⟩ := exact_absorb K2 (b := b2) (v := v2)
      (L := min L (ω K2 (b2 + v2))) (fun x => hb _) (fun x => hv _)
      (le_min (le_trans (le_max_right _ _) e1) m2) (min_le_right _ _)
    refine ⟨jp a1 a2, jp_nonneg ha1 ha2, ?_, ?_⟩
    · intro x; rcases x with x | x
      · exact ha1v x
      · exact ha2v x
    · rw [jp_split b, jp_add, ω_jp, ha1L, ha2L, ← min_max_distrib_left]
      exact min_eq_left e2

/-! ### Path sums of tuples -/

section PathTuples

variable {α β : Type*}

theorem PathSums_fst {V V' : Type*} [AddCommMonoid V] [AddCommMonoid V'] (t : TCode)
    (z : N t → V × V') {T : V × V'} (hT : T ∈ PathSums t z) :
    T.1 ∈ PathSums t (fun x => (z x).1) := by
  show T.1 ∈ PathSums t (fun x => AddMonoidHom.fst V V' (z x))
  rw [PathSums_map (AddMonoidHom.fst V V') t z]; exact ⟨T, hT, rfl⟩

theorem PathSums_snd {V V' : Type*} [AddCommMonoid V] [AddCommMonoid V'] (t : TCode)
    (z : N t → V × V') {T : V × V'} (hT : T ∈ PathSums t z) :
    T.2 ∈ PathSums t (fun x => (z x).2) := by
  show T.2 ∈ PathSums t (fun x => AddMonoidHom.snd V V' (z x))
  rw [PathSums_map (AddMonoidHom.snd V V') t z]; exact ⟨T, hT, rfl⟩

theorem PathSums_pair_nonneg (t : TCode) {f g : N t → α → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    {T : (α → ℝ) × (α → ℝ)} (hT : T ∈ PathSums t (fun x => (f x, g x))) : 0 ≤ T.1 ∧ 0 ≤ T.2 :=
  ⟨PathSums_nonneg t f hf _ (PathSums_fst t _ hT), PathSums_nonneg t g hg _ (PathSums_snd t _ hT)⟩

theorem PathSums_zero {V : Type*} [AddCommMonoid V] (t : TCode) {S : V}
    (hS : S ∈ PathSums t (fun _ => (0 : V))) : S = 0 := by
  have := PathSums_map (0 : V →+ V) t (fun _ => 0)
  simp only [AddMonoidHom.zero_apply] at this
  rw [this] at hS
  obtain ⟨_, _, rfl⟩ := hS; rfl

end PathTuples

/-! ### Absorption -/

/-- The two absorption conditions along one path, with path sums `S = (Σ p, Σ q)`. -/
def AbsOK (K : ACode) (L : ℝ) (m : W K → ℝ) (S : (W K → ℝ) × (W K → ℝ)) : Prop :=
  ω K (m + S.1) ≤ L ∧ ω K S.2 + L ≤ max L (ω K (m + S.1 + S.2))

/-- The absorption statement at a level `L`. -/
def AbsAt (K : ACode) (t : TCode) (L : ℝ) (m : W K → ℝ) (y : N t → W K → ℝ) : Prop :=
  ∃ p q : N t → W K → ℝ, 0 ≤ p ∧ 0 ≤ q ∧ p + q = y ∧
    ∀ S ∈ PathSums t (fun x => (p x, q x)), AbsOK K L m S

theorem AbsOK_zero (K : ACode) {L : ℝ} {m : W K → ℝ} (hm : ω K m ≤ L) : AbsOK K L m 0 := by
  refine ⟨by simpa using hm, ?_⟩
  simp only [Prod.fst_zero, Prod.snd_zero, ω_zero, zero_add]
  exact le_max_left _ _

/-- **Greedy absorption** from absorption at the level of the base. -/
theorem greedy (K : ACode)
    (abs0 : ∀ (t : TCode) (m : W K → ℝ) (y : N t → W K → ℝ), 0 ≤ m → 0 ≤ y →
      AbsAt K t (ω K m) m y) :
    ∀ (t : TCode) (L : ℝ) (m : W K → ℝ) (y : N t → W K → ℝ), 0 ≤ m → 0 ≤ y → ω K m ≤ L →
      AbsAt K t L m y
  | TCode.one, L, m, y, hm, hy, hL => by
    set v := y ACode.pt
    by_cases h : ω K (m + v) ≤ L
    · refine ⟨y, 0, hy, le_rfl, by simp, ?_⟩
      rintro S (rfl | hS)
      · exact AbsOK_zero K hL
      · rw [Set.mem_singleton_iff.1 hS]
        refine ⟨h, ?_⟩
        show ω K 0 + L ≤ _
        rw [ω_zero, zero_add]
        exact le_max_left _ _
    · have h' : L < ω K (m + v) := not_le.1 h
      obtain ⟨a, ha0, hav, haL⟩ := exact_absorb K hm (hy _) hL h'.le
      obtain ⟨p', q', hp', hq', hpq', hS'⟩ := abs0 TCode.one (m + a) (fun _ => v - a)
        (add_nonneg hm ha0) (fun _ => sub_nonneg.2 hav)
      refine ⟨fun x => a + p' x, q', fun x => add_nonneg ha0 (hp' x), hq', ?_, ?_⟩
      · funext x
        have := congrFun hpq' x
        simp only [Pi.add_apply] at this ⊢
        rw [ACode.eq_pt x] at this ⊢
        rw [add_assoc, this]; abel
      · rintro S (rfl | hS)
        · exact AbsOK_zero K hL
        · rw [Set.mem_singleton_iff.1 hS]
          have := hS' (p' ACode.pt, q' ACode.pt) (Set.mem_insert_of_mem _ rfl)
          rw [haL] at this
          obtain ⟨h1, h2⟩ := this
          dsimp only at h1 h2
          have e : m + a + p' ACode.pt + q' ACode.pt = m + v := by
            have := congrFun hpq' ACode.pt
            simp only [Pi.add_apply] at this
            rw [add_assoc (m + a), this]; abel
          have e2 : m + (a + p' ACode.pt) + q' ACode.pt = m + v := by rw [← e]; abel
          refine ⟨?_, ?_⟩
          · show ω K (m + (a + p' ACode.pt)) ≤ L
            rw [← add_assoc]; exact h1
          · show ω K (q' ACode.pt) + L ≤ max L (ω K (m + (a + p' ACode.pt) + q' ACode.pt))
            rw [e2]; rw [e] at h2; exact h2
  | TCode.plus s u, L, m, y, hm, hy, hL => by
    obtain ⟨ps, qs, hps, hqs, hpqs, hs⟩ := greedy K abs0 s L m (fun x => y (Sum.inl x)) hm
      (fun x => hy _) hL
    obtain ⟨pu, qu, hpu, hqu, hpqu, hu⟩ := greedy K abs0 u L m (fun x => y (Sum.inr x)) hm
      (fun x => hy _) hL
    refine ⟨Sum.elim ps pu, Sum.elim qs qu, ?_, ?_, ?_, ?_⟩
    · rintro (x | x)
      · exact hps x
      · exact hpu x
    · rintro (x | x)
      · exact hqs x
      · exact hqu x
    · funext x; rcases x with x | x
      · exact congrFun hpqs x
      · exact congrFun hpqu x
    · rintro S (hS | hS)
      · exact hs S hS
      · exact hu S hS
  | TCode.cone u, L, m, y, hm, hy, hL => by
    set v := y (root u)
    by_cases h : ω K (m + v) ≤ L
    · obtain ⟨pu, qu, hpu, hqu, hpqu, hu⟩ := greedy K abs0 u L (m + v)
        (fun x => y (Sum.inl x)) (add_nonneg hm (hy _)) (fun x => hy _) h
      refine ⟨Sum.elim pu (fun _ => v), Sum.elim qu (fun _ => 0), ?_, ?_, ?_, ?_⟩
      · rintro (x | x)
        · exact hpu x
        · exact hy (root u)
      · rintro (x | x)
        · exact hqu x
        · exact le_rfl
      · funext x; rcases x with x | x
        · exact congrFun hpqu x
        · show v + 0 = y (Sum.inr x)
          rw [add_zero, ACode.eq_pt x]; rfl
      · rintro S (rfl | ⟨T, hT, rfl⟩)
        · exact AbsOK_zero K hL
        · obtain ⟨h1, h2⟩ := hu T hT
          refine ⟨?_, ?_⟩
          · show ω K (m + (v + T.1)) ≤ L
            rw [← add_assoc]; exact h1
          · show ω K (0 + T.2) + L ≤ max L (ω K (m + (v + T.1) + (0 + T.2)))
            rw [zero_add, ← add_assoc]; exact h2
    · have h' : L < ω K (m + v) := not_le.1 h
      obtain ⟨a, ha0, hav, haL⟩ := exact_absorb K hm (hy _) hL h'.le
      let r : N (TCode.cone u) → W K → ℝ := Sum.elim (fun _ => 0) (fun _ => a)
      let y' : N (TCode.cone u) → W K → ℝ := Sum.elim (fun x => y (Sum.inl x)) (fun _ => v - a)
      obtain ⟨p', q', hp', hq', hpq', hS'⟩ := abs0 (TCode.cone u) (m + a) y'
        (add_nonneg hm ha0) (by
          rintro (x | x)
          · exact hy _
          · exact sub_nonneg.2 hav)
      refine ⟨p' + r, q', ?_, hq', ?_, ?_⟩
      · rintro (x | x)
        · show 0 ≤ p' (Sum.inl x) + 0
          rw [add_zero]; exact hp' _
        · exact add_nonneg (hp' _) ha0
      · funext x; rcases x with x | x
        · have := congrFun hpq' (Sum.inl x)
          show p' (Sum.inl x) + 0 + q' (Sum.inl x) = y (Sum.inl x)
          rw [add_zero]; exact this
        · have := congrFun hpq' (Sum.inr x)
          show p' (Sum.inr x) + a + q' (Sum.inr x) = y (Sum.inr x)
          have e : p' (Sum.inr x) + q' (Sum.inr x) = v - a := this
          rw [add_right_comm, e, ACode.eq_pt x]; show v - a + a = v; ring
      · rintro S (rfl | ⟨T, hT, rfl⟩)
        · exact AbsOK_zero K hL
        · have hfun : (fun x => ((p' + r) (Sum.inl x), q' (Sum.inl x))) =
              (fun x => (p' (Sum.inl x), q' (Sum.inl x))) := by
            funext x; show ((p' (Sum.inl x) + 0, q' (Sum.inl x))) = _; rw [add_zero]
          have hT' : T ∈ PathSums u (fun x => (p' (Sum.inl x), q' (Sum.inl x))) := hfun ▸ hT
          have hS'' := hS' ((p' (root u), q' (root u)) + T) (Set.mem_insert_of_mem _ ⟨T, hT', rfl⟩)
          rw [haL] at hS''
          obtain ⟨h1, h2⟩ := hS''
          have e : m + a + (p' (root u) + T.1) + (q' (root u) + T.2) =
              m + ((p' + r) (root u) + T.1) + (q' (root u) + T.2) := by
            show _ = m + (p' (root u) + a + T.1) + (q' (root u) + T.2); abel
          refine ⟨?_, ?_⟩
          · show ω K (m + ((p' + r) (root u) + T.1)) ≤ L
            have : m + ((p' + r) (root u) + T.1) =
                m + a + (p' (root u) + T.1) := by
              show m + (p' (root u) + a + T.1) = _; abel
            rw [this]; exact h1
          · show ω K (q' (root u) + T.2) + L ≤
              max L (ω K (m + ((p' + r) (root u) + T.1) +
                (q' (root u) + T.2)))
            rw [← e]; exact h2

/-- Joining pairs of vectors on the summands of `a & b`, as an additive map. -/
def jnHom (a b : ACode) :
    ((W a → ℝ) × (W a → ℝ)) × ((W b → ℝ) × (W b → ℝ)) →+
      (W (ACode.wth a b) → ℝ) × (W (ACode.wth a b) → ℝ) where
  toFun T := (jn T.1.1 T.2.1, jn T.1.2 T.2.2)
  map_zero' := Prod.ext (funext fun x => by rcases x with x | x <;> rfl)
    (funext fun x => by rcases x with x | x <;> rfl)
  map_add' T T' := Prod.ext (funext fun x => by rcases x with x | x <;> rfl)
    (funext fun x => by rcases x with x | x <;> rfl)

/-- Joining pairs of vectors on the summands of `a ⊕ b`, as an additive map. -/
def jpHom (a b : ACode) :
    ((W a → ℝ) × (W a → ℝ)) × ((W b → ℝ) × (W b → ℝ)) →+
      (W (ACode.plus a b) → ℝ) × (W (ACode.plus a b) → ℝ) where
  toFun T := (jp T.1.1 T.2.1, jp T.1.2 T.2.2)
  map_zero' := Prod.ext (funext fun x => by rcases x with x | x <;> rfl)
    (funext fun x => by rcases x with x | x <;> rfl)
  map_add' T T' := Prod.ext (funext fun x => by rcases x with x | x <;> rfl)
    (funext fun x => by rcases x with x | x <;> rfl)

/-- Joining vectors on the summands of `a ⊕ b`, as an additive map. -/
def jpA (a b : ACode) : (W a → ℝ) × (W b → ℝ) →+ (W (ACode.plus a b) → ℝ) where
  toFun T := jp T.1 T.2
  map_zero' := funext fun x => by rcases x with x | x <;> rfl
  map_add' T T' := funext fun x => by rcases x with x | x <;> rfl

/-- Joining vectors on the summands of `a & b`, as an additive map. -/
def jnA (a b : ACode) : (W a → ℝ) × (W b → ℝ) →+ (W (ACode.wth a b) → ℝ) where
  toFun T := jn T.1 T.2
  map_zero' := funext fun x => by rcases x with x | x <;> rfl
  map_add' T T' := funext fun x => by rcases x with x | x <;> rfl

theorem le_ω_add (K : ACode) {m S : W K → ℝ} (hS : 0 ≤ S) : ω K m ≤ ω K (m + S) :=
  ω_mono K fun x => le_add_of_nonneg_right (hS x)

/-- **Absorption.** -/
theorem absorb : ∀ (K : ACode) (t : TCode) (L : ℝ) (m : W K → ℝ) (y : N t → W K → ℝ),
    0 ≤ m → 0 ≤ y → ω K m ≤ L → AbsAt K t L m y
  | ACode.one => greedy ACode.one fun t m y _ hy => by
    refine ⟨0, y, le_rfl, hy, by simp, fun S hS => ?_⟩
    have h1 : S.1 = 0 := PathSums_zero t (PathSums_fst t _ hS)
    refine ⟨by rw [h1, add_zero], ?_⟩
    rw [h1, add_zero]
    show S.2 ACode.pt + m ACode.pt ≤ max (m ACode.pt) ((m + S.2) ACode.pt)
    rw [Pi.add_apply, add_comm]; exact le_max_right _ _
  | ACode.wth K1 K2 => greedy (ACode.wth K1 K2) fun t m y hm hy => by
    obtain ⟨p1, q1, hp1, hq1, hpq1, h1⟩ := absorb K1 t (ω K1 fun x => m (Sum.inl x))
      (fun x => m (Sum.inl x)) (fun z x => y z (Sum.inl x)) (fun x => hm _)
      (fun z x => hy z _) le_rfl
    obtain ⟨p2, q2, hp2, hq2, hpq2, h2⟩ := absorb K2 t (ω K2 fun x => m (Sum.inr x))
      (fun x => m (Sum.inr x)) (fun z x => y z (Sum.inr x)) (fun x => hm _)
      (fun z x => hy z _) le_rfl
    refine ⟨fun z => jn (p1 z) (p2 z), fun z => jn (q1 z) (q2 z),
      fun z => jn_nonneg (hp1 z) (hp2 z), fun z => jn_nonneg (hq1 z) (hq2 z), ?_, ?_⟩
    · funext z x; rcases x with x | x
      · exact congrFun (congrFun hpq1 z) x
      · exact congrFun (congrFun hpq2 z) x
    · intro S hS
      have hS' : S ∈ PathSums t (fun z => jnHom K1 K2 ((p1 z, q1 z), (p2 z, q2 z))) := hS
      rw [PathSums_map] at hS'
      obtain ⟨T, hT, rfl⟩ := hS'
      have hT1 := PathSums_fst t _ hT
      have hT2 := PathSums_snd t _ hT
      obtain ⟨n11, n12⟩ := PathSums_pair_nonneg t hp1 hq1 hT1
      obtain ⟨n21, n22⟩ := PathSums_pair_nonneg t hp2 hq2 hT2
      obtain ⟨a1, a2⟩ := h1 _ hT1
      obtain ⟨b1, b2⟩ := h2 _ hT2
      rw [max_eq_right (le_trans (le_ω_add K1 n11) (le_ω_add K1 n12))] at a2
      rw [max_eq_right (le_trans (le_ω_add K2 n21) (le_ω_add K2 n22))] at b2
      have em : m = jn (fun x => m (Sum.inl x)) (fun x => m (Sum.inr x)) := jn_split m
      refine ⟨?_, ?_⟩
      · show ω _ (m + jn T.1.1 T.2.1) ≤ ω _ m
        rw [em, jn_add, ω_jn, ω_jn]
        exact add_le_add a1 b1
      · show ω _ (jn T.1.2 T.2.2) + ω _ m ≤ max (ω _ m) (ω _ (m + jn T.1.1 T.2.1 + jn T.1.2 T.2.2))
        rw [em, jn_add, jn_add, ω_jn, ω_jn, ω_jn]
        refine le_trans ?_ (le_max_right _ _)
        linarith
  | ACode.plus K1 K2 => fun t L m y hm hy hL => by
    have hL1 : ω K1 (fun x => m (Sum.inl x)) ≤ L := le_trans (le_max_left _ _) hL
    have hL2 : ω K2 (fun x => m (Sum.inr x)) ≤ L := le_trans (le_max_right _ _) hL
    obtain ⟨p1, q1, hp1, hq1, hpq1, h1⟩ := absorb K1 t L (fun x => m (Sum.inl x))
      (fun z x => y z (Sum.inl x)) (fun x => hm _) (fun z x => hy z _) hL1
    obtain ⟨p2, q2, hp2, hq2, hpq2, h2⟩ := absorb K2 t L (fun x => m (Sum.inr x))
      (fun z x => y z (Sum.inr x)) (fun x => hm _) (fun z x => hy z _) hL2
    refine ⟨fun z => jp (p1 z) (p2 z), fun z => jp (q1 z) (q2 z),
      fun z => jp_nonneg (hp1 z) (hp2 z), fun z => jp_nonneg (hq1 z) (hq2 z), ?_, ?_⟩
    · funext z x; rcases x with x | x
      · exact congrFun (congrFun hpq1 z) x
      · exact congrFun (congrFun hpq2 z) x
    · intro S hS
      have hS' : S ∈ PathSums t (fun z => jpHom K1 K2 ((p1 z, q1 z), (p2 z, q2 z))) := hS
      rw [PathSums_map] at hS'
      obtain ⟨T, hT, rfl⟩ := hS'
      obtain ⟨a1, a2⟩ := h1 _ (PathSums_fst t _ hT)
      obtain ⟨b1, b2⟩ := h2 _ (PathSums_snd t _ hT)
      have em : m = jp (fun x => m (Sum.inl x)) (fun x => m (Sum.inr x)) := jp_split m
      refine ⟨?_, ?_⟩
      · show ω _ (m + jp T.1.1 T.2.1) ≤ L
        rw [em, jp_add, ω_jp]
        exact max_le a1 b1
      · show ω _ (jp T.1.2 T.2.2) + L ≤ max L (ω _ (m + jp T.1.1 T.2.1 + jp T.1.2 T.2.2))
        rw [em, jp_add, jp_add, ω_jp, ω_jp, ← max_add_add_right]
        refine max_le (le_trans a2 ?_) (le_trans b2 ?_)
        · exact max_le_max le_rfl (le_max_left _ _)
        · exact max_le_max le_rfl (le_max_right _ _)

/-! ### The root step -/

/-- The pairs (stable set at the root, conditional weights of the subforest). -/
def RootSet (K : ACode) (t : TCode) : Set ((W K → ℝ) × (N t → W K → ℝ)) :=
  {p | IsStab K p.1 ∧ 0 ≤ p.2 ∧ ∀ S ∈ PathSums t p.2, ω K (p.1 + S) ≤ 1}

theorem PathSums_smul {α : Type*} (t : TCode) (c : ℝ) (y : N t → α → ℝ) {S : α → ℝ}
    (hS : S ∈ PathSums t (fun x => c • y x)) : ∃ S' ∈ PathSums t y, S = c • S' := by
  have := PathSums_map (DistribMulAction.toAddMonoidHom (α → ℝ) c) t y
  have hS2 : S ∈ PathSums t (fun x => DistribMulAction.toAddMonoidHom (α → ℝ) c (y x)) := hS
  rw [this] at hS2
  obtain ⟨S', hS', rfl⟩ := hS2
  exact ⟨S', hS', rfl⟩

/-- A node's vector vanishes when every path sum through it has `ω` zero. -/
theorem eq_zero_of_PathSums {K : ACode} (t : TCode) {y : N t → W K → ℝ} (hy : 0 ≤ y)
    (h : ∀ S ∈ PathSums t y, ω K S ≤ 0) : y = 0 := by
  funext x h'
  obtain ⟨S, hS, hle⟩ := le_PathSums t y hy x
  have hS0 : 0 ≤ S := PathSums_nonneg t y hy S hS
  have := le_trans (le_trans (hle h') (coord_le_ω K hS0 h')) (h S hS)
  exact le_antisymm this (hy x h')

theorem smul_inv_smul_of {E : Type*} [AddCommGroup E] [Module ℝ E] {c : ℝ} {v : E}
    (h : c = 0 → v = 0) : c • (c⁻¹ • v) = v := by
  by_cases hc : c = 0
  · rw [h hc, smul_zero, smul_zero]
  · rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- **The root step.** -/
theorem root_step : ∀ (K : ACode) (t : TCode) (m : W K → ℝ) (y : N t → W K → ℝ),
    0 ≤ m → 0 ≤ y → (∀ S ∈ PathSums t y, ω K (m + S) ≤ 1) → (m, y) ∈ PMix (RootSet K t)
  | ACode.one, t, m, y, hm, hy, h => by
    set μ := m ACode.pt
    have hμ1 : μ ≤ 1 := by
      have := h 0 (zero_mem_PathSums t y); rw [add_zero] at this; exact this
    have hμ0 : 0 ≤ μ := hm _
    have hmμ : m = fun _ => μ := funext fun x => by rw [ACode.eq_pt x]
    by_cases hlt : μ < 1
    · have key : (m, y) = μ • ((fun _ => (1 : ℝ)), (0 : N t → W ACode.one → ℝ)) +
          (1 - μ) • ((0 : W ACode.one → ℝ), (1 - μ)⁻¹ • y) := by
        refine Prod.ext ?_ ?_
        · funext x; simp [hmμ]
        · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add]
          rw [smul_smul, mul_inv_cancel₀ (by linarith), one_smul]
      rw [key]
      refine PMix_combo hμ0 hμ1 (fun _ => mem_PMix_self ⟨⟨fun _ => Or.inr rfl, le_rfl⟩, le_rfl,
        fun S hS => ?_⟩) (fun _ => mem_PMix_self ⟨⟨fun _ => Or.inl rfl, ?_⟩, ?_, fun S hS => ?_⟩)
      · rw [PathSums_zero t hS, add_zero]; exact le_rfl
      · show (0 : ℝ) ≤ 1; exact zero_le_one
      · exact smul_nonneg (inv_nonneg.2 (by linarith)) hy
      · obtain ⟨S', hS', rfl⟩ := PathSums_smul t _ y hS
        have := h S' hS'
        show 0 + (1 - μ)⁻¹ * S' ACode.pt ≤ 1
        have e : (m + S') ACode.pt = μ + S' ACode.pt := rfl
        have hle : μ + S' ACode.pt ≤ 1 := e ▸ this
        rw [zero_add, inv_mul_le_iff₀ (by linarith)]; linarith
    · have hμ : μ = 1 := le_antisymm hμ1 (not_lt.1 hlt)
      have hy0 : y = 0 := eq_zero_of_PathSums t hy fun S hS => by
        have := h S hS
        have e : (m + S) ACode.pt = μ + S ACode.pt := rfl
        show S ACode.pt ≤ 0
        have : μ + S ACode.pt ≤ 1 := e ▸ this
        linarith
      rw [hy0]
      refine mem_PMix_self ⟨⟨fun x => Or.inr (by rw [hmμ, hμ]), by
        show m ACode.pt ≤ 1; exact hμ1⟩, le_rfl, fun S hS => ?_⟩
      rw [PathSums_zero t hS, add_zero]; exact hμ1
  | ACode.plus K1 K2, t, m, y, hm, hy, h => by
    set m1 : W K1 → ℝ := fun x => m (Sum.inl x)
    set m2 : W K2 → ℝ := fun x => m (Sum.inr x)
    set y1 : N t → W K1 → ℝ := fun z x => y z (Sum.inl x)
    set y2 : N t → W K2 → ℝ := fun z x => y z (Sum.inr x)
    -- restriction of path sums
    let r1 : (W (ACode.plus K1 K2) → ℝ) →+ (W K1 → ℝ) :=
      { toFun := fun v x => v (Sum.inl x), map_zero' := rfl, map_add' := fun _ _ => rfl }
    let r2 : (W (ACode.plus K1 K2) → ℝ) →+ (W K2 → ℝ) :=
      { toFun := fun v x => v (Sum.inr x), map_zero' := rfl, map_add' := fun _ _ => rfl }
    have h1 : ∀ S ∈ PathSums t y1, ω K1 (m1 + S) ≤ 1 := by
      intro S hS
      rw [show y1 = fun z => r1 (y z) from rfl, PathSums_map] at hS
      obtain ⟨S0, hS0, rfl⟩ := hS
      exact le_trans (le_max_left _ _) (h S0 hS0)
    have h2 : ∀ S ∈ PathSums t y2, ω K2 (m2 + S) ≤ 1 := by
      intro S hS
      rw [show y2 = fun z => r2 (y z) from rfl, PathSums_map] at hS
      obtain ⟨S0, hS0, rfl⟩ := hS
      exact le_trans (le_max_right _ _) (h S0 hS0)
    have H1 := root_step K1 t m1 y1 (fun x => hm _) (fun z x => hy z _) h1
    have H2 := root_step K2 t m2 y2 (fun x => hm _) (fun z x => hy z _) h2
    let Ψ : ((W K1 → ℝ) × (N t → W K1 → ℝ)) × ((W K2 → ℝ) × (N t → W K2 → ℝ)) →ₗ[ℝ]
        (W (ACode.plus K1 K2) → ℝ) × (N t → W (ACode.plus K1 K2) → ℝ) :=
      { toFun := fun T => (jp T.1.1 T.2.1, fun z => jp (T.1.2 z) (T.2.2 z))
        map_add' := fun T T' => Prod.ext (funext fun x => by rcases x with x | x <;> rfl)
          (funext fun z => funext fun x => by rcases x with x | x <;> rfl)
        map_smul' := fun c T => Prod.ext (funext fun x => by rcases x with x | x <;> rfl)
          (funext fun z => funext fun x => by rcases x with x | x <;> rfl) }
    have hΨ : Ψ ((m1, y1), (m2, y2)) = (m, y) :=
      Prod.ext (funext fun x => by rcases x with x | x <;> rfl)
        (funext fun z => funext fun x => by rcases x with x | x <;> rfl)
    rw [← hΨ]
    refine PMix_image_subset Ψ ?_ (PMix_prod H1 H2)
    rintro _ ⟨⟨⟨e1, w1⟩, ⟨e2, w2⟩⟩, ⟨⟨hs1, hw1, hp1⟩, ⟨hs2, hw2, hp2⟩⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, fun z => jp_nonneg (hw1 z) (hw2 z), fun S hS => ?_⟩
    · rintro (x | x)
      · exact hs1.1 x
      · exact hs2.1 x
    · show max (ω K1 e1) (ω K2 e2) ≤ 1; exact max_le hs1.2 hs2.2
    · have hS' : S ∈ PathSums t (fun z => jpA K1 K2 (w1 z, w2 z)) := hS
      rw [PathSums_map] at hS'
      obtain ⟨T, hT, rfl⟩ := hS'
      have hT1 := PathSums_fst t _ hT
      have hT2 := PathSums_snd t _ hT
      show ω _ (jp e1 e2 + jp T.1 T.2) ≤ 1
      rw [jp_add, ω_jp]
      exact max_le (hp1 _ hT1) (hp2 _ hT2)
  | ACode.wth K1 K2, t, m, y, hm, hy, h => by
    set m1 : W K1 → ℝ := fun x => m (Sum.inl x)
    set m2 : W K2 → ℝ := fun x => m (Sum.inr x)
    set y1 : N t → W K1 → ℝ := fun z x => y z (Sum.inl x)
    set y2 : N t → W K2 → ℝ := fun z x => y z (Sum.inr x)
    have hm1 : 0 ≤ m1 := fun x => hm _
    have hm2 : 0 ≤ m2 := fun x => hm _
    set t1 := ω K1 m1
    set t2 := ω K2 m2
    have ht1 : 0 ≤ t1 := ω_nonneg K1 hm1
    have ht2 : 0 ≤ t2 := ω_nonneg K2 hm2
    have h12 : t1 + t2 ≤ 1 := by
      have := h 0 (zero_mem_PathSums t y); rw [add_zero] at this; exact this
    obtain ⟨p1, q1, hp1, hq1, hpq1, a1⟩ := absorb K1 t t1 m1 y1 hm1 (fun z x => hy z _) le_rfl
    obtain ⟨p2, q2, hp2, hq2, hpq2, a2⟩ := absorb K2 t t2 m2 y2 hm2 (fun z x => hy z _) le_rfl
    set t0 := 1 - t1 - t2
    have ht0 : 0 ≤ t0 := by simp only [t0]; linarith
    -- the joint path sums
    let Z : N t → ((W K1 → ℝ) × (W K1 → ℝ)) × ((W K2 → ℝ) × (W K2 → ℝ)) :=
      fun z => ((p1 z, q1 z), (p2 z, q2 z))
    let Q : ((W K1 → ℝ) × (W K1 → ℝ)) × ((W K2 → ℝ) × (W K2 → ℝ)) →+ (W (ACode.wth K1 K2) → ℝ) :=
      { toFun := fun T => jn T.1.2 T.2.2
        map_zero' := funext fun x => by rcases x with x | x <;> rfl
        map_add' := fun T T' => funext fun x => by rcases x with x | x <;> rfl }
    let Y : ((W K1 → ℝ) × (W K1 → ℝ)) × ((W K2 → ℝ) × (W K2 → ℝ)) →+ (W (ACode.wth K1 K2) → ℝ) :=
      { toFun := fun T => jn (T.1.1 + T.1.2) (T.2.1 + T.2.2)
        map_zero' := funext fun x => by rcases x with x | x <;> exact add_zero (0 : ℝ)
        map_add' := fun T T' => funext fun x => by
          rcases x with x | x
          · show (T + T').1.1 x + (T + T').1.2 x = (T.1.1 x + T.1.2 x) + (T'.1.1 x + T'.1.2 x)
            simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
          · show (T + T').2.1 x + (T + T').2.2 x = (T.2.1 x + T.2.2 x) + (T'.2.1 x + T'.2.2 x)
            simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring }
    have hyY : y = fun z => Y (Z z) := by
      funext z x; rcases x with x | x
      · show y z (Sum.inl x) = p1 z x + q1 z x
        exact (congrFun (congrFun hpq1 z) x).symm
      · show y z (Sum.inr x) = p2 z x + q2 z x
        exact (congrFun (congrFun hpq2 z) x).symm
    -- the remainder bound along every joint path
    have hrem : ∀ T ∈ PathSums t Z, ω K1 T.1.2 + ω K2 T.2.2 ≤ t0 := by
      intro T hT
      have hT1 := PathSums_fst t _ hT
      have hT2 := PathSums_snd t _ hT
      obtain ⟨n11, n12⟩ := PathSums_pair_nonneg t hp1 hq1 hT1
      obtain ⟨n21, n22⟩ := PathSums_pair_nonneg t hp2 hq2 hT2
      obtain ⟨-, r1⟩ := a1 _ hT1
      obtain ⟨-, r2⟩ := a2 _ hT2
      rw [max_eq_right (le_trans (le_ω_add K1 n11) (le_ω_add K1 n12))] at r1
      rw [max_eq_right (le_trans (le_ω_add K2 n21) (le_ω_add K2 n22))] at r2
      have hY : Y T ∈ PathSums t y := by rw [hyY, PathSums_map]; exact ⟨T, hT, rfl⟩
      have := h _ hY
      have e : ω (ACode.wth K1 K2) (m + Y T) =
          ω K1 (m1 + T.1.1 + T.1.2) + ω K2 (m2 + T.2.1 + T.2.2) := by
        show ω K1 (m1 + (T.1.1 + T.1.2)) + ω K2 (m2 + (T.2.1 + T.2.2)) = _
        rw [← add_assoc, ← add_assoc]
      rw [e] at this
      simp only [t0]; linarith
    -- the side components
    have side1 : 0 < t1 → t1⁻¹ • (m1, p1) ∈ PMix (RootSet K1 t) := by
      intro hpos
      have := root_step K1 t (t1⁻¹ • m1) (fun z => t1⁻¹ • p1 z)
        (smul_nonneg (inv_nonneg.2 ht1) hm1) (fun z => smul_nonneg (inv_nonneg.2 ht1) (hp1 z))
        (by
          intro S hS
          obtain ⟨S', hS', rfl⟩ := PathSums_smul t _ p1 hS
          have hS'' : S' ∈ PathSums t (fun z => AddMonoidHom.fst _ _ (p1 z, q1 z)) := hS'
          rw [PathSums_map] at hS''
          obtain ⟨T, hT, rfl⟩ := hS''
          have := (a1 T hT).1
          rw [← smul_add, ω_smul K1 _ (inv_nonneg.2 ht1)]
          calc t1⁻¹ * ω K1 (m1 + T.1) ≤ t1⁻¹ * t1 := mul_le_mul_of_nonneg_left this
                (inv_nonneg.2 ht1)
            _ = 1 := inv_mul_cancel₀ hpos.ne')
      exact this
    have side2 : 0 < t2 → t2⁻¹ • (m2, p2) ∈ PMix (RootSet K2 t) := by
      intro hpos
      have := root_step K2 t (t2⁻¹ • m2) (fun z => t2⁻¹ • p2 z)
        (smul_nonneg (inv_nonneg.2 ht2) hm2) (fun z => smul_nonneg (inv_nonneg.2 ht2) (hp2 z))
        (by
          intro S hS
          obtain ⟨S', hS', rfl⟩ := PathSums_smul t _ p2 hS
          have hS'' : S' ∈ PathSums t (fun z => AddMonoidHom.fst _ _ (p2 z, q2 z)) := hS'
          rw [PathSums_map] at hS''
          obtain ⟨T, hT, rfl⟩ := hS''
          have := (a2 T hT).1
          rw [← smul_add, ω_smul K2 _ (inv_nonneg.2 ht2)]
          calc t2⁻¹ * ω K2 (m2 + T.1) ≤ t2⁻¹ * t2 := mul_le_mul_of_nonneg_left this
                (inv_nonneg.2 ht2)
            _ = 1 := inv_mul_cancel₀ hpos.ne')
      exact this
    -- embeddings of the sides
    let E1 : (W K1 → ℝ) × (N t → W K1 → ℝ) →ₗ[ℝ]
        (W (ACode.wth K1 K2) → ℝ) × (N t → W (ACode.wth K1 K2) → ℝ) :=
      { toFun := fun T => (jn T.1 0, fun z => jn (T.2 z) 0)
        map_add' := fun T T' => Prod.ext
          (funext fun x => by rcases x with x | x; exacts [rfl, by show (0 : ℝ) = 0 + 0; simp])
          (funext fun z => funext fun x => by
            rcases x with x | x; exacts [rfl, by show (0 : ℝ) = 0 + 0; simp])
        map_smul' := fun c T => Prod.ext
          (funext fun x => by rcases x with x | x; exacts [rfl, by show (0 : ℝ) = c * 0; simp])
          (funext fun z => funext fun x => by
            rcases x with x | x; exacts [rfl, by show (0 : ℝ) = c * 0; simp]) }
    let E2 : (W K2 → ℝ) × (N t → W K2 → ℝ) →ₗ[ℝ]
        (W (ACode.wth K1 K2) → ℝ) × (N t → W (ACode.wth K1 K2) → ℝ) :=
      { toFun := fun T => (jn 0 T.1, fun z => jn 0 (T.2 z))
        map_add' := fun T T' => Prod.ext
          (funext fun x => by rcases x with x | x; exacts [by show (0 : ℝ) = 0 + 0; simp, rfl])
          (funext fun z => funext fun x => by
            rcases x with x | x; exacts [by show (0 : ℝ) = 0 + 0; simp, rfl])
        map_smul' := fun c T => Prod.ext
          (funext fun x => by rcases x with x | x; exacts [by show (0 : ℝ) = c * 0; simp, rfl])
          (funext fun z => funext fun x => by
            rcases x with x | x; exacts [by show (0 : ℝ) = c * 0; simp, rfl]) }
    have hE1 : E1 '' RootSet K1 t ⊆ RootSet (ACode.wth K1 K2) t := by
      rintro _ ⟨⟨e, w⟩, ⟨hs, hw, hp⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, fun z => jn_nonneg (hw z) le_rfl, fun S hS => ?_⟩
      · rintro (x | x)
        · exact hs.1 x
        · exact Or.inl rfl
      · show ω K1 e + ω K2 0 ≤ 1; rw [ω_zero, add_zero]; exact hs.2
      · have hS' : S ∈ PathSums t (fun z => jnA K1 K2 (w z, 0)) := hS
        rw [PathSums_map] at hS'
        obtain ⟨T, hT, rfl⟩ := hS'
        have hT2 : T.2 = 0 := PathSums_zero t (PathSums_snd t _ hT)
        show ω _ (jn e 0 + jn T.1 T.2) ≤ 1
        rw [jn_add, ω_jn, hT2, add_zero, ω_zero, add_zero]
        exact hp _ (PathSums_fst t _ hT)
    have hE2 : E2 '' RootSet K2 t ⊆ RootSet (ACode.wth K1 K2) t := by
      rintro _ ⟨⟨e, w⟩, ⟨hs, hw, hp⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, fun z => jn_nonneg le_rfl (hw z), fun S hS => ?_⟩
      · rintro (x | x)
        · exact Or.inl rfl
        · exact hs.1 x
      · show ω K1 0 + ω K2 e ≤ 1; rw [ω_zero, zero_add]; exact hs.2
      · have hS' : S ∈ PathSums t (fun z => jnA K1 K2 (0, w z)) := hS
        rw [PathSums_map] at hS'
        obtain ⟨T, hT, rfl⟩ := hS'
        have hT1 : T.1 = 0 := PathSums_zero t (PathSums_fst t _ hT)
        show ω _ (jn 0 e + jn T.1 T.2) ≤ 1
        rw [jn_add, ω_jn, hT1, add_zero, ω_zero, zero_add]
        exact hp _ (PathSums_snd t _ hT)
    -- the remainder component
    let q : N t → W (ACode.wth K1 K2) → ℝ := fun z => jn (q1 z) (q2 z)
    have hqQ : q = fun z => Q (Z z) := rfl
    have rest : 0 < t0 → ((0 : W (ACode.wth K1 K2) → ℝ), t0⁻¹ • q) ∈
        PMix (RootSet (ACode.wth K1 K2) t) := by
      intro hpos
      refine mem_PMix_self ⟨⟨fun _ => Or.inl rfl, by rw [ω_zero]; exact zero_le_one⟩,
        smul_nonneg (inv_nonneg.2 ht0) fun z => jn_nonneg (hq1 z) (hq2 z), fun S hS => ?_⟩
      obtain ⟨S', hS', rfl⟩ := PathSums_smul t _ q hS
      rw [hqQ, PathSums_map] at hS'
      obtain ⟨T, hT, rfl⟩ := hS'
      rw [zero_add, ω_smul _ _ (inv_nonneg.2 ht0)]
      have : ω (ACode.wth K1 K2) (Q T) = ω K1 T.1.2 + ω K2 T.2.2 := rfl
      rw [this]
      calc t0⁻¹ * (ω K1 T.1.2 + ω K2 T.2.2) ≤ t0⁻¹ * t0 :=
            mul_le_mul_of_nonneg_left (hrem T hT) (inv_nonneg.2 ht0)
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    -- vanishing when a weight is zero
    have z1 : t1 = 0 → (m1, p1) = 0 := by
      intro h0
      refine Prod.ext (funext fun x => le_antisymm ?_ (hm1 x)) ?_
      · exact le_trans (coord_le_ω K1 hm1 x) (le_of_eq h0)
      · refine eq_zero_of_PathSums t hp1 fun S hS => ?_
        have hS'' : S ∈ PathSums t (fun z => AddMonoidHom.fst _ _ (p1 z, q1 z)) := hS
        rw [PathSums_map] at hS''
        obtain ⟨T, hT, rfl⟩ := hS''
        have := (a1 T hT).1
        exact le_trans (ω_mono K1 fun x => le_add_of_nonneg_left (hm1 x)) (h0 ▸ this)
    have z2 : t2 = 0 → (m2, p2) = 0 := by
      intro h0
      refine Prod.ext (funext fun x => le_antisymm ?_ (hm2 x)) ?_
      · exact le_trans (coord_le_ω K2 hm2 x) (le_of_eq h0)
      · refine eq_zero_of_PathSums t hp2 fun S hS => ?_
        have hS'' : S ∈ PathSums t (fun z => AddMonoidHom.fst _ _ (p2 z, q2 z)) := hS
        rw [PathSums_map] at hS''
        obtain ⟨T, hT, rfl⟩ := hS''
        have := (a2 T hT).1
        exact le_trans (ω_mono K2 fun x => le_add_of_nonneg_left (hm2 x)) (h0 ▸ this)
    have z0 : t0 = 0 → q = 0 := by
      intro h0
      have hq1' : q1 = 0 := eq_zero_of_PathSums t hq1 fun S hS => by
        have hS'' : S ∈ PathSums t (fun z =>
            ((AddMonoidHom.snd _ _).comp (AddMonoidHom.fst _ _)) (Z z)) := hS
        rw [PathSums_map] at hS''
        obtain ⟨T, hT, rfl⟩ := hS''
        have := hrem T hT
        have h2n : 0 ≤ ω K2 T.2.2 := ω_nonneg K2
          (PathSums_pair_nonneg t hp2 hq2 (PathSums_snd t _ hT)).2
        show ω K1 T.1.2 ≤ 0; linarith
      have hq2' : q2 = 0 := eq_zero_of_PathSums t hq2 fun S hS => by
        have hS'' : S ∈ PathSums t (fun z =>
            ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _)) (Z z)) := hS
        rw [PathSums_map] at hS''
        obtain ⟨T, hT, rfl⟩ := hS''
        have := hrem T hT
        have h1n : 0 ≤ ω K1 T.1.2 := ω_nonneg K1
          (PathSums_pair_nonneg t hp1 hq1 (PathSums_fst t _ hT)).2
        show ω K2 T.2.2 ≤ 0; linarith
      funext z x; rcases x with x | x
      · exact congrFun (congrFun hq1' z) x
      · exact congrFun (congrFun hq2' z) x
    -- the mixture
    have key : (m, y) = ∑ k : Fin 3, ![t1, t2, t0] k •
        ![E1 (t1⁻¹ • (m1, p1)), E2 (t2⁻¹ • (m2, p2)), ((0 : W (ACode.wth K1 K2) → ℝ), t0⁻¹ • q)] k := by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      rw [← map_smul, ← map_smul, smul_inv_smul_of z1, smul_inv_smul_of z2]
      have hq : t0 • ((0 : W (ACode.wth K1 K2) → ℝ), t0⁻¹ • q) = (0, q) := by
        rw [Prod.smul_mk, smul_zero, smul_inv_smul_of z0]
      rw [hq]
      refine Prod.ext ?_ ?_
      · funext x; rcases x with x | x
        · show m (Sum.inl x) = m (Sum.inl x) + 0 + 0; simp
        · show m (Sum.inr x) = 0 + m (Sum.inr x) + 0; simp
      · funext z x; rcases x with x | x
        · show y z (Sum.inl x) = p1 z x + 0 + q1 z x
          rw [add_zero]; exact (congrFun (congrFun hpq1 z) x).symm
        · show y z (Sum.inr x) = 0 + p2 z x + q2 z x
          rw [zero_add]; exact (congrFun (congrFun hpq2 z) x).symm
    rw [key]
    refine PMix_bind _ _ (fun k => by fin_cases k <;> simp [ht1, ht2, ht0]) (by
      rw [Fin.sum_univ_three]; simp [t0]) (fun k hk => ?_)
    fin_cases k
    · exact PMix_image_subset E1 hE1 (side1 hk)
    · exact PMix_image_subset E2 hE2 (side2 hk)
    · exact rest hk

/-! ### The forest induction -/

/-- Assignments of stable sets to the nodes, stable along every path. -/
def Valid (t : TCode) (K : ACode) : Set (N t → W K → ℝ) :=
  {σ | (∀ x h, σ x h = 0 ∨ σ x h = 1) ∧ ∀ S ∈ PathSums t σ, IsStab K S}

theorem Valid_nonneg {t : TCode} {K : ACode} {σ : N t → W K → ℝ} (h : σ ∈ Valid t K) : 0 ≤ σ :=
  fun x k => by rcases h.1 x k with e | e <;> simp [e]

theorem IsStab_zero (K : ACode) : IsStab K 0 :=
  ⟨fun _ => Or.inl rfl, by rw [ω_zero]; exact (zero_le_one : (0 : ℝ) ≤ 1)⟩

theorem IsStab_nonneg {K : ACode} {e : W K → ℝ} (h : IsStab K e) : 0 ≤ e :=
  fun x => by rcases h.1 x with e' | e' <;> simp [e']

/-- Mixing mixtures. -/
theorem PMix_join {E : Type*} [AddCommGroup E] [Module ℝ E] {S T : Set E} (h : T ⊆ PMix S)
    {x : E} (hx : x ∈ PMix T) : x ∈ PMix S := by
  obtain ⟨ι, _, w, s, hw, hw1, hs, rfl⟩ := hx
  exact PMix_bind w s (fun i => (hw i).le) hw1 fun i _ => h (hs i)

/-- Affine images of mixtures. -/
theorem PMix_affine {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ₗ[ℝ] F) (c : F) {S : Set E} {x : E} (hx : x ∈ PMix S) :
    f x + c ∈ PMix ((fun s => f s + c) '' S) := by
  obtain ⟨ι, _, w, s, hw, hw1, hs, rfl⟩ := hx
  refine ⟨ι, inferInstance, w, fun i => f (s i) + c, hw, hw1, fun i => ⟨s i, hs i, rfl⟩, ?_⟩
  simp only [map_sum, map_smul, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw1, one_smul]

/-- Components of a mixture vanish where the mixture does. -/
theorem PMix_supp {α β : Type*} {S : Set (α → β → ℝ)} (hS : ∀ s ∈ S, 0 ≤ s) {z : α → β → ℝ}
    (hz : z ∈ PMix S) : z ∈ PMix {s | s ∈ S ∧ ∀ x h, z x h = 0 → s x h = 0} := by
  obtain ⟨ι, _, w, s, hw, hw1, hs, rfl⟩ := hz
  refine ⟨ι, inferInstance, w, s, hw, hw1, fun i => ⟨hs i, fun x h h0 => ?_⟩, rfl⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ w j * s j x h :=
    fun j _ => mul_nonneg (hw j).le (hS _ (hs j) x h)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (hw i).ne'
  · exact h1

/-- Path sums inherit supports. -/
theorem PathSums_supp {β : Type*} :
    ∀ (t : TCode) {f g : N t → β → ℝ}, 0 ≤ f → 0 ≤ g → (∀ x h, f x h ≠ 0 → g x h ≠ 0) →
      ∀ T ∈ PathSums t (fun x => (f x, g x)), ∀ h, T.1 h ≠ 0 → T.2 h ≠ 0
  | TCode.one, f, g, _, _, hfg, T, hT, h => by
    rcases hT with rfl | hT
    · intro h0; exact absurd rfl h0
    · rw [Set.mem_singleton_iff.1 hT]; exact hfg _ h
  | TCode.plus s u, f, g, hf, hg, hfg, T, hT, h => by
    rcases hT with hT | hT
    · exact PathSums_supp s (fun x => hf _) (fun x => hg _) (fun x => hfg _) T hT h
    · exact PathSums_supp u (fun x => hf _) (fun x => hg _) (fun x => hfg _) T hT h
  | TCode.cone u, f, g, hf, hg, hfg, T, hT, h => by
    rcases hT with rfl | ⟨T', hT', rfl⟩
    · intro h0; exact absurd rfl h0
    · intro hne
      have hn := PathSums_pair_nonneg u (f := fun x => f (Sum.inl x)) (g := fun x => g (Sum.inl x))
        (fun x => hf _) (fun x => hg _) hT'
      have hr1 : 0 ≤ f (root u) h := hf _ h
      have hr2 : 0 ≤ g (root u) h := hg _ h
      show g (root u) h + T'.2 h ≠ 0
      have hsum : f (root u) h + T'.1 h ≠ 0 := hne
      by_cases h1 : f (root u) h = 0
      · have h2 : T'.1 h ≠ 0 := by rwa [h1, zero_add] at hsum
        have h5 := PathSums_supp u (fun x => hf _) (fun x => hg _) (fun x => hfg _) T' hT' h h2
        have h6 : 0 < T'.2 h := lt_of_le_of_ne (hn.2 h) (Ne.symm h5)
        linarith
      · have h4 : 0 < g (root u) h := lt_of_le_of_ne hr2 (Ne.symm (hfg _ h h1))
        have h3 : (0 : ℝ) ≤ T'.2 h := hn.2 h
        linarith

/-- **Gluing a root to a subforest.** -/
theorem glue (K : ACode) (u : TCode) {e : W K → ℝ} {w σ : N u → W K → ℝ} (he : IsStab K e)
    (hw : 0 ≤ w) (hew : ∀ S ∈ PathSums u w, ω K (e + S) ≤ 1) (hσ : σ ∈ Valid u K)
    (hsupp : ∀ x h, w x h = 0 → σ x h = 0) :
    (Sum.elim σ (fun _ => e) : N (TCode.cone u) → W K → ℝ) ∈ Valid (TCode.cone u) K := by
  have hσ0 := Valid_nonneg hσ
  have he0 := IsStab_nonneg he
  refine ⟨?_, ?_⟩
  · rintro (x | x) h
    · exact hσ.1 x h
    · exact he.1 h
  · rintro S (rfl | ⟨S', hS', rfl⟩)
    · exact IsStab_zero K
    · show IsStab K (e + S')
      -- the matching path sum of `w`
      have hS'' : S' ∈ PathSums u (fun x => AddMonoidHom.fst _ _ (σ x, w x)) := hS'
      rw [PathSums_map] at hS''
      obtain ⟨T, hT, hTS⟩ := hS''
      have hS'T : S' = T.1 := hTS.symm
      rw [hS'T]
      have hsup := PathSums_supp u hσ0 hw (fun x h hne h0 => hne (hsupp x h h0)) T hT
      have hTw : T.2 ∈ PathSums u w := PathSums_snd u _ hT
      have hTσ : T.1 ∈ PathSums u σ := PathSums_fst u _ hT
      have hT2 : 0 ≤ T.2 := (PathSums_pair_nonneg u hσ0 hw hT).2
      have hstab := hσ.2 _ hTσ
      have hbound := hew _ hTw
      -- where `e` is `1`, the path sum of `σ` is `0`
      have hdisj : ∀ h, e h = 1 → T.1 h = 0 := by
        intro h he1
        by_contra hne
        have hpos : 0 < T.2 h := lt_of_le_of_ne (hT2 h) (Ne.symm (hsup h hne))
        have h7 : (e + T.2) h ≤ 1 := le_trans (coord_le_ω K (add_nonneg he0 hT2) h) hbound
        have h8 : (e + T.2) h = 1 + T.2 h := by simp only [Pi.add_apply, he1]
        linarith
      -- coherent with a point of `e`: the path sum of `σ` is `0`
      have hnb : ∀ h0 h, e h0 = 1 → h0 ≠ h → ACode.coh K h0 h → T.1 h = 0 := by
        intro h0 h he1 hne hc
        by_contra hne'
        have hpos : 0 < T.2 h := lt_of_le_of_ne (hT2 h) (Ne.symm (hsup h hne'))
        have h7 : (e + T.2) h0 + (e + T.2) h ≤ 1 :=
          le_trans (pair_le_ω K (add_nonneg he0 hT2) hne hc) hbound
        have h8 : (e + T.2) h0 = 1 + T.2 h0 := by simp only [Pi.add_apply, he1]
        have h9 : (0 : ℝ) ≤ e h := he0 h
        have h10 : (0 : ℝ) ≤ T.2 h0 := hT2 h0
        have h11 : (e + T.2) h = e h + T.2 h := rfl
        linarith
      refine ⟨fun h => ?_, ?_⟩
      · rcases he.1 h with h1 | h1
        · simp only [Pi.add_apply, h1, zero_add]; exact hstab.1 h
        · right; simp only [Pi.add_apply, h1, hdisj h h1, add_zero]
      · obtain ⟨c, hc, hω⟩ := ω_attain K (e + T.1)
        rw [hω]
        by_cases hA : ∃ h0, c h0 = 1 ∧ e h0 = 1
        · obtain ⟨h0, hc0, he0'⟩ := hA
          have : ∀ h, c h * (e + T.1) h = c h * e h := by
            intro h
            rcases hc.1 h with ch | ch
            · rw [ch, zero_mul, zero_mul]
            · by_cases hh : h0 = h
              · subst hh; simp only [Pi.add_apply, hdisj h0 he0', add_zero]
              · simp only [Pi.add_apply, hnb h0 h he0' hh (hc.2 h0 h hc0 ch), add_zero]
          rw [Finset.sum_congr rfl fun h _ => this h]
          exact le_trans (clique_le_ω K he0 c hc) he.2
        · push_neg at hA
          have : ∀ h, c h * (e + T.1) h = c h * T.1 h := by
            intro h
            rcases hc.1 h with ch | ch
            · rw [ch, zero_mul, zero_mul]
            · have : e h = 0 := (he.1 h).resolve_right (hA h ch)
              simp only [Pi.add_apply, this, zero_add]
          rw [Finset.sum_congr rfl fun h _ => this h]
          exact le_trans (clique_le_ω K (IsStab_nonneg hstab) c hc) hstab.2

/-- Stable sets of a cograph: the case of one node. -/
theorem stab_mix (K : ACode) {v : W K → ℝ} (hv : 0 ≤ v) (h : ω K v ≤ 1) :
    v ∈ PMix {e | IsStab K e} := by
  have := root_step K TCode.one v 0 hv le_rfl (fun S hS => by
    rw [PathSums_zero TCode.one hS, add_zero]; exact h)
  have := PMix_map (LinearMap.fst ℝ _ _) this
  exact PMix_mono (by rintro _ ⟨p, hp, rfl⟩; exact hp.1) this

/-- **The decomposition.** -/
theorem main : ∀ (t : TCode) (K : ACode) (z : N t → W K → ℝ), 0 ≤ z →
    (∀ S ∈ PathSums t z, ω K S ≤ 1) → z ∈ PMix (Valid t K)
  | TCode.one, K, z, hz, h => by
    have hv := stab_mix K (hz ACode.pt) (h _ (Set.mem_insert_of_mem _ rfl))
    let f : (W K → ℝ) →ₗ[ℝ] (N TCode.one → W K → ℝ) :=
      { toFun := fun v _ => v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hzf : z = f (z ACode.pt) := funext fun x => by rw [ACode.eq_pt x]; rfl
    rw [hzf]
    refine PMix_image_subset f ?_ hv
    rintro _ ⟨e, he, rfl⟩
    refine ⟨fun _ h => he.1 h, ?_⟩
    rintro S (rfl | hS)
    · exact IsStab_zero K
    · rw [Set.mem_singleton_iff.1 hS]; exact he
  | TCode.plus s u, K, z, hz, h => by
    have H1 := main s K (fun x => z (Sum.inl x)) (fun x => hz _) (fun S hS => h S (Or.inl hS))
    have H2 := main u K (fun x => z (Sum.inr x)) (fun x => hz _) (fun S hS => h S (Or.inr hS))
    let f : (N s → W K → ℝ) × (N u → W K → ℝ) →ₗ[ℝ] (N (TCode.plus s u) → W K → ℝ) :=
      { toFun := fun p => Sum.elim p.1 p.2
        map_add' := fun p p' => funext fun x => by rcases x with x | x <;> rfl
        map_smul' := fun c p => funext fun x => by rcases x with x | x <;> rfl }
    have hzf : z = f (fun x => z (Sum.inl x), fun x => z (Sum.inr x)) :=
      funext fun x => by rcases x with x | x <;> rfl
    rw [hzf]
    refine PMix_image_subset f ?_ (PMix_prod H1 H2)
    rintro _ ⟨⟨σ1, σ2⟩, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro (x | x) k
      · exact h1.1 x k
      · exact h2.1 x k
    · rintro S (hS | hS)
      · exact h1.2 S hS
      · exact h2.2 S hS
  | TCode.cone u, K, z, hz, h => by
    set m := z (root u)
    set y : N u → W K → ℝ := fun x => z (Sum.inl x)
    have hroot := root_step K u m y (hz _) (fun x => hz _) (fun S hS =>
      h _ (Set.mem_insert_of_mem _ ⟨S, hS, rfl⟩))
    let Λ : (W K → ℝ) × (N u → W K → ℝ) →ₗ[ℝ] (N (TCode.cone u) → W K → ℝ) :=
      { toFun := fun p => Sum.elim p.2 (fun _ => p.1)
        map_add' := fun p p' => funext fun x => by rcases x with x | x <;> rfl
        map_smul' := fun c p => funext fun x => by rcases x with x | x <;> rfl }
    have hzΛ : z = Λ (m, y) := funext fun x => by
      rcases x with x | x
      · rfl
      · show z (Sum.inr x) = m; rw [ACode.eq_pt x]; rfl
    rw [hzΛ]
    refine PMix_join ?_ (PMix_map Λ hroot)
    rintro _ ⟨⟨e, w⟩, ⟨he, hw, hew⟩, rfl⟩
    have hw' := main u K w hw (fun S hS => le_trans
      (ω_mono K fun k => le_add_of_nonneg_left (IsStab_nonneg he k)) (hew S hS))
    have hw'' := PMix_supp (fun s hs => Valid_nonneg hs) hw'
    let L : (N u → W K → ℝ) →ₗ[ℝ] (N (TCode.cone u) → W K → ℝ) :=
      { toFun := fun σ => Sum.elim σ 0
        map_add' := fun σ σ' => funext fun x => by
          rcases x with x | x; exacts [rfl, by funext k; show (0 : ℝ) = 0 + 0; simp]
        map_smul' := fun c σ => funext fun x => by
          rcases x with x | x; exacts [rfl, by funext k; show (0 : ℝ) = c * 0; simp] }
    let c0 : N (TCode.cone u) → W K → ℝ := Sum.elim 0 (fun _ => e)
    have hΛ : Λ (e, w) = L w + c0 := funext fun x => by
      rcases x with x | x
      · funext k; show w x k = w x k + 0; rw [add_zero]
      · funext k; show e k = 0 + e k; rw [zero_add]
    rw [hΛ]
    refine PMix_mono ?_ (PMix_affine L c0 hw'')
    rintro _ ⟨σ, ⟨hσ, hsupp⟩, rfl⟩
    show L σ + c0 ∈ Valid (TCode.cone u) K
    have : L σ + c0 = Sum.elim σ (fun _ => e) := funext fun x => by
      rcases x with x | x
      · funext k; show σ x k + 0 = σ x k; rw [add_zero]
      · funext k; show 0 + e k = e k; rw [zero_add]
    rw [this]
    exact glue K u he hw hew hσ hsupp

end ConstructiveProb.Cograph
