/-
# Minimal and maximal axiomatizations of the calculus

A set `Λ` of affine laws valid on the certain states `S` *determines* the calculus when every set
that contains `S`, is closed under mixtures and satisfies the laws in `Λ` is `Mix S`. This holds
exactly when the solutions of `Λ` are `Mix S` (`determines_iff`). The laws valid on `S` form the
largest such set (`validLaws_maximal`, `determines_validLaws`), and the property is upward closed
(`determines_mono`).

On a finite frame `LowerSet P`, normalization, modularity and monotonicity across the covering
`Iio p ≤ Iic p` at each point `p` already give monotonicity, so the function is a valuation
(`monotone_of_rmass_nonneg`, `toValuationR`). The law at a point `p` that has a point `q < p`
below it cannot be dropped, even among nonnegative functions (`local_axiom_needed`). At a minimal
point it says `f {p} ≥ 0`.

At the second-order type `T` over `Bool` the deterministic hull satisfies the clique laws, which
cut out the PCS (`tD_eq_QSTAB`), and eight laws of CHSH type (`recipe_satisfies_laws`). Each law
for a maximal clique and each CHSH-type law is independent of all the others
(`clique_law_needed`, `chsh_law_needed`). The PCS violates every CHSH-type law. That these laws
cut out exactly the deterministic hull is checked by an exact polytope computation, not here.
-/
import ConstructiveProb.Uniqueness
import ConstructiveProb.PCSGraph

open scoped ENNReal
open Finset

namespace ConstructiveProb

/-! ### The interval of determining axiom sets -/

section Interval

variable {E : Type*} [Fintype E]

/-- The functions that satisfy every law in `Λ`. -/
def Sol (Λ : Set (AffineLaw E)) : Set (E → ℝ≥0∞) := {x | ∀ L ∈ Λ, L.Holds x}

/-- The laws valid on every certain state. -/
def ValidLaws (S : Set (E → ℝ≥0∞)) : Set (AffineLaw E) := {L | ∀ s ∈ S, L.Holds s}

/-- `Λ` *determines the calculus*: every set that contains the certain states, is closed under
mixtures and satisfies the laws in `Λ` is `Mix S`. -/
def Determines (S : Set (E → ℝ≥0∞)) (Λ : Set (AffineLaw E)) : Prop :=
  ∀ C : Set (E → ℝ≥0∞), S ⊆ C → Mix C ⊆ C → (∀ L ∈ Λ, ∀ x ∈ C, L.Holds x) → C = Mix S

omit [Fintype E] in
theorem mix_subset_of_closed {S C : Set (E → ℝ≥0∞)} (hSC : S ⊆ C) (hconv : Mix C ⊆ C) :
    Mix S ⊆ C := by
  rintro x ⟨n, w, s, hs, hw, rfl⟩
  exact hconv ⟨n, w, s, fun i => hSC (hs i), hw, rfl⟩

theorem Sol_mix_closed (Λ : Set (AffineLaw E)) : Mix (Sol Λ) ⊆ Sol Λ :=
  fun _ hx L hL => L.holds_of_Mix (S := Sol Λ) (fun _ hs => hs L hL) hx

theorem mix_subset_Sol {S : Set (E → ℝ≥0∞)} {Λ : Set (AffineLaw E)} (hΛ : Λ ⊆ ValidLaws S) :
    Mix S ⊆ Sol Λ :=
  fun _ hx L hL => L.holds_of_Mix (hΛ hL) hx

/-- **Determining axiom sets.** A set of laws valid on the certain states determines the
calculus iff its solutions are exactly the calculus. -/
theorem determines_iff {S : Set (E → ℝ≥0∞)} {Λ : Set (AffineLaw E)} (hΛ : Λ ⊆ ValidLaws S) :
    Determines S Λ ↔ Sol Λ = Mix S := by
  constructor
  · intro h
    exact h (Sol Λ) (fun s hs L hL => hΛ hL s hs) (Sol_mix_closed Λ) fun L hL x hx => hx L hL
  · intro h C hSC hconv hC
    refine le_antisymm (fun x hx => ?_) (mix_subset_of_closed hSC hconv)
    rw [← h]
    exact fun L hL => hC L hL x hx

/-- **Existence.** Some set containing the certain states, closed under mixtures and satisfying
`Λ` exists iff every law in `Λ` is valid on the certain states. -/
theorem exists_extension_iff {S : Set (E → ℝ≥0∞)} {Λ : Set (AffineLaw E)} :
    (∃ C : Set (E → ℝ≥0∞), S ⊆ C ∧ Mix C ⊆ C ∧ ∀ L ∈ Λ, ∀ x ∈ C, L.Holds x) ↔
      Λ ⊆ ValidLaws S := by
  constructor
  · rintro ⟨C, hSC, -, hC⟩ L hL s hs
    exact hC L hL s (hSC hs)
  · intro hΛ
    exact ⟨Mix S, (calculus_conditions (S := S)).1, (Mix_Mix S).le,
      fun L hL x hx => mix_subset_Sol hΛ hx L hL⟩

/-- **Existence and uniqueness.** The extension satisfying `Λ` exists and is unique iff every law
in `Λ` is valid on the certain states and the solutions of `Λ` are exactly the calculus. -/
theorem existsUnique_extension_iff {S : Set (E → ℝ≥0∞)} {Λ : Set (AffineLaw E)} :
    (∃! C : Set (E → ℝ≥0∞), S ⊆ C ∧ Mix C ⊆ C ∧ ∀ L ∈ Λ, ∀ x ∈ C, L.Holds x) ↔
      Λ ⊆ ValidLaws S ∧ Sol Λ = Mix S := by
  constructor
  · rintro ⟨C, hC, huniq⟩
    have hΛ : Λ ⊆ ValidLaws S := exists_extension_iff.1 ⟨C, hC⟩
    refine ⟨hΛ, ?_⟩
    have h1 := huniq (Sol Λ) ⟨fun s hs L hL => hΛ hL s hs, Sol_mix_closed Λ,
      fun L hL x hx => hx L hL⟩
    have h2 := huniq (Mix S) ⟨(calculus_conditions (S := S)).1, (Mix_Mix S).le,
      fun L hL x hx => mix_subset_Sol hΛ hx L hL⟩
    rw [h1, h2]
  · rintro ⟨hΛ, hsol⟩
    obtain ⟨C, hC⟩ := exists_extension_iff.2 hΛ
    refine ⟨Mix S, ⟨(calculus_conditions (S := S)).1, (Mix_Mix S).le,
      fun L hL x hx => mix_subset_Sol hΛ hx L hL⟩, fun C' hC' => ?_⟩
    exact (determines_iff hΛ).2 hsol C' hC'.1 hC'.2.1 hC'.2.2

/-- **The largest axiom set.** A set of laws whose solutions contain the certain states consists
of laws valid on them. -/
theorem validLaws_maximal {S : Set (E → ℝ≥0∞)} {Λ : Set (AffineLaw E)} (h : S ⊆ Sol Λ) :
    Λ ⊆ ValidLaws S :=
  fun L hL _ hs => h hs L hL

/-- The valid laws determine the calculus (completeness). -/
theorem determines_validLaws {S : Set (E → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s) :
    Determines S (ValidLaws S) := by
  rw [determines_iff le_rfl, Mix_eq_laws' hS]
  rfl

/-- **Upward closure.** Adding valid laws to a determining set keeps it determining. -/
theorem determines_mono {S : Set (E → ℝ≥0∞)} {Λ Λ' : Set (AffineLaw E)} (h : Λ ⊆ Λ')
    (hΛ' : Λ' ⊆ ValidLaws S) (hd : Determines S Λ) : Determines S Λ' := by
  rw [determines_iff (h.trans hΛ')] at hd
  rw [determines_iff hΛ']
  refine le_antisymm (fun x hx => ?_) (mix_subset_Sol hΛ')
  rw [← hd]
  exact fun L hL => hx L (h hL)

/-! #### Finite values

Some laws are satisfied trivially by infinite values (`x a ≤ x b` holds whenever `x b = ⊤`), so
an extension is taken to consist of functions with finite values, as every element of `Mix S`
has when `S` consists of `{0,1}`-valued functions. -/

/-- The functions with finite values. -/
def FinVal : Set (E → ℝ≥0∞) := {x | ∀ e, x e ≠ ⊤}

omit [Fintype E] in
theorem Mix_finVal {S : Set (E → ℝ≥0∞)} (hS : S ⊆ FinVal) : Mix S ⊆ FinVal := by
  rintro x ⟨n, w, s, hs, hw, rfl⟩ e
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top ?_ (hS (hs i) e)
  have : w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i)
  rw [hw] at this
  exact ne_top_of_le_ne_top ENNReal.one_ne_top this

omit [Fintype E] in
theorem sharp_finVal {S : Set (E → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s) : S ⊆ FinVal :=
  fun s hs e => by rcases hS s hs e with h | h <;> simp [h]

/-- **Existence and uniqueness, with finite values.** For `{0,1}`-valued certain states, exactly
one set of finite-valued functions contains them, is closed under mixtures and satisfies `Λ` iff
every law in `Λ` is valid on them and the finite-valued solutions of `Λ` are exactly the
calculus. -/
theorem existsUnique_finExtension_iff {S : Set (E → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s)
    {Λ : Set (AffineLaw E)} :
    (∃! C : Set (E → ℝ≥0∞), C ⊆ FinVal ∧ S ⊆ C ∧ Mix C ⊆ C ∧ ∀ L ∈ Λ, ∀ x ∈ C, L.Holds x) ↔
      Λ ⊆ ValidLaws S ∧ FinVal ∩ Sol Λ = Mix S := by
  have hMfin : Mix S ⊆ FinVal := Mix_finVal (sharp_finVal hS)
  have hext : Λ ⊆ ValidLaws S →
      Mix S ⊆ FinVal ∧ S ⊆ Mix S ∧ Mix (Mix S) ⊆ Mix S ∧
        ∀ L ∈ Λ, ∀ x ∈ Mix S, L.Holds x := fun hΛ =>
    ⟨hMfin, (calculus_conditions (S := S)).1, (Mix_Mix S).le,
      fun L hL x hx => mix_subset_Sol hΛ hx L hL⟩
  have hsol : Λ ⊆ ValidLaws S →
      FinVal ∩ Sol Λ ⊆ FinVal ∧ S ⊆ FinVal ∩ Sol Λ ∧ Mix (FinVal ∩ Sol Λ) ⊆ FinVal ∩ Sol Λ ∧
        ∀ L ∈ Λ, ∀ x ∈ FinVal ∩ Sol Λ, L.Holds x := fun hΛ =>
    ⟨Set.inter_subset_left, fun s hs => ⟨sharp_finVal hS hs, fun L hL => hΛ hL s hs⟩,
      fun x hx => ⟨Mix_finVal Set.inter_subset_left hx,
        Sol_mix_closed Λ (by
          obtain ⟨n, w, s, hs, hw, rfl⟩ := hx
          exact ⟨n, w, s, fun i => (hs i).2, hw, rfl⟩)⟩,
      fun L hL x hx => hx.2 L hL⟩
  constructor
  · rintro ⟨C, ⟨-, hSC, -, hC⟩, huniq⟩
    have hΛ : Λ ⊆ ValidLaws S := fun L hL s hs => hC L hL s (hSC hs)
    refine ⟨hΛ, ?_⟩
    rw [huniq _ (hsol hΛ), huniq _ (hext hΛ)]
  · rintro ⟨hΛ, hsolEq⟩
    refine ⟨Mix S, hext hΛ, fun C ⟨hCfin, hSC, hconv, hC⟩ => ?_⟩
    refine le_antisymm (fun x hx => ?_) (mix_subset_of_closed hSC hconv)
    rw [← hsolEq]
    exact ⟨hCfin hx, fun L hL => hC L hL x hx⟩

/-- The valid laws give exactly one finite-valued extension. -/
theorem existsUnique_finExtension_validLaws {S : Set (E → ℝ≥0∞)}
    (hS : ∀ s ∈ S, IsSharpVec s) :
    ∃! C : Set (E → ℝ≥0∞), C ⊆ FinVal ∧ S ⊆ C ∧ Mix C ⊆ C ∧
      ∀ L ∈ ValidLaws S, ∀ x ∈ C, L.Holds x := by
  refine (existsUnique_finExtension_iff hS).2 ⟨le_rfl, ?_⟩
  rw [(determines_iff le_rfl).1 (determines_validLaws hS)]
  exact Set.inter_eq_right.2 (Mix_finVal (sharp_finVal hS))

/-- **Upward closure, with finite values.** -/
theorem existsUnique_finExtension_mono {S : Set (E → ℝ≥0∞)} (hS : ∀ s ∈ S, IsSharpVec s)
    {Λ Λ' : Set (AffineLaw E)} (h : Λ ⊆ Λ') (hΛ' : Λ' ⊆ ValidLaws S)
    (hd : ∃! C : Set (E → ℝ≥0∞), C ⊆ FinVal ∧ S ⊆ C ∧ Mix C ⊆ C ∧
      ∀ L ∈ Λ, ∀ x ∈ C, L.Holds x) :
    ∃! C : Set (E → ℝ≥0∞), C ⊆ FinVal ∧ S ⊆ C ∧ Mix C ⊆ C ∧
      ∀ L ∈ Λ', ∀ x ∈ C, L.Holds x := by
  obtain ⟨-, hsol⟩ := (existsUnique_finExtension_iff hS).1 hd
  refine (existsUnique_finExtension_iff hS).2 ⟨hΛ', le_antisymm (fun x hx => ?_) ?_⟩
  · rw [← hsol]; exact ⟨hx.1, fun L hL => hx.2 L (h hL)⟩
  · exact fun x hx => ⟨Mix_finVal (sharp_finVal hS) hx, mix_subset_Sol hΛ' hx⟩

end Interval

/-! ### Finite frames: monotonicity is needed only at the points -/

section Frames

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P]

/-- The mass of a real-valued function on the lower sets at a point. -/
noncomputable def rmass (f : LowerSet P → ℝ) (p : P) : ℝ :=
  f (LowerSet.Iic p) - f (LowerSet.Iio p)

/-- Modularity of a real-valued function on the lower sets. -/
def IsModularR (f : LowerSet P → ℝ) : Prop :=
  ∀ U V : LowerSet P, f (U ⊔ V) + f (U ⊓ V) = f U + f V

omit [Fintype P] [DecidableEq P] in
theorem rmass_step {f : LowerSet P → ℝ} (hmod : IsModularR f) {U : LowerSet P} {p : P}
    (hp : p ∈ U) (hmax : ∀ b ∈ U, p ≤ b → b = p) : f U = f (U.erase p) + rmass f p := by
  have h := hmod (U.erase p) (LowerSet.Iic p)
  rw [LowerSet.erase_sup_Iic hp hmax, LowerSet.erase_inf_Iic hp] at h
  unfold rmass
  linarith

/-- **Representation by masses.** A real-valued modular function vanishing at `⊥` is the sum of
its masses over each lower set. -/
theorem eq_sum_rmass {f : LowerSet P → ℝ} (h0 : f ⊥ = 0) (hmod : IsModularR f)
    (U : LowerSet P) : f U = ∑ p ∈ U.toFinset, rmass f p := by
  suffices h : ∀ n (U : LowerSet P), U.toFinset.card = n →
      f U = ∑ p ∈ U.toFinset, rmass f p from h _ U rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro U hcard
    rcases eq_or_ne U ⊥ with rfl | hUne
    · have hbot : (⊥ : LowerSet P).toFinset = ∅ := by simp [LowerSet.toFinset]
      rw [hbot, Finset.sum_empty, h0]
    · have hne : (↑U : Set P).Nonempty := Set.nonempty_iff_ne_empty.mpr fun h =>
        hUne (SetLike.coe_injective (h.trans LowerSet.coe_bot.symm))
      obtain ⟨p, hpmax⟩ := (↑U : Set P).toFinite.exists_maximal hne
      have hp : p ∈ U := hpmax.1
      have hmax : ∀ b ∈ U, p ≤ b → b = p := fun b hb hpb => le_antisymm (hpmax.2 hb hpb) hpb
      have hfin : (U.erase p).toFinset = U.toFinset.erase p :=
        LowerSet.toFinset_erase_of_max hmax
      have hcard' : (U.erase p).toFinset.card < n := by
        rw [hfin, ← hcard]; exact Finset.card_erase_lt_of_mem (LowerSet.mem_toFinset.mpr hp)
      rw [rmass_step hmod hp hmax, IH _ hcard' (U.erase p) rfl, hfin]
      exact Finset.sum_erase_add U.toFinset (rmass f) (LowerSet.mem_toFinset.mpr hp)

/-- **Local monotonicity suffices.** A real-valued function on a finite frame that vanishes at
`⊥`, is modular, and is monotone across each covering `Iio p ≤ Iic p` is monotone. -/
theorem monotone_of_rmass_nonneg {f : LowerSet P → ℝ} (h0 : f ⊥ = 0) (hmod : IsModularR f)
    (hloc : ∀ p, f (LowerSet.Iio p) ≤ f (LowerSet.Iic p)) : Monotone f := by
  intro U V hUV
  rw [eq_sum_rmass h0 hmod U, eq_sum_rmass h0 hmod V]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun p _ _ => ?_
  · rw [LowerSet.mem_toFinset] at hq ⊢
    exact LowerSet.coe_subset_coe.2 hUV hq
  · have := hloc p
    unfold rmass
    linarith

/-- **The local axioms give a valuation.** -/
noncomputable def toValuationR {f : LowerSet P → ℝ} (h0 : f ⊥ = 0) (h1 : f ⊤ = 1)
    (hmod : IsModularR f) (hloc : ∀ p, f (LowerSet.Iio p) ≤ f (LowerSet.Iic p)) :
    Valuation (LowerSet P) where
  toFun U := ENNReal.ofReal (f U)
  map_bot' := by simp [h0]
  map_top' := by simp [h1]
  mono' _ _ h := ENNReal.ofReal_le_ofReal (monotone_of_rmass_nonneg h0 hmod hloc h)
  modular' U V := by
    have hnn : ∀ W : LowerSet P, 0 ≤ f W := fun W => by
      have := monotone_of_rmass_nonneg h0 hmod hloc (bot_le (a := W))
      rwa [h0] at this
    rw [← ENNReal.ofReal_add (hnn U) (hnn V), ← ENNReal.ofReal_add (hnn _) (hnn _), hmod U V]

@[simp] theorem toValuationR_apply {f : LowerSet P → ℝ} (h0 : f ⊥ = 0) (h1 : f ⊤ = 1)
    (hmod : IsModularR f) (hloc : ∀ p, f (LowerSet.Iio p) ≤ f (LowerSet.Iic p))
    (U : LowerSet P) : toValuationR h0 h1 hmod hloc U = ENNReal.ofReal (f U) := rfl

/-- The sum of a weight over a lower set. -/
noncomputable def sumOver (m : P → ℝ) (U : LowerSet P) : ℝ := ∑ r ∈ U.toFinset, m r

theorem toFinset_sup (U V : LowerSet P) : (U ⊔ V).toFinset = U.toFinset ∪ V.toFinset := by
  ext q; simp [LowerSet.mem_toFinset]

theorem toFinset_inf (U V : LowerSet P) : (U ⊓ V).toFinset = U.toFinset ∩ V.toFinset := by
  ext q; simp [LowerSet.mem_toFinset]

theorem sumOver_modular (m : P → ℝ) : IsModularR (sumOver m) := by
  intro U V
  unfold sumOver
  rw [toFinset_sup, toFinset_inf]
  exact Finset.sum_union_inter

omit [DecidableEq P] in
theorem sumOver_bot (m : P → ℝ) : sumOver m ⊥ = 0 := by
  have hbot : (⊥ : LowerSet P).toFinset = ∅ := by simp [LowerSet.toFinset]
  simp [sumOver, hbot]

omit [DecidableEq P] in
theorem sumOver_top (m : P → ℝ) : sumOver m ⊤ = ∑ r, m r := by
  have htop : (⊤ : LowerSet P).toFinset = Finset.univ := by
    ext q; simp [LowerSet.mem_toFinset]
  simp [sumOver, htop]

theorem sumOver_Iic (m : P → ℝ) (r : P) :
    sumOver m (LowerSet.Iic r) = sumOver m (LowerSet.Iio r) + m r := by
  have h : (LowerSet.Iic r).toFinset = insert r (LowerSet.Iio r).toFinset := by
    ext q; simp [LowerSet.mem_toFinset, le_iff_eq_or_lt]
  have hr : r ∉ (LowerSet.Iio r).toFinset := by simp [LowerSet.mem_toFinset]
  unfold sumOver
  rw [h, Finset.sum_insert hr, add_comm]

/-- **Each local axiom with a point below it is needed.** For `q < p` there is a nonnegative,
normalized, modular function that is monotone across every covering except the one at `p`, and
is not monotone. -/
theorem local_axiom_needed {p q : P} (hqp : q < p) :
    ∃ f : LowerSet P → ℝ, f ⊥ = 0 ∧ f ⊤ = 1 ∧ IsModularR f ∧ (∀ U, 0 ≤ f U) ∧
      (∀ r, r ≠ p → f (LowerSet.Iio r) ≤ f (LowerSet.Iic r)) ∧ ¬ Monotone f := by
  classical
  have hpq : p ≠ q := hqp.ne'
  set m : P → ℝ := fun r => if r = p then -1 else if r = q then 2 else 0 with hm
  have hsplit : ∀ r, m r = (if r = p then (-1 : ℝ) else 0) + (if r = q then 2 else 0) := by
    intro r
    simp only [hm]
    by_cases h1 : r = p
    · subst h1; simp [hpq]
    · simp [h1]
  have hsum : ∀ U : LowerSet P, sumOver m U =
      (if p ∈ U then (-1 : ℝ) else 0) + (if q ∈ U then 2 else 0) := by
    intro U
    unfold sumOver
    rw [Finset.sum_congr rfl fun r _ => hsplit r, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp [LowerSet.mem_toFinset]
  refine ⟨sumOver m, sumOver_bot m, ?_, sumOver_modular m, fun U => ?_, fun r hr => ?_,
    fun hmono => ?_⟩
  · rw [hsum]
    simp only [LowerSet.mem_top, if_true]
    norm_num
  · rw [hsum]
    by_cases hp : p ∈ U
    · have hq : q ∈ U := U.lower hqp.le hp
      simp [hp, hq]
    · by_cases hq : q ∈ U <;> simp [hp, hq]
  · rw [sumOver_Iic]
    have : 0 ≤ m r := by
      simp only [hm, if_neg hr]
      split_ifs <;> norm_num
    linarith
  · have h := hmono (show LowerSet.Iio p ≤ LowerSet.Iic p from fun x hx => le_of_lt hx)
    rw [sumOver_Iic] at h
    have : m p = -1 := by simp [hm]
    linarith

/-- **The frame axioms, in `[0, ∞]`.** A finite-valued function on a finite frame satisfies
normalization, modularity and monotonicity across each covering `Iio p ≤ Iic p` iff it is a
valuation. -/
theorem frame_axioms_iff {x : LowerSet P → ℝ≥0∞} (hfin : ∀ U, x U ≠ ⊤) :
    (x ⊥ = 0 ∧ x ⊤ = 1 ∧ (∀ U V, x U + x V = x (U ⊔ V) + x (U ⊓ V)) ∧
        ∀ p, x (LowerSet.Iio p) ≤ x (LowerSet.Iic p)) ↔
      ∃ v : Valuation (LowerSet P), v.toFun = x := by
  constructor
  · rintro ⟨h0, h1, hmod, hloc⟩
    have h0' : (x ⊥).toReal = 0 := by simp [h0]
    have h1' : (x ⊤).toReal = 1 := by simp [h1]
    have hmod' : IsModularR fun U => (x U).toReal := fun U V => by
      simp only
      rw [← ENNReal.toReal_add (hfin _) (hfin _), ← ENNReal.toReal_add (hfin _) (hfin _),
        hmod U V]
    have hloc' : ∀ p, (x (LowerSet.Iio p)).toReal ≤ (x (LowerSet.Iic p)).toReal :=
      fun p => ENNReal.toReal_mono (hfin _) (hloc p)
    refine ⟨toValuationR h0' h1' hmod' hloc', funext fun U => ?_⟩
    exact ENNReal.ofReal_toReal (hfin U)
  · rintro ⟨v, rfl⟩
    exact ⟨v.map_bot', v.map_top', v.modular', fun p => v.mono' fun q hq => le_of_lt hq⟩

/-- **Dropping a local axiom loses uniqueness.** For `q < p` some finite-valued function on the
frame satisfies normalization, modularity and the local axioms at all points other than `p`,
and is not a valuation. -/
theorem frame_axiom_needed {p q : P} (hqp : q < p) :
    ∃ x : LowerSet P → ℝ≥0∞, (∀ U, x U ≠ ⊤) ∧ x ⊥ = 0 ∧ x ⊤ = 1 ∧
      (∀ U V, x U + x V = x (U ⊔ V) + x (U ⊓ V)) ∧
      (∀ r, r ≠ p → x (LowerSet.Iio r) ≤ x (LowerSet.Iic r)) ∧
      ¬ ∃ v : Valuation (LowerSet P), v.toFun = x := by
  obtain ⟨f, h0, h1, hmod, hnn, hloc, hnot⟩ := local_axiom_needed hqp
  refine ⟨fun U => ENNReal.ofReal (f U), fun U => ENNReal.ofReal_ne_top, by simp [h0],
    by simp [h1], fun U V => ?_, fun r hr => ENNReal.ofReal_le_ofReal (hloc r hr), ?_⟩
  · rw [← ENNReal.ofReal_add (hnn U) (hnn V), ← ENNReal.ofReal_add (hnn _) (hnn _), hmod U V]
  · rintro ⟨v, hv⟩
    apply hnot
    intro U V hUV
    have h := v.mono' hUV
    rw [hv] at h
    exact (ENNReal.ofReal_le_ofReal_iff (hnn V)).1 h

end Frames

/-! ### The second-order type over `Bool` -/

section SecondOrder

open ConstructiveProb.Graph ConstructiveProb.PCS.General

/-- The web of `T` over `Bool`. A point `((x, a), (y, b))` records `f x = a` and `g y = b`. -/
abbrev W4 := (Bool × Bool) × (Bool × Bool)

/-- Exclusivity on the web of `T` over `Bool`. -/
abbrev exclB : W4 → W4 → Prop := excl (X := Bool) (Y := Bool) (X' := Bool) (Y' := Bool)

instance (s t : W4) : Decidable (exclB s t) := by
  unfold exclB excl cp2 cp; infer_instance

/-- The support of a Popescu–Rohrlich box relabelled by `α β γ`: the events with
`a ⊕ b = (x ⊕ α)(y ⊕ β) ⊕ γ`. -/
def chshSupp (α β γ : Bool) : Finset W4 :=
  Finset.univ.filter fun e => (e.1.2 ^^ e.2.2) = (((e.1.1 ^^ α) && (e.2.1 ^^ β)) ^^ γ)

/-- No three points of a CHSH support are pairwise non-exclusive. -/
theorem chsh_no_three : ∀ α β γ : Bool, ∀ a ∈ chshSupp α β γ, ∀ b ∈ chshSupp α β γ,
    ∀ c ∈ chshSupp α β γ, a ≠ b → a ≠ c → b ≠ c → exclB a b ∨ exclB a c ∨ exclB b c := by
  decide

theorem stable_inter_chsh_card {I : Finset W4} (hI : IsStableG exclB I) (α β γ : Bool) :
    (chshSupp α β γ ∩ I).card ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 h
  rw [Finset.mem_inter] at ha hb hc
  rcases chsh_no_three α β γ a ha.1 b hb.1 c hc.1 hab hac hbc with h | h | h
  · exact hI a ha.2 b hb.2 h
  · exact hI a ha.2 c hc.2 h
  · exact hI b hb.2 c hc.2 h

/-- **The CHSH-type laws hold on the stable set polytope.** -/
theorem stab_chsh_le {x : W4 → ℝ≥0∞} (hx : x ∈ STAB exclB) (α β γ : Bool) :
    ∑ e ∈ chshSupp α β γ, x e ≤ 2 :=
  stab_sum_le (adj := exclB) hx _ 2 fun I hI => by exact_mod_cast stable_inter_chsh_card hI α β γ

/-- **The deterministic hull satisfies the clique laws and the CHSH-type laws.** -/
theorem recipe_satisfies_laws {x : W4 → ℝ≥0∞}
    (hx : x ∈ Mix {z | z ∈ tD Bool Bool Bool Bool ∧ ∀ u, z u = 0 ∨ z u = 1}) :
    (∀ C, IsCliqueG exclB C → ∑ e ∈ C, x e ≤ 1) ∧
      ∀ α β γ, ∑ e ∈ chshSupp α β γ, x e ≤ 2 := by
  rw [recipe_eq_STAB] at hx
  exact ⟨stab_subset_qstab (adj := exclB) hx, stab_chsh_le hx⟩

/-- A constant weight on a finite set. -/
noncomputable def cInd (c : ℝ≥0∞) (A : Finset W4) : W4 → ℝ≥0∞ := fun e => if e ∈ A then c else 0

theorem sum_cInd (c : ℝ≥0∞) (A C : Finset W4) :
    ∑ e ∈ C, cInd c A e = c * (C ∩ A).card := by
  unfold cInd
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- A pentagon inside each CHSH support. -/
def wit : Bool → Bool → Bool → Finset W4
  | false, false, false => {((false, false), (false, false)), ((false, false), (true, false)),
      ((false, true), (false, true)), ((true, false), (true, true)), ((true, true), (false, true))}
  | false, false, true => {((false, false), (false, true)), ((false, false), (true, true)),
      ((false, true), (false, false)), ((true, false), (true, false)), ((true, true), (false, false))}
  | false, true, false => {((false, false), (false, false)), ((false, false), (true, false)),
      ((false, true), (false, true)), ((true, false), (false, true)), ((true, true), (true, true))}
  | false, true, true => {((false, false), (false, true)), ((false, false), (true, true)),
      ((false, true), (false, false)), ((true, false), (false, false)), ((true, true), (true, false))}
  | true, false, false => {((false, false), (false, false)), ((false, false), (true, true)),
      ((false, true), (false, true)), ((true, false), (true, false)), ((true, true), (false, true))}
  | true, false, true => {((false, false), (false, true)), ((false, false), (true, false)),
      ((false, true), (false, false)), ((true, false), (true, true)), ((true, true), (false, false))}
  | true, true, false => {((false, false), (false, true)), ((false, false), (true, false)),
      ((false, true), (false, false)), ((true, false), (false, false)), ((true, true), (true, true))}
  | true, true, true => {((false, false), (false, false)), ((false, false), (true, true)),
      ((false, true), (false, true)), ((true, false), (false, true)), ((true, true), (true, false))}

theorem wit_sub : ∀ α β γ : Bool, wit α β γ ⊆ chshSupp α β γ := by decide

theorem wit_card : ∀ α β γ : Bool, (wit α β γ).card = 5 := by decide

/-- The pentagon has no three pairwise exclusive points. -/
theorem wit_no_triangle : ∀ α β γ : Bool, ∀ a ∈ wit α β γ, ∀ b ∈ wit α β γ, ∀ c ∈ wit α β γ,
    a ≠ b → a ≠ c → b ≠ c → ¬ (exclB a b ∧ exclB a c ∧ exclB b c) := by
  decide

/-- The pentagon of one support meets every other support in at most four points. -/
theorem wit_other : ∀ α β γ α' β' γ' : Bool, (α', β', γ') ≠ (α, β, γ) →
    (chshSupp α' β' γ' ∩ wit α β γ).card ≤ 4 := by
  decide

theorem two_inv_mul_four : (2 : ℝ≥0∞)⁻¹ * 4 = 2 := by
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ← mul_assoc,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- **Each CHSH-type law is independent of the other laws.** The pentagon inside its support lies
in the PCS, so it satisfies every clique law, satisfies the other seven CHSH-type laws, and
violates this one. -/
theorem chsh_law_needed (α β γ : Bool) : ∃ x ∈ tD Bool Bool Bool Bool,
    (∀ C, IsCliqueG exclB C → ∑ e ∈ C, x e ≤ 1) ∧
    (∀ α' β' γ' : Bool, (α', β', γ') ≠ (α, β, γ) → ∑ e ∈ chshSupp α' β' γ', x e ≤ 2) ∧
    2 < ∑ e ∈ chshSupp α β γ, x e := by
  have hq : ∀ C, IsCliqueG exclB C → ∑ e ∈ C, cInd 2⁻¹ (wit α β γ) e ≤ 1 := by
    intro C hC
    rw [sum_cInd]
    have hcard : (C ∩ wit α β γ).card ≤ 2 := by
      by_contra h
      push Not at h
      obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 h
      rw [Finset.mem_inter] at ha hb hc
      exact wit_no_triangle α β γ a ha.2 b hb.2 c hc.2 hab hac hbc
        ⟨hC a ha.1 b hb.1 hab, hC a ha.1 c hc.1 hac, hC b hb.1 c hc.1 hbc⟩
    calc (2 : ℝ≥0∞)⁻¹ * ((C ∩ wit α β γ).card : ℝ≥0∞) ≤ 2⁻¹ * 2 := by
          gcongr; exact_mod_cast hcard
      _ = 1 := ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  refine ⟨cInd 2⁻¹ (wit α β γ), ?_, hq, fun α' β' γ' hne => ?_, ?_⟩
  · rw [tD_eq_QSTAB]; exact hq
  · rw [sum_cInd]
    calc (2 : ℝ≥0∞)⁻¹ * ((chshSupp α' β' γ' ∩ wit α β γ).card : ℝ≥0∞) ≤ 2⁻¹ * 4 := by
          gcongr; exact_mod_cast wit_other α β γ α' β' γ' hne
      _ = 2 := two_inv_mul_four
  · rw [sum_cInd, Finset.inter_eq_right.2 (wit_sub α β γ), wit_card]
    calc (2 : ℝ≥0∞) = 2⁻¹ * 4 := two_inv_mul_four.symm
      _ < 2⁻¹ * ((5 : ℕ) : ℝ≥0∞) := ENNReal.mul_lt_mul_right (by simp) (by simp) (by norm_num)

/-- The maximal clique of a pair of total functions: its events are the input–output pairs the
two functions produce. -/
def cliq (f g : Bool → Bool) : Finset W4 :=
  Finset.univ.filter fun e => f e.1.1 = e.1.2 ∧ g e.2.1 = e.2.2

theorem cliq_card : ∀ f g : Bool → Bool, (cliq f g).card = 4 := by decide

theorem cliq_isClique : ∀ f g : Bool → Bool, IsCliqueG exclB (cliq f g) := by
  unfold IsCliqueG; decide

/-- Every point outside the clique is not exclusive with some point of it. -/
theorem cliq_maximal : ∀ f g : Bool → Bool, ∀ v : W4, v ∉ cliq f g →
    ∃ u ∈ cliq f g, ¬ exclB u v := by
  decide

/-- A deterministic pair wins at most three of the four rounds of each CHSH game. -/
theorem cliq_chsh : ∀ f g : Bool → Bool, ∀ α β γ : Bool,
    (chshSupp α β γ ∩ cliq f g).card ≤ 3 := by
  decide

theorem three_inv_mul_three : (3 : ℝ≥0∞)⁻¹ * 3 = 1 :=
  ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top

/-- **Each maximal clique law is independent of the other laws.** The weight `1/3` on the clique
satisfies the law of every other clique and every CHSH-type law, and violates this one. -/
theorem clique_law_needed (f g : Bool → Bool) : ∃ x : W4 → ℝ≥0∞,
    (∀ C, IsCliqueG exclB C → C ≠ cliq f g → ∑ e ∈ C, x e ≤ 1) ∧
    (∀ α β γ : Bool, ∑ e ∈ chshSupp α β γ, x e ≤ 2) ∧
    1 < ∑ e ∈ cliq f g, x e := by
  refine ⟨cInd 3⁻¹ (cliq f g), fun C hC hne => ?_, fun α β γ => ?_, ?_⟩
  · rw [sum_cInd]
    have hcard : (C ∩ cliq f g).card ≤ 3 := by
      by_contra h
      push Not at h
      have h4 : (C ∩ cliq f g).card = (cliq f g).card := by
        have := Finset.card_le_card (Finset.inter_subset_right (s₁ := C) (s₂ := cliq f g))
        rw [cliq_card] at this ⊢
        omega
      have hsub : cliq f g ⊆ C := by
        have := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁ := C)
          (s₂ := cliq f g)) h4.ge
        rw [← this]; exact Finset.inter_subset_left
      apply hne
      refine Finset.Subset.antisymm (fun v hv => ?_) hsub
      by_contra hvK
      obtain ⟨u, hu, hnu⟩ := cliq_maximal f g v hvK
      exact hnu (hC u (hsub hu) v hv fun h => hvK (h ▸ hu))
    calc (3 : ℝ≥0∞)⁻¹ * ((C ∩ cliq f g).card : ℝ≥0∞) ≤ 3⁻¹ * 3 := by
          gcongr; exact_mod_cast hcard
      _ = 1 := three_inv_mul_three
  · rw [sum_cInd]
    calc (3 : ℝ≥0∞)⁻¹ * ((chshSupp α β γ ∩ cliq f g).card : ℝ≥0∞) ≤ 3⁻¹ * 3 := by
          gcongr; exact_mod_cast cliq_chsh f g α β γ
      _ = 1 := three_inv_mul_three
      _ ≤ 2 := by norm_num
  · rw [sum_cInd, Finset.inter_self, cliq_card]
    calc (1 : ℝ≥0∞) = 3⁻¹ * 3 := three_inv_mul_three.symm
      _ < 3⁻¹ * ((4 : ℕ) : ℝ≥0∞) := ENNReal.mul_lt_mul_right (by simp) (by simp) (by norm_num)

/-- **The PCS violates every CHSH-type law.** -/
theorem tD_violates_chsh (α β γ : Bool) :
    ∃ x ∈ tD Bool Bool Bool Bool, 2 < ∑ e ∈ chshSupp α β γ, x e := by
  obtain ⟨x, hx, -, -, h⟩ := chsh_law_needed α β γ
  exact ⟨x, hx, h⟩

end SecondOrder

end ConstructiveProb
