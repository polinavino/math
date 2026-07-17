/-
# Product freedom beyond rigid frames: Fubini fails for discontinuous valuations

`ProductRigidity.lean` shows that on the chain product `LowerSet (ℕ × ℕ)` the product
valuation is unique: rectangle data pins everything down.  This file shows that the rigidity
is a property of that frame, not of the theory.  On the powerset frame `Set (ℕ × ℕ)` — a
frame whose opens are *not* finite unions of rectangles — the product valuation is **not**
determined by its rectangle data, and the failure is exactly a failure of Fubini.

The witnesses are ultrafilter couplings.  For an ultrafilter `𝒲` on `ι`, the indicator
`A ↦ if A ∈ 𝒲 then 1 else 0` is a valuation on `Set ι` (`ultrafilterValuation`): modularity
in the only nontrivial case is precisely the ultrafilter dichotomy.  Any ultrafilter on a
product splits rectangles through its marginals, so with `𝒰` the hyperfilter (a free
ultrafilter on `ℕ`) the three couplings

* `tensorL 𝒰 𝒰` — iterate `𝒰` left-then-right,
* `tensorR 𝒰 𝒰` — iterate `𝒰` right-then-left,
* `diagUF 𝒰`    — push `𝒰` forward along the diagonal,

all have marginals `(𝒰, 𝒰)`, hence *identical* values on every rectangle `S ×ˢ T`, namely the
product `[S ∈ 𝒰] · [T ∈ 𝒰]` (`tensorL_prod_apply`, `tensorR_prod_apply`,
`diagUF_prod_apply`).  But on the upper triangle `{(m, m') | m < m'}` the left iteration gives
`1` while the right iteration and the diagonal give `0`: the two iterated "integrals" of the
same product data disagree (`fubini_fails_for_valuations`), and the product valuation is not
unique (`product_valuation_not_unique`).

Two readings.  For the monad question: the multiplication genuinely has freedom for
discontinuous valuations — no canonical product exists on frames rich enough to see a
triangle — so any monad structure must either restrict the frames (rigidity), restrict the
valuations (continuity, or the countably-presented fragment of `CountableMix.lean`), or make
a choice.  For the mathematics: on the powerset frame our valuations are finitely additive
probability charges, and non-uniqueness of products in the finitely additive setting is,
we believe, classical (theory-of-charges literature; verify a citation before claiming this
in prose).  What this file contributes is the mechanization, in valuation form, with the
Fubini reading made explicit.
-/
import ConstructiveProb.Basic

open scoped ENNReal
open Filter

namespace ConstructiveProb

variable {ι : Type*}

/-! ### The 0-1 valuation of an ultrafilter -/

open scoped Classical in
/-- **The indicator of an ultrafilter is a valuation on the powerset frame.**  Modularity in
the both-out case is exactly the ultrafilter dichotomy (`Ultrafilter.union_mem_iff`). -/
noncomputable def ultrafilterValuation (W : Ultrafilter ι) : Valuation (Set ι) where
  toFun A := if A ∈ W then 1 else 0
  map_bot' := by
    have h : (⊥ : Set ι) ∉ W := W.empty_notMem
    rw [if_neg h]
  map_top' := by
    have h : (⊤ : Set ι) ∈ W := Filter.univ_mem
    rw [if_pos h]
  mono' A B hAB := by
    change (if A ∈ W then (1 : ℝ≥0∞) else 0) ≤ if B ∈ W then 1 else 0
    split_ifs with hA hB hB
    · exact le_rfl
    · exact absurd (Filter.mem_of_superset hA hAB) hB
    · exact zero_le
    · exact le_rfl
  modular' A B := by
    change (if A ∈ W then (1 : ℝ≥0∞) else 0) + (if B ∈ W then 1 else 0)
      = (if A ∪ B ∈ W then 1 else 0) + (if A ∩ B ∈ W then 1 else 0)
    by_cases hA : A ∈ W <;> by_cases hB : B ∈ W
    · rw [if_pos hA, if_pos hB,
        if_pos (show A ∪ B ∈ W from Filter.mem_of_superset hA Set.subset_union_left),
        if_pos (show A ∩ B ∈ W from Filter.inter_mem hA hB)]
    · rw [if_pos hA, if_neg hB,
        if_pos (show A ∪ B ∈ W from Filter.mem_of_superset hA Set.subset_union_left),
        if_neg (show A ∩ B ∉ W from
          fun h => hB (Filter.mem_of_superset h Set.inter_subset_right))]
    · rw [if_neg hA, if_pos hB,
        if_pos (show A ∪ B ∈ W from Filter.mem_of_superset hB Set.subset_union_right),
        if_neg (show A ∩ B ∉ W from
          fun h => hA (Filter.mem_of_superset h Set.inter_subset_left)), zero_add, add_zero]
    · rw [if_neg hA, if_neg hB,
        if_neg (show A ∪ B ∉ W from fun h => ((W.union_mem_iff).mp h).elim hA hB),
        if_neg (show A ∩ B ∉ W from
          fun h => hA (Filter.mem_of_superset h Set.inter_subset_left))]

open scoped Classical in
@[simp] theorem ultrafilterValuation_apply (W : Ultrafilter ι) (A : Set ι) :
    ultrafilterValuation W A = if A ∈ W then 1 else 0 := rfl

/-! ### Three couplings of a free ultrafilter with itself -/

/-- Left iteration: choose the first coordinate along `U`, then the second along `V`. -/
noncomputable def tensorL (U V : Ultrafilter ℕ) : Ultrafilter (ℕ × ℕ) :=
  U.bind fun m => V.map fun m' => (m, m')

/-- Right iteration: choose the second coordinate along `V`, then the first along `U`. -/
noncomputable def tensorR (U V : Ultrafilter ℕ) : Ultrafilter (ℕ × ℕ) :=
  V.bind fun m' => U.map fun m => (m, m')

/-- The diagonal coupling: push `U` forward along `n ↦ (n, n)`. -/
noncomputable def diagUF (U : Ultrafilter ℕ) : Ultrafilter (ℕ × ℕ) :=
  U.map fun n => (n, n)

theorem mem_tensorL {U V : Ultrafilter ℕ} {A : Set (ℕ × ℕ)} :
    A ∈ tensorL U V ↔ {m | {m' | (m, m') ∈ A} ∈ V} ∈ U := by
  change A ∈ Filter.bind (U : Filter ℕ)
      (fun m => ((V.map fun m' => (m, m')) : Filter (ℕ × ℕ))) ↔ _
  rw [Filter.mem_bind']
  simp only [Ultrafilter.mem_coe, Ultrafilter.mem_map]
  rfl

theorem mem_tensorR {U V : Ultrafilter ℕ} {A : Set (ℕ × ℕ)} :
    A ∈ tensorR U V ↔ {m' | {m | (m, m') ∈ A} ∈ U} ∈ V := by
  change A ∈ Filter.bind (V : Filter ℕ)
      (fun m' => ((U.map fun m => (m, m')) : Filter (ℕ × ℕ))) ↔ _
  rw [Filter.mem_bind']
  simp only [Ultrafilter.mem_coe, Ultrafilter.mem_map]
  rfl

theorem mem_diagUF {U : Ultrafilter ℕ} {A : Set (ℕ × ℕ)} :
    A ∈ diagUF U ↔ {n | (n, n) ∈ A} ∈ U :=
  Ultrafilter.mem_map

/-! ### All three couplings have the same rectangle data -/

/-- **Every ultrafilter on a product splits rectangles through its marginals**: membership of
`S ×ˢ T` is decided by the two pushforward ultrafilters.  This is why 0-1 couplings hide
their dependence structure from rectangle queries. -/
theorem rect_mem_iff {α β : Type*} {W : Ultrafilter (α × β)} {S : Set α} {T : Set β} :
    S ×ˢ T ∈ W ↔ S ∈ W.map Prod.fst ∧ T ∈ W.map Prod.snd := by
  rw [Ultrafilter.mem_map, Ultrafilter.mem_map, Set.prod_eq]
  constructor
  · intro h
    exact ⟨Filter.mem_of_superset h Set.inter_subset_left,
      Filter.mem_of_superset h Set.inter_subset_right⟩
  · rintro ⟨h1, h2⟩
    exact Filter.inter_mem h1 h2

theorem tensorL_rect {U V : Ultrafilter ℕ} {S T : Set ℕ} :
    S ×ˢ T ∈ tensorL U V ↔ S ∈ U ∧ T ∈ V := by
  rw [mem_tensorL]
  have hset : {m | {m' | (m, m') ∈ S ×ˢ T} ∈ V} = {m | m ∈ S ∧ T ∈ V} := by
    ext m
    by_cases hm : m ∈ S
    · have : {m' | (m, m') ∈ S ×ˢ T} = T := by ext m'; simp [Set.mem_prod, hm]
      simp [hm]
    · have : {m' | (m, m') ∈ S ×ˢ T} = ∅ := by ext m'; simp [Set.mem_prod, hm]
      simp [hm, V.empty_notMem]
  rw [hset]
  by_cases hT : T ∈ V
  · have : {m | m ∈ S ∧ T ∈ V} = S := by ext m; simp [hT]
    rw [this]
    simp [hT]
  · have : {m | m ∈ S ∧ T ∈ V} = ∅ := by ext m; simp [hT]
    rw [this]
    simp [hT, U.empty_notMem]

theorem tensorR_rect {U V : Ultrafilter ℕ} {S T : Set ℕ} :
    S ×ˢ T ∈ tensorR U V ↔ S ∈ U ∧ T ∈ V := by
  rw [mem_tensorR]
  have hset : {m' | {m | (m, m') ∈ S ×ˢ T} ∈ U} = {m' | m' ∈ T ∧ S ∈ U} := by
    ext m'
    by_cases hm : m' ∈ T
    · have : {m | (m, m') ∈ S ×ˢ T} = S := by ext m; simp [Set.mem_prod, hm]
      simp [hm]
    · have : {m | (m, m') ∈ S ×ˢ T} = ∅ := by ext m; simp [Set.mem_prod, hm]
      simp [hm, U.empty_notMem]
  rw [hset]
  by_cases hS : S ∈ U
  · have : {m' | m' ∈ T ∧ S ∈ U} = T := by ext m'; simp [hS]
    rw [this]
    simp [hS]
  · have : {m' | m' ∈ T ∧ S ∈ U} = ∅ := by ext m'; simp [hS]
    rw [this]
    simp [hS, V.empty_notMem]

theorem diagUF_rect {U : Ultrafilter ℕ} {S T : Set ℕ} :
    S ×ˢ T ∈ diagUF U ↔ S ∈ U ∧ T ∈ U := by
  rw [mem_diagUF]
  have hd : {n | (n, n) ∈ S ×ˢ T} = S ∩ T := rfl
  rw [hd]
  constructor
  · intro h
    exact ⟨Filter.mem_of_superset h Set.inter_subset_left,
      Filter.mem_of_superset h Set.inter_subset_right⟩
  · rintro ⟨hS, hT⟩
    exact Filter.inter_mem hS hT

/-- The left tensor restricts on rectangles to the product of the marginal valuations. -/
theorem tensorL_prod_apply (U V : Ultrafilter ℕ) (S T : Set ℕ) :
    ultrafilterValuation (tensorL U V) (S ×ˢ T)
      = ultrafilterValuation U S * ultrafilterValuation V T := by
  by_cases hS : S ∈ U <;> by_cases hT : T ∈ V <;>
    simp [tensorL_rect, hS, hT]

theorem tensorR_prod_apply (U V : Ultrafilter ℕ) (S T : Set ℕ) :
    ultrafilterValuation (tensorR U V) (S ×ˢ T)
      = ultrafilterValuation U S * ultrafilterValuation V T := by
  by_cases hS : S ∈ U <;> by_cases hT : T ∈ V <;>
    simp [tensorR_rect, hS, hT]

theorem diagUF_prod_apply (U : Ultrafilter ℕ) (S T : Set ℕ) :
    ultrafilterValuation (diagUF U) (S ×ˢ T)
      = ultrafilterValuation U S * ultrafilterValuation U T := by
  by_cases hS : S ∈ U <;> by_cases hT : T ∈ U <;>
    simp [diagUF_rect, hS, hT]

/-! ### The couplings differ on the upper triangle -/

/-- The upper triangle, an "open" of the product frame that is no finite union of
rectangles. -/
def upperTriangle : Set (ℕ × ℕ) := {p | p.1 < p.2}

theorem upperTriangle_mem_tensorL :
    upperTriangle ∈ tensorL (hyperfilter ℕ) (hyperfilter ℕ) := by
  rw [mem_tensorL]
  have hall : ∀ m : ℕ, {m' | (m, m') ∈ upperTriangle} ∈ hyperfilter ℕ := by
    intro m
    have : {m' : ℕ | (m, m') ∈ upperTriangle} = (Set.Iic m)ᶜ := by
      ext m'
      simp only [upperTriangle, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Iic, not_le]
    rw [this]
    exact (Set.finite_Iic m).compl_mem_hyperfilter
  have : {m | {m' | (m, m') ∈ upperTriangle} ∈ hyperfilter ℕ} = Set.univ :=
    Set.eq_univ_of_forall hall
  rw [this]
  exact Filter.univ_mem

theorem upperTriangle_notMem_tensorR :
    upperTriangle ∉ tensorR (hyperfilter ℕ) (hyperfilter ℕ) := by
  rw [mem_tensorR]
  have hnone : ∀ m' : ℕ, {m | (m, m') ∈ upperTriangle} ∉ hyperfilter ℕ := by
    intro m'
    have : {m : ℕ | (m, m') ∈ upperTriangle} = Set.Iio m' := rfl
    rw [this]
    exact (Set.finite_Iio m').notMem_hyperfilter
  have : {m' | {m | (m, m') ∈ upperTriangle} ∈ hyperfilter ℕ} = (∅ : Set ℕ) := by
    ext m'
    simp [hnone m']
  rw [this]
  exact (hyperfilter ℕ).empty_notMem

theorem upperTriangle_notMem_diagUF :
    upperTriangle ∉ diagUF (hyperfilter ℕ) := by
  rw [mem_diagUF]
  have : {n : ℕ | (n, n) ∈ upperTriangle} = (∅ : Set ℕ) := by
    ext n
    simp [upperTriangle]
  rw [this]
  exact (hyperfilter ℕ).empty_notMem

/-! ### The headline theorems -/

/-- The two iteration orders give genuinely different valuations. -/
theorem tensorL_valuation_ne_tensorR :
    ultrafilterValuation (tensorL (hyperfilter ℕ) (hyperfilter ℕ))
      ≠ ultrafilterValuation (tensorR (hyperfilter ℕ) (hyperfilter ℕ)) := by
  intro h
  have h1 : (1 : ℝ≥0∞) = 0 := by
    calc (1 : ℝ≥0∞)
        = ultrafilterValuation (tensorL (hyperfilter ℕ) (hyperfilter ℕ)) upperTriangle := by
          rw [ultrafilterValuation_apply, if_pos upperTriangle_mem_tensorL]
      _ = ultrafilterValuation (tensorR (hyperfilter ℕ) (hyperfilter ℕ)) upperTriangle := by
          rw [h]
      _ = 0 := by
          rw [ultrafilterValuation_apply, if_neg upperTriangle_notMem_tensorR]
  exact one_ne_zero h1

/-- **Product valuations are not unique on the powerset frame.**  Two valuations on
`Set (ℕ × ℕ)` agree on every rectangle yet differ.  Contrast `Valuation.product_unique`
on the chain product: rectangle rigidity is a property of that frame, not of the theory. -/
theorem product_valuation_not_unique :
    ∃ u u' : Valuation (Set (ℕ × ℕ)),
      (∀ S T : Set ℕ, u (S ×ˢ T) = u' (S ×ˢ T)) ∧ u ≠ u' :=
  ⟨ultrafilterValuation (tensorL (hyperfilter ℕ) (hyperfilter ℕ)),
   ultrafilterValuation (tensorR (hyperfilter ℕ) (hyperfilter ℕ)),
   fun S T => by rw [tensorL_prod_apply, tensorR_prod_apply],
   tensorL_valuation_ne_tensorR⟩

/-- **Fubini fails for discontinuous valuations.**  There are marginal valuations `v, w` and
two product valuations for them, the two orders of iterated integration, that disagree.  By
Kock's correspondence between commutative monads and Fubini theorems, this is the concrete
obstruction to a canonical commutative monad structure on unrestricted valuations. -/
theorem fubini_fails_for_valuations :
    ∃ (v w : Valuation (Set ℕ)) (u u' : Valuation (Set (ℕ × ℕ))),
      (∀ S T : Set ℕ, u (S ×ˢ T) = v S * w T) ∧
      (∀ S T : Set ℕ, u' (S ×ˢ T) = v S * w T) ∧ u ≠ u' :=
  ⟨ultrafilterValuation (hyperfilter ℕ), ultrafilterValuation (hyperfilter ℕ),
   ultrafilterValuation (tensorL (hyperfilter ℕ) (hyperfilter ℕ)),
   ultrafilterValuation (tensorR (hyperfilter ℕ) (hyperfilter ℕ)),
   tensorL_prod_apply _ _, tensorR_prod_apply _ _,
   tensorL_valuation_ne_tensorR⟩

end ConstructiveProb
