/-
# Product rigidity on chain products: Fubini-uniqueness without continuity

The monad question for valuations (see the paper's conclusion) reduces, at its first
nontrivial layer, to *products*: given valuations `v, w` on two frames, is a valuation `u` on
the product frame with `u (A ×ˢ B) = v A * w B` determined by that constraint?  For
Scott-continuous valuations the answer is classical (the probabilistic-powerdomain line);
without continuity one might expect freedom — diffuse mass "at infinity" choosing between
different infinities of the product.

**This file proves the opposite for chain products.**  The frame `LowerSet (ℕ × ℕ)` is
*rigid*: every lower set of `ℕ × ℕ` is a **finite** union of rectangles
(`exists_rect_decomposition`) — column heights are antitone, and an antitone map out of `ℕ`
is a finite step function.  Consequently two valuations agreeing on rectangles agree
everywhere (`eq_of_forall_prod_eq`), by the inclusion–exclusion *equality* of
`InclusionExclusion.lean`: the value of a finite union of rectangles is a signed sum of values
of rectangles (meets of rectangles are rectangles, `LowerSet.prod_inf_prod`).  In particular
the product valuation, whenever it exists, is **unique** (`Valuation.product_unique`) — no
Scott continuity required.

So on `ω × ω` there is no room for a non-canonical product: the diffuse part cannot choose an
infinity, because the poset's lower sets detect only finitely much of the boundary.  Where
product *non*-uniqueness — hence genuine multiplication freedom for a would-be monad — can
occur, if anywhere, is on frames whose opens are not finitely rectangle-generated; that
remains open, and the categorical question upstream of it is harder still (the Jung–Tix
problem, already in the continuous additive setting).
-/
import ConstructiveProb.InclusionExclusion
import Mathlib.Order.UpperLower.Prod

open scoped ENNReal

namespace ConstructiveProb

/-! ### Rows and full columns of a lower set of `ℕ × ℕ` -/

/-- The `n`-th row of `W`, as a lower set of `ℕ`. -/
def _root_.LowerSet.row (W : LowerSet (ℕ × ℕ)) (n : ℕ) : LowerSet ℕ :=
  ⟨{m | (m, n) ∈ W}, fun _ _ hle hm => W.lower (Prod.mk_le_mk.mpr ⟨hle, le_rfl⟩) hm⟩

@[simp] theorem _root_.LowerSet.mem_row {W : LowerSet (ℕ × ℕ)} {m n : ℕ} :
    m ∈ W.row n ↔ (m, n) ∈ W := Iff.rfl

/-- The set of full columns of `W`, as a lower set of `ℕ`. -/
def _root_.LowerSet.fullCols (W : LowerSet (ℕ × ℕ)) : LowerSet ℕ :=
  ⟨{m | ∀ n, (m, n) ∈ W},
   fun _ _ hle hm n => W.lower (Prod.mk_le_mk.mpr ⟨hle, le_rfl⟩) (hm n)⟩

@[simp] theorem _root_.LowerSet.mem_fullCols {W : LowerSet (ℕ × ℕ)} {m : ℕ} :
    m ∈ W.fullCols ↔ ∀ n, (m, n) ∈ W := Iff.rfl

/-! ### The structure theorem: lower sets of `ℕ × ℕ` are finite unions of rectangles -/

/-- **Chain products are finitely rectangle-generated.**  Every lower set of `ℕ × ℕ` is a
finite union of rectangles `A ×ˢ B`.  The decomposition: the full columns contribute
`fullCols ×ˢ ⊤`, and beyond the stabilization height every occupied column is full, so
finitely many rows `row n ×ˢ Iic n` account for the rest. -/
theorem exists_rect_decomposition (W : LowerSet (ℕ × ℕ)) :
    ∃ (N : ℕ) (A B : ℕ → LowerSet ℕ),
      W = (Finset.range N).sup fun i => A i ×ˢ B i := by
  classical
  by_cases htop : W.fullCols = ⊤
  · -- all columns full: `W = ⊤ = ⊤ ×ˢ ⊤`
    refine ⟨1, fun _ => ⊤, fun _ => ⊤, ?_⟩
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← LowerSet.coe_subset_coe]
      rintro ⟨m, n⟩ -
      have hm : m ∈ W.fullCols := by rw [htop]; exact Set.mem_univ m
      exact LowerSet.mem_fullCols.mp hm n
    rw [hW, Finset.range_one, Finset.sup_singleton, LowerSet.top_prod_top]
  · -- some column `m₀` misses height `b`
    have hex : ∃ m₀ b, (m₀, b) ∉ W := by
      by_contra hall
      refine htop (eq_top_iff.mpr ?_)
      rw [← LowerSet.coe_subset_coe]
      intro m _
      refine LowerSet.mem_fullCols.mpr fun n => ?_
      by_contra hmn
      exact hall ⟨m, n, hmn⟩
    obtain ⟨m₀, b, hm₀b⟩ := hex
    -- rows at height ≥ b live strictly left of m₀
    have hrow_bound : ∀ n, b ≤ n → ∀ m, (m, n) ∈ W → m < m₀ := by
      intro n hbn m hm
      by_contra hge
      exact hm₀b (W.lower (Prod.mk_le_mk.mpr ⟨not_lt.mp hge, hbn⟩) hm)
    -- for each non-full column, a height it misses
    let miss : ℕ → ℕ := fun m =>
      if h : ∀ n, (m, n) ∈ W then 0 else Classical.choose (not_forall.mp h)
    have hmiss : ∀ m, m ∉ W.fullCols → (m, miss m) ∉ W := by
      intro m hm
      have h : ¬ ∀ n, (m, n) ∈ W := fun h => hm (LowerSet.mem_fullCols.mpr h)
      have heq : miss m = Classical.choose (not_forall.mp h) := dif_neg h
      rw [heq]
      exact Classical.choose_spec (not_forall.mp h)
    set N : ℕ := max b ((Finset.range m₀).sup miss) with hN
    -- beyond height N, occupied columns are full
    have hstab : ∀ n, N < n → ∀ m, (m, n) ∈ W → m ∈ W.fullCols := by
      intro n hn m hm
      by_contra hnf
      have hmlt : m < m₀ := hrow_bound n (le_trans (le_max_left _ _) hn.le) m hm
      have hle : miss m ≤ N :=
        le_trans (Finset.le_sup (Finset.mem_range.mpr hmlt)) (le_max_right _ _)
      exact hmiss m hnf (W.lower (Prod.mk_le_mk.mpr ⟨le_rfl, le_trans hle hn.le⟩) hm)
    -- the decomposition: index 0 ↦ fullCols ×ˢ ⊤, index k+1 ↦ row k ×ˢ Iic k
    refine ⟨N + 2,
      fun i => match i with | 0 => W.fullCols | (k + 1) => W.row k,
      fun i => match i with | 0 => ⊤ | (k + 1) => LowerSet.Iic k, ?_⟩
    apply le_antisymm
    · rw [← LowerSet.coe_subset_coe]
      rintro ⟨m, n⟩ hmn
      rcases Nat.lt_or_ge n (N + 1) with hle | hlt
      · -- low rows: land in the (n+1)-st rectangle
        have hterm : (W.row n ×ˢ LowerSet.Iic n : LowerSet (ℕ × ℕ)) ≤
            (Finset.range (N + 2)).sup fun i =>
              (match i with | 0 => W.fullCols | (k + 1) => W.row k) ×ˢ
              (match i with | 0 => (⊤ : LowerSet ℕ) | (k + 1) => LowerSet.Iic k) :=
          Finset.le_sup (f := fun i =>
              (match i with | 0 => W.fullCols | (k + 1) => W.row k) ×ˢ
              (match i with | 0 => (⊤ : LowerSet ℕ) | (k + 1) => LowerSet.Iic k))
            (Finset.mem_range.mpr (by omega : n + 1 < N + 2))
        exact LowerSet.coe_subset_coe.2 hterm (LowerSet.mem_prod.mpr ⟨hmn, by simp [LowerSet.Iic]⟩)
      · -- high rows: the column is full, land in the 0-th rectangle
        have hterm : (W.fullCols ×ˢ (⊤ : LowerSet ℕ) : LowerSet (ℕ × ℕ)) ≤
            (Finset.range (N + 2)).sup fun i =>
              (match i with | 0 => W.fullCols | (k + 1) => W.row k) ×ˢ
              (match i with | 0 => (⊤ : LowerSet ℕ) | (k + 1) => LowerSet.Iic k) :=
          Finset.le_sup (f := fun i =>
              (match i with | 0 => W.fullCols | (k + 1) => W.row k) ×ˢ
              (match i with | 0 => (⊤ : LowerSet ℕ) | (k + 1) => LowerSet.Iic k))
            (Finset.mem_range.mpr (by omega : 0 < N + 2))
        exact LowerSet.coe_subset_coe.2 hterm
          (LowerSet.mem_prod.mpr ⟨hstab n hlt m hmn, Set.mem_univ n⟩)
    · -- every rectangle is inside W
      refine Finset.sup_le fun i _ => ?_
      rw [← LowerSet.coe_subset_coe]
      match i with
      | 0 =>
        rintro ⟨m, n⟩ hmn
        exact (LowerSet.mem_prod.mp hmn).1 n
      | (k + 1) =>
        rintro ⟨m, n⟩ hmn
        obtain ⟨hrow, hIic⟩ := LowerSet.mem_prod.mp hmn
        exact W.lower (Prod.mk_le_mk.mpr ⟨le_rfl, hIic⟩) hrow

/-! ### Rigidity: rectangle values determine the valuation -/

/-- A nonempty finite meet of rectangles is a rectangle of the meets. -/
theorem _root_.Finset.Nonempty.inf_prod {ι : Type*} {T : Finset ι} (hT : T.Nonempty)
    (A B : ι → LowerSet ℕ) :
    (T.inf fun i => A i ×ˢ B i) = T.inf A ×ˢ T.inf B := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i T hi hT IH =>
    rw [Finset.inf_cons, Finset.inf_cons, Finset.inf_cons, IH,
      LowerSet.prod_inf_prod]

/-- **Product rigidity.**  Two valuations on `LowerSet (ℕ × ℕ)` that agree on all rectangles
`A ×ˢ B` are equal.  Proof: decompose any lower set as a finite union of rectangles
(`exists_rect_decomposition`); by the inclusion–exclusion *equality*
(`Valuation.inclusion_exclusion`), its value is determined by values at meets of rectangles,
which are rectangles.  No Scott continuity is used. -/
theorem Valuation.eq_of_forall_prod_eq
    (u u' : Valuation (LowerSet (ℕ × ℕ)))
    (h : ∀ A B : LowerSet ℕ, u (A ×ˢ B) = u' (A ×ˢ B)) : u = u' := by
  ext W
  obtain ⟨N, A, B, rfl⟩ := exists_rect_decomposition W
  refine Valuation.eq_on_finsetSup_of_eq_on
    (G := {r | ∃ A' B' : LowerSet ℕ, r = A' ×ˢ B'}) ?_ u u' ?_ _ _ ?_
  · rintro g ⟨gA, gB, rfl⟩ g' ⟨gA', gB', rfl⟩
    exact ⟨gA ⊓ gA', gB ⊓ gB', LowerSet.prod_inf_prod gA gA' gB gB'⟩
  · rintro g ⟨gA, gB, rfl⟩
    exact h gA gB
  · exact fun i _ => ⟨A i, B i, rfl⟩

/-- **Uniqueness of the product valuation on the chain product `ω × ω`** (whenever one
exists): any two valuations on `LowerSet (ℕ × ℕ)` restricting to `v(A)·w(B)` on rectangles
coincide.  Contrast with the powerdomain literature, where Scott continuity is assumed to
build (and pin down) products: on this frame, no continuity is needed for uniqueness ---
the frame itself is rigid. -/
theorem Valuation.product_unique (v w : Valuation (LowerSet ℕ))
    {u u' : Valuation (LowerSet (ℕ × ℕ))}
    (hu : ∀ A B : LowerSet ℕ, u (A ×ˢ B) = v A * w B)
    (hu' : ∀ A B : LowerSet ℕ, u' (A ×ˢ B) = v A * w B) : u = u' :=
  u.eq_of_forall_prod_eq u' fun A B => (hu A B).trans (hu' A B).symm

end ConstructiveProb
