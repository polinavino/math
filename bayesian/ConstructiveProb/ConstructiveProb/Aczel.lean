/-
# Aczél's associativity theorem — the build (in progress)

The product-rule half of a constructive Cox theorem is Aczél's theorem: a continuous,
strictly-monotone, associative conjunction functional `F` on the plausibility scale is
**conjugate to multiplication** — there is a strictly monotone generator `g` with
`g (F x y) = g x · g y` (equivalently, an additive generator with `F x y = g⁻¹(g x + g y)`).
The full statement is `AczelStatement` in `Cox.lean`.

mathlib supplies none of the analytic core (no Cauchy functional equation, no Hölder embedding of
ordered cancellative semigroups, no theory of triangular norms and their generators), so the
existence of `g` is a multi-session build. This file records the part that *is* clean:

* the **converse/well-definedness direction** (a generator makes `F` associative and
  commutative), which validates that the conclusion of `AczelStatement` is the right
  characterisation, and
* the canonical **archetype** `exp/log`, which is the generator realising product = regraduated
  sum.

## Plan for the forward (hard) direction — what remains

Given `F` continuous, per-argument strictly monotone, and associative on `Icc 0 1`:

1. **Cancellativity (1a) + commutativity (1b).** Strict monotonicity gives cancellativity
   (`strictMonoOn_cancel`, proved). Commutativity turns out *not* to be an independent step: it
   is a corollary of the generator (`comm_of_additiveGenerator`, proved) — see step 3.
2. **Divisibility / roots.** Continuity + the intermediate value theorem give `F`-roots
   (`exists_diag_eq`, proved), so `(Icc 0 1, F)` is a divisible, cancellative, Archimedean,
   densely-ordered topological semigroup.
3. **Embedding into `(ℝ, +)`** (Hölder) — **the single irreducible hinge**. Such a semigroup
   embeds order-isomorphically into the additive reals; the embedding *is* the additive generator
   `g`. This is `HasAdditiveGenerator` below. The downstream consequences are all *proved* from
   it: it yields the multiplicative generator `exp ∘ g` (`hasMulGenerator_of_additive`, hence the
   conclusion of `AczelStatement`) and commutativity (`comm_of_additiveGenerator`). Only the
   *existence* of `g` is open — the analytic heart, with no mathlib support.
4. **Uniqueness up to scale.** Two generators differ by a positive scalar — Cauchy's equation
   (`monotone_additive_linear`, proved); mathlib had it only under continuity.

Standard proof: Aczél, *Lectures on Functional Equations* (1966). **Proved here:** the converse
direction, step 1a (cancellativity), step 1b (commutativity, from the generator), step 2 (roots
via IVT), step 4 (Cauchy), and the reductions showing step 3 ⟹ everything downstream. **Open:**
the existence of the generator (step 3, `HasAdditiveGenerator`) — Hölder's embedding theorem,
which is genuine missing infrastructure. Nothing here is `sorry`: the forward direction reduces
to the *stated* target `HasAdditiveGenerator`, not a half-finished proof.
-/
import ConstructiveProb.Cox
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic

namespace ConstructiveProb.Aczel

/-- The binary operation **generated** by `g` with section `ginv`: `F x y = ginv (g x · g y)`.
In Cox terms, `g` is the regraduation putting conjunction into multiplicative form. -/
def genOp {α : Type*} [Mul α] (g : ℝ → α) (ginv : α → ℝ) (x y : ℝ) : ℝ := ginv (g x * g y)

/-- **Converse direction: a generated operation is associative.** This is the easy half of
Aczél's characterisation — it shows the multiplicative form in `AczelStatement`'s conclusion
really does yield an associative conjunction. Needs only that `ginv` is a section of `g`
(`g ∘ ginv = id`) and associativity of `·`. -/
theorem genOp_assoc {α : Type*} [Semigroup α] (g : ℝ → α) (ginv : α → ℝ)
    (hgi : Function.RightInverse ginv g) (x y z : ℝ) :
    genOp g ginv (genOp g ginv x y) z = genOp g ginv x (genOp g ginv y z) := by
  have h : ∀ t, g (ginv t) = t := hgi
  simp only [genOp, h, mul_assoc]

/-- **A generated operation is commutative.** Aczél operations are always commutative; here that
is immediate from commutativity of `·`. -/
theorem genOp_comm {α : Type*} [CommMonoid α] (g : ℝ → α) (ginv : α → ℝ) (x y : ℝ) :
    genOp g ginv x y = genOp g ginv y x := by
  simp only [genOp, mul_comm]

/-- **The archetype.** `exp` (with section `log`) generates ordinary multiplication on the
positive reals from addition: `exp (log x + log y) = x · y`. This is the concrete regraduation
underlying the product rule — the `g = log` case of Aczél, made explicit. -/
theorem exp_add_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp (Real.log x + Real.log y) = x * y := by
  rw [Real.exp_add, Real.exp_log hx, Real.exp_log hy]

/-- The identity generator recovers multiplication itself: the product t-norm `F x y = x · y` is
Aczél-generated with `g = ginv = id`, the base point of the characterisation. -/
theorem genOp_id (x y : ℝ) : genOp (α := ℝ) id id x y = x * y := rfl

/-- **Forward direction, step 1 (cancellativity).** A per-argument strictly monotone operation
is cancellative on its domain: `F x z = F y z → x = y`. This is the first genuine reduction of
the hard direction — it turns the plausibility interval under `F` into a cancellative magma, the
starting point for the semigroup embedding (steps 2–3 of the plan above). Unlike the remaining
steps it needs no missing infrastructure: it is just injectivity of a strictly monotone map. -/
theorem strictMonoOn_cancel {F : ℝ → ℝ → ℝ} {s : Set ℝ}
    (hF : ∀ z, StrictMonoOn (fun x => F x z) s) {x y z : ℝ} (hx : x ∈ s) (hy : y ∈ s)
    (h : F x z = F y z) : x = y :=
  (hF z).injOn hx hy h

/-- **Forward direction, step 4 (Cauchy / generator uniqueness).** A monotone additive function
`ℝ → ℝ` is linear: `f x = f 1 · x`. This is the regularity that pins the Aczél generator down to
a positive rescaling — two additive generators of the same operation differ by a scalar, giving
the "up to rescaling" clause of Cox. mathlib proves linearity only under *continuity*
(`AddMonoidHom.toRealLinearMap`); the monotone hypothesis, which is what the Cox/plausibility
setting actually supplies, we discharge here from ℚ-homogeneity plus a density squeeze. -/
theorem monotone_additive_linear {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y)
    (hmono : Monotone f) (x : ℝ) : f x = f 1 * x := by
  have h0 : f 0 = 0 := by
    have h := hadd 0 0; rw [add_zero] at h; linarith
  have hc : 0 ≤ f 1 := h0 ▸ hmono zero_le_one
  -- ℚ-homogeneity: `f` is ℚ-linear because it is additive.
  have hrat : ∀ q : ℚ, f (q : ℝ) = f 1 * (q : ℝ) := by
    intro q
    have h := map_ratCast_smul (AddMonoidHom.mk' f hadd) ℝ ℝ q (1 : ℝ)
    simp only [AddMonoidHom.mk'_apply, smul_eq_mul, mul_one] at h
    rw [h, mul_comm]
  -- monotone squeeze against the rationals
  have upper : ∀ q : ℚ, x ≤ (q : ℝ) → f x ≤ f 1 * (q : ℝ) := fun q hq => hrat q ▸ hmono hq
  have lower : ∀ q : ℚ, (q : ℝ) ≤ x → f 1 * (q : ℝ) ≤ f x := fun q hq => hrat q ▸ hmono hq
  refine le_antisymm ?_ ?_
  · by_contra hcon
    replace hcon := not_le.mp hcon
    rcases hc.lt_or_eq with hpos | hzero
    · have hxlt : x < f x / f 1 := (lt_div_iff₀ hpos).mpr (by rwa [mul_comm] at hcon)
      obtain ⟨q, hxq, hqf⟩ := exists_rat_btwn hxlt
      have hqf' : f 1 * (q : ℝ) < f x := by rw [mul_comm]; exact (lt_div_iff₀ hpos).mp hqf
      exact absurd (upper q hxq.le) (not_le.mpr hqf')
    · rw [← hzero, zero_mul] at hcon
      obtain ⟨q, hxq⟩ := exists_rat_gt x
      have h := upper q hxq.le
      rw [← hzero, zero_mul] at h
      exact absurd h (not_le.mpr hcon)
  · by_contra hcon
    replace hcon := not_le.mp hcon
    rcases hc.lt_or_eq with hpos | hzero
    · have hxlt : f x / f 1 < x := (div_lt_iff₀ hpos).mpr (by rwa [mul_comm] at hcon)
      obtain ⟨q, hfq, hqx⟩ := exists_rat_btwn hxlt
      have hqf' : f x < f 1 * (q : ℝ) := by rw [mul_comm]; exact (div_lt_iff₀ hpos).mp hfq
      exact absurd (lower q hqx.le) (not_le.mpr hqf')
    · rw [← hzero, zero_mul] at hcon
      obtain ⟨q, hqx⟩ := exists_rat_lt x
      have h := lower q hqx.le
      rw [← hzero, zero_mul] at h
      exact absurd h (not_le.mpr hcon)

/-- **Forward direction, step 2 (roots, via the intermediate value theorem).** If the diagonal
`x ↦ F x x` is continuous on `[a,b]`, every value between `F a a` and `F b b` is attained — `F`
has "square roots". Iterating gives `2ⁿ`-th roots, the divisibility that makes the plausibility
interval an Archimedean *divisible* semigroup (a hypothesis Hölder's embedding needs). This is
the hard-direction step mathlib fully supports, via `intermediate_value_Icc`. -/
theorem exists_diag_eq {F : ℝ → ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun x => F x x) (Set.Icc a b))
    (hc : c ∈ Set.Icc (F a a) (F b b)) : ∃ x ∈ Set.Icc a b, F x x = c := by
  obtain ⟨x, hx, hxc⟩ := intermediate_value_Icc hab hcont hc
  exact ⟨x, hx, hxc⟩

/-- **The generator existence claim (Hölder embedding — the irreducible analytic core).** `F`
admits an *additive generator*: an injective `g` with `g (F x y) = g x + g y`. Given roots
(step 2), a continuous associative per-argument strictly monotone `F` makes `Icc 0 1` an
Archimedean, divisible, cancellative, densely-ordered topological semigroup, and **Hölder's
theorem** embeds any such order-isomorphically into `(ℝ, +)`; the embedding *is* `g`. This is the
one part with no mathlib support (no ordered-semigroup / Hölder infrastructure), a substantial
development in its own right — recorded here as the precise remaining target. Everything else in
the forward direction reduces to it (below). -/
def HasAdditiveGenerator (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, Function.Injective g ∧ ∀ x y, g (F x y) = g x + g y

/-- **Step 1b, resolved as a corollary of step 3.** Commutativity of `F` is *downstream* of the
generator, not a separate prerequisite: an additive generator forces `F x y = F y x` immediately,
because `g (F x y) = g x + g y = g y + g x = g (F y x)` and `g` is injective. (The classical
proof establishes commutativity by hand *en route* to building `g`; either way it is inseparable
from the embedding, not an independent easy step.) -/
theorem comm_of_additiveGenerator {F : ℝ → ℝ → ℝ} (h : HasAdditiveGenerator F) (x y : ℝ) :
    F x y = F y x := by
  obtain ⟨g, hinj, hgen⟩ := h
  exact hinj (by rw [hgen x y, hgen y x, add_comm])

/-- **Step 3 discharges the product-rule conclusion.** An additive generator `g` yields the
*multiplicative* generator `exp ∘ g`, giving the conclusion shape of `AczelStatement`
(`G (F x y) = G x · G y`). So proving `HasAdditiveGenerator` (the Hölder embedding) would complete
the forward direction; `exp ∘ g` is the regraduation putting conjunction into product form. -/
theorem hasMulGenerator_of_additive {F : ℝ → ℝ → ℝ} (h : HasAdditiveGenerator F) :
    ∃ G : ℝ → ℝ, Function.Injective G ∧ ∀ x y, G (F x y) = G x * G y := by
  obtain ⟨g, hinj, hgen⟩ := h
  refine ⟨fun x => Real.exp (g x), fun a b hab => hinj (Real.exp_injective hab), fun x y => ?_⟩
  simp only [hgen, Real.exp_add]

/-- What Hölder's embedding *actually* delivers is stronger than `HasAdditiveGenerator`: the
generator is an **order embedding** (`StrictMono g`), not merely injective. This is the faithful
target — an order-isomorphism onto a sub-semigroup of `(ℝ, +)`. -/
def HasOrderedGenerator (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, StrictMono g ∧ ∀ x y, g (F x y) = g x + g y

theorem hasAdditiveGenerator_of_ordered {F : ℝ → ℝ → ℝ} (h : HasOrderedGenerator F) :
    HasAdditiveGenerator F := by
  obtain ⟨g, hg, hgen⟩ := h; exact ⟨g, hg.injective, hgen⟩

/-- **The reduction, tightened to match `AczelStatement`.** From the order-embedding generator,
`exp ∘ g` is itself a *strictly monotone* multiplicative generator: `G (F x y) = G x · G y` with
`StrictMono G`. This is the full conclusion shape of `AczelStatement` — the strict monotonicity
of the regraduation flows through — leaving *only* the continuity of `g` (also supplied by the
embedding) and, above all, the existence of `g` (`HasOrderedGenerator`, i.e. Hölder) as the open
core. -/
theorem hasStrictMonoMulGenerator_of_ordered {F : ℝ → ℝ → ℝ} (h : HasOrderedGenerator F) :
    ∃ G : ℝ → ℝ, StrictMono G ∧ ∀ x y, G (F x y) = G x * G y := by
  obtain ⟨g, hg, hgen⟩ := h
  refine ⟨fun x => Real.exp (g x), Real.exp_strictMono.comp hg, fun x y => ?_⟩
  simp only [hgen, Real.exp_add]

/-! ### Building the generator: the direct (Aczél) construction — first stones

mathlib's Archimedean/Hahn machinery (`ArchimedeanClass`, `hahnEmbedding_isOrderedAddMonoid`) is
built for ordered *groups/modules*, not a semigroup on an interval, and bridging to it (group
completion, archimedean verification, continuity) is a large project. Aczél's own 1966 proof
instead constructs the generator *directly* on `ℝ`, by extending the discrete "iterate count"
`n ↦ aⁿ` (a semigroup hom `(ℕ,+) → (ℝ,F)`) to a real-valued `g`. The first stones of that
construction — the iterate and its laws — are below.

**What these give and what remains.** `Fpow_add` shows `n ↦ aⁿ` is a homomorphism, i.e. the
`ℕ`-linearity `g aⁿ = n · g a` on the cyclic sub-semigroup; `Fpow_strictMono` makes it an order
embedding when the base is positive. `Fpow_not_bddAbove`/`Fpow_archimedean` then show the iterates
are unbounded — the **Archimedean property**, *derived* here from strict positivity + continuity
rather than assumed — and `exists_Fpow_floor` reads off the resulting integer part `⌊g b / g a⌋`
of the generator. So of Hölder's three hypotheses on the semigroup, divisibility (`exists_diag_eq`,
roots) and Archimedeanness (`Fpow_archimedean`) are now theorems; only the embedding itself is open.
To finish one still needs: the dyadic refinement of `exists_Fpow_floor` (roots give `a^{m/2ⁿ}`); the
monotone-limit argument that these dyadic powers converge and define `g` on all of `ℝ`; additivity
of the limit; and continuity — after which Cauchy (`monotone_additive_linear`) pins `g` down. That
gluing (a genuine real-analysis development) is the remaining multi-session work; here we establish
the algebraic backbone plus the two structural (divisibility, Archimedean) preconditions. -/

/-- The right-associated `F`-**iterate**: `Fpow F a n` combines `a` with itself `n+1` times,
`(⋯((a ∘ a) ∘ a)⋯) ∘ a`. This is the seed of the additive generator (`g (Fpow a n) = (n+1)·g a`). -/
def Fpow (F : ℝ → ℝ → ℝ) (a : ℝ) : ℕ → ℝ
  | 0 => a
  | (n + 1) => F (Fpow F a n) a

/-- The zeroth iterate is the base itself (one copy). -/
@[simp] theorem Fpow_zero {F : ℝ → ℝ → ℝ} (a : ℝ) : Fpow F a 0 = a := rfl

/-- **The iterate is a semigroup homomorphism `(ℕ,+) → (ℝ,F)`** — from associativity *alone*, no
commutativity needed: `a^{m+n+1} = aᵐ ∘ aⁿ`. This is the `ℕ`-linearity that the generator extends
(via Cauchy, `monotone_additive_linear`) to all of `ℝ`. -/
theorem Fpow_add {F : ℝ → ℝ → ℝ} (hassoc : ∀ x y z, F (F x y) z = F x (F y z)) (a : ℝ)
    (m n : ℕ) : Fpow F a (m + n + 1) = F (Fpow F a m) (Fpow F a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hidx : m + (n + 1) + 1 = (m + n + 1) + 1 := by ring
    rw [hidx]
    change F (Fpow F a (m + n + 1)) a = F (Fpow F a m) (Fpow F a (n + 1))
    rw [ih, hassoc]
    rfl

/-- Each iterate step strictly increases when the base `a` is **positive** (`x < F x a` for all
`x`): `aⁿ < aⁿ⁺¹`. -/
theorem Fpow_lt_succ {F : ℝ → ℝ → ℝ} {a : ℝ} (hpos : ∀ x, x < F x a) (n : ℕ) :
    Fpow F a n < Fpow F a (n + 1) :=
  hpos (Fpow F a n)

/-- **The iterate is an order embedding** for a positive base: `n ↦ aⁿ` is strictly monotone.
This is what makes the eventual generator an order embedding (`HasOrderedGenerator`), and it needs
only positivity of `a`, not commutativity. -/
theorem Fpow_strictMono {F : ℝ → ℝ → ℝ} {a : ℝ} (hpos : ∀ x, x < F x a) :
    StrictMono (Fpow F a) :=
  strictMono_nat_of_lt_succ (Fpow_lt_succ hpos)

/-- **The Archimedean property, derived (not assumed).** The iterates of a positive base are
**unbounded above**: `{aⁿ}` has no upper bound in `ℝ`. This is the crux hypothesis of Hölder's
embedding theorem — and here it is *not* an axiom but a consequence of strict positivity plus
continuity. If the strictly-increasing iterates were bounded, monotone convergence would send them
to their supremum `L`; continuity of `x ↦ F x a` would then force `L = F L a`, contradicting the
strict `L < F L a`. So the sequence escapes every bound: the semigroup is Archimedean.

This upgrades the plan's step-3 "Archimedean, divisible semigroup" from a stack of assumptions
toward theorems — divisibility is `exists_diag_eq` (roots), and Archimedeanness is this. -/
theorem Fpow_not_bddAbove {F : ℝ → ℝ → ℝ} {a : ℝ} (hpos : ∀ x, x < F x a)
    (hcont : Continuous (fun x => F x a)) : ¬ BddAbove (Set.range (Fpow F a)) := by
  intro hbdd
  set L := ⨆ n, Fpow F a n with hLdef
  have hmono := (Fpow_strictMono hpos).monotone
  have hL : Filter.Tendsto (Fpow F a) Filter.atTop (nhds L) := tendsto_atTop_ciSup hmono hbdd
  have hshift : Filter.Tendsto (fun n => Fpow F a (n + 1)) Filter.atTop (nhds L) :=
    hL.comp (Filter.tendsto_add_atTop_nat 1)
  have hcomp : Filter.Tendsto (fun n => F (Fpow F a n) a) Filter.atTop (nhds (F L a)) :=
    (hcont.tendsto L).comp hL
  have heq : (fun n => Fpow F a (n + 1)) = (fun n => F (Fpow F a n) a) := rfl
  rw [heq] at hshift
  exact absurd (tendsto_nhds_unique hshift hcomp) (ne_of_lt (hpos L))

/-- **Archimedeanness in usable form.** Every real target `b` is eventually exceeded by some
iterate: `∃ n, b < aⁿ`. This is the shape the generator construction consumes — to assign `g b`
one counts how many fine roots of a fixed unit fit below `b`, which terminates precisely because
the iterates overshoot every `b`. Immediate from `Fpow_not_bddAbove`. -/
theorem Fpow_archimedean {F : ℝ → ℝ → ℝ} {a : ℝ} (hpos : ∀ x, x < F x a)
    (hcont : Continuous (fun x => F x a)) (b : ℝ) : ∃ n, b < Fpow F a n := by
  have h := Fpow_not_bddAbove hpos hcont
  rw [not_bddAbove_iff] at h
  obtain ⟨y, hy, hby⟩ := h b
  obtain ⟨n, rfl⟩ := hy
  exact ⟨n, hby⟩

/-- **The integer part of the generator.** For a base `a` and any target `b ≥ a`, there is a
*unique* largest iterate below `b`: an `N` with `aᴺ ≤ b < aᴺ⁺¹`. Reading `g` off the eventual
generator, `N = ⌊g b / g a⌋` — this is the first concrete numerical datum the construction extracts
from `b`, the coarse (integer) approximation later refined by dyadic roots.

Well-definedness rests on the two structural facts just established: the iterates are strictly
increasing (`Fpow_strictMono`, so at most one `N` qualifies) and **unbounded** (`Fpow_archimedean`,
so the search terminates — some iterate overshoots `b`). Existence of the floor is thus a corollary
of Archimedeanness, exactly as the floor `⌊x⌋` of a real is a corollary of `ℕ`'s Archimedean
property in `ℝ`.

(The `classical` here is meta-level: `Nat.findGreatest` wants decidable `≤` on `ℝ`, and this is a
bridge lemma in the classically-proved Aczél development, not part of the constructive valuation
layer — cf. the counterexamples, which are likewise meta.) -/
theorem exists_Fpow_floor {F : ℝ → ℝ → ℝ} {a b : ℝ} (hpos : ∀ x, x < F x a)
    (hcont : Continuous (fun x => F x a)) (hab : a ≤ b) :
    ∃ N, Fpow F a N ≤ b ∧ b < Fpow F a (N + 1) := by
  obtain ⟨m, hm⟩ := Fpow_archimedean hpos hcont b
  classical
  have hP0 : (fun n => Fpow F a n ≤ b) 0 := hab
  have hPN := Nat.findGreatest_spec (P := fun n => Fpow F a n ≤ b) (Nat.zero_le m) hP0
  have hmP : ¬ Fpow F a m ≤ b := not_le.mpr hm
  have hNm : Nat.findGreatest (fun n => Fpow F a n ≤ b) m < m :=
    lt_of_le_of_ne (Nat.findGreatest_le m) (fun h => hmP (h ▸ hPN))
  have hgreatest := Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hNm
  exact ⟨Nat.findGreatest (fun n => Fpow F a n ≤ b) m, hPN, not_le.mp hgreatest⟩

/-! ### The dyadic root tower — the scaffold for the generator's values

Where the integer part `exists_Fpow_floor` measures `b` in whole copies of the unit, the
*fractional* part measures it in copies of ever-finer roots. This block builds that ruler: the
tower of `2ⁿ`-th roots of a fixed unit `u`, proving that `2ⁿ` copies of the `n`-th root recompose
`u` exactly. That "recompose" identity is what makes the dyadic resolution *coherent* across
scales — refining `n → n+1` halves the tick without moving the marks already placed — and it is the
fact the eventual monotone-limit argument rests on. Divisibility enters as the abstract hypothesis
`hdiv : ∀ c, ∃ x, F x x = c` ("every element has a halver"); `exists_diag_eq` is the evidence that
the plausibility interval satisfies it. -/

/-- A **halver** of `c`: an `x` with `F x x = c`, i.e. `c` split into two equal copies. Chosen (via
`Classical.choose`) from the divisibility hypothesis; this is meta-level, in the classical Aczél
layer, not the constructive valuation layer. -/
noncomputable def half (F : ℝ → ℝ → ℝ) (hdiv : ∀ c, ∃ x, F x x = c) (c : ℝ) : ℝ :=
  Classical.choose (hdiv c)

theorem half_spec (F : ℝ → ℝ → ℝ) (hdiv : ∀ c, ∃ x, F x x = c) (c : ℝ) :
    F (half F hdiv c) (half F hdiv c) = c :=
  Classical.choose_spec (hdiv c)

/-- The **dyadic root tower** of a unit `u`: `droot u n` is a `2ⁿ`-th root of `u`, obtained by
halving `n` times. `droot u 0 = u`; each level is a halver of the one above. -/
noncomputable def droot (F : ℝ → ℝ → ℝ) (hdiv : ∀ c, ∃ x, F x x = c) (u : ℝ) : ℕ → ℝ
  | 0 => u
  | (n + 1) => half F hdiv (droot F hdiv u n)

/-- Adjacent levels of the tower: two copies of the finer root give the coarser one. Immediate
from `half_spec` — this is the tower's defining recurrence. -/
theorem droot_succ_double (F : ℝ → ℝ → ℝ) (hdiv : ∀ c, ∃ x, F x x = c) (u : ℝ) (n : ℕ) :
    F (droot F hdiv u (n + 1)) (droot F hdiv u (n + 1)) = droot F hdiv u n :=
  half_spec F hdiv (droot F hdiv u n)

/-- The tower is **strictly decreasing** (roots get genuinely finer) when the operation is
diagonally increasing (`x < F x x`): `droot u (n+1) < droot u n`. Diagonal positivity is the
divisible-semigroup analogue of `hpos`, and this monotonicity is what will let the dyadic
approximants converge from below. -/
theorem droot_strictAnti (F : ℝ → ℝ → ℝ) (hdiv : ∀ c, ∃ x, F x x = c) (hdiag : ∀ x, x < F x x)
    (u : ℝ) (n : ℕ) : droot F hdiv u (n + 1) < droot F hdiv u n := by
  have h := hdiag (droot F hdiv u (n + 1))
  rwa [droot_succ_double F hdiv u n] at h

/-- **Copies compose.** `k` copies of "two copies of `r`" is `2k+1`-fold iteration of `r`:
`Fpow F (F r r) k = Fpow F r (2k+1)`. Associativity alone (no commutativity). This is the bridge
between iterating a *doubled* element and iterating the element itself — the arithmetic heart of
the recompose lemma below. -/
theorem Fpow_double {F : ℝ → ℝ → ℝ} (hassoc : ∀ x y z, F (F x y) z = F x (F y z)) (r : ℝ) (k : ℕ) :
    Fpow F (F r r) k = Fpow F r (2 * k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
    calc Fpow F (F r r) (k + 1)
        = F (Fpow F (F r r) k) (F r r) := rfl
      _ = F (Fpow F r (2 * k + 1)) (F r r) := by rw [ih]
      _ = F (F (Fpow F r (2 * k + 1)) r) r := (hassoc _ r r).symm
      _ = Fpow F r (2 * (k + 1) + 1) := by rw [e]; rfl

/-- **The payoff: `2ⁿ` copies of the `n`-th root recompose the unit.**
`Fpow F (droot u n) (2ⁿ − 1) = u` (recall `Fpow … (m)` combines `m+1` copies, so `2ⁿ−1` is `2ⁿ`
copies). By induction: level `n+1` is `2·(2ⁿ−1)+1` copies of `droot u (n+1)`, which by `Fpow_double`
equals `2ⁿ−1` copies of `F (droot u (n+1)) (droot u (n+1)) = droot u n`, then the inductive
hypothesis. This coherence — every level of the ruler measures the *same* unit — is precisely what a
well-defined dyadic generator needs, and it is now a theorem. -/
theorem Fpow_droot_pow {F : ℝ → ℝ → ℝ} (hdiv : ∀ c, ∃ x, F x x = c)
    (hassoc : ∀ x y z, F (F x y) z = F x (F y z)) (u : ℝ) (n : ℕ) :
    Fpow F (droot F hdiv u n) (2 ^ n - 1) = u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    have hge : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
    have e : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by omega
    calc Fpow F (droot F hdiv u (n + 1)) (2 ^ (n + 1) - 1)
        = Fpow F (droot F hdiv u (n + 1)) (2 * (2 ^ n - 1) + 1) := by rw [e]
      _ = Fpow F (F (droot F hdiv u (n + 1)) (droot F hdiv u (n + 1))) (2 ^ n - 1) :=
            (Fpow_double hassoc (droot F hdiv u (n + 1)) (2 ^ n - 1)).symm
      _ = Fpow F (droot F hdiv u n) (2 ^ n - 1) := by rw [droot_succ_double F hdiv u n]
      _ = u := ih

/-- **Refinement preserves marks.** The `(k+1)`-th mark on the coarse ruler (level `n`) coincides
*exactly* with the `2(k+1)`-th mark on the fine ruler (level `n+1`):
`Fpow F (droot u (n+1)) (2k+1) = Fpow F (droot u n) k`. (Recall `Fpow … m` is `m+1` copies, so the
index `2k+1` names `2(k+1)` copies and `k` names `k+1` copies.) Halving the tick moves no mark
already placed — the precise coherence that makes the dyadic approximants `gₙ` a *consistent*
refinement (so `g_{n+1}` extends, not overwrites, `gₙ`) and hence lets them converge. Immediate from
`droot_succ_double` (two fine copies = one coarse) and `Fpow_double` (copies compose). -/
theorem Fpow_droot_succ {F : ℝ → ℝ → ℝ} (hdiv : ∀ c, ∃ x, F x x = c)
    (hassoc : ∀ x y z, F (F x y) z = F x (F y z)) (u : ℝ) (n k : ℕ) :
    Fpow F (droot F hdiv u (n + 1)) (2 * k + 1) = Fpow F (droot F hdiv u n) k := by
  rw [← droot_succ_double F hdiv u n]
  exact (Fpow_double hassoc (droot F hdiv u (n + 1)) k).symm

/-- **The tower is one coherent ruler (marks coincide across any level gap).** Descending `ℓ`
levels multiplies the copy-count by `2^ℓ`: the `(k+1)`-th coarse mark at level `n` is the
`2^ℓ·(k+1)`-th mark at level `n+ℓ`,
`Fpow F (droot u (n+ℓ)) (2^ℓ·(k+1) − 1) = Fpow F (droot u n) k`. Iterating `Fpow_droot_succ`, by
induction on `ℓ`. This is the *well-definedness backbone* of the eventual limit `g`: it says every
level of the dyadic ruler refines a single common ruler, so comparing `b` against level `n` versus
level `m` is comparing it against nested marks that agree wherever they overlap. `Fpow_droot_pow`
is the special case `n = k = 0` (`2^ℓ` copies of the `ℓ`-th root recompose the unit). -/
theorem Fpow_droot_add {F : ℝ → ℝ → ℝ} (hdiv : ∀ c, ∃ x, F x x = c)
    (hassoc : ∀ x y z, F (F x y) z = F x (F y z)) (u : ℝ) (n k ℓ : ℕ) :
    Fpow F (droot F hdiv u (n + ℓ)) (2 ^ ℓ * (k + 1) - 1) = Fpow F (droot F hdiv u n) k := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have e : 2 ^ (ℓ + 1) * (k + 1) - 1 = 2 * (2 ^ ℓ * (k + 1) - 1) + 1 := by
      have hge : 1 ≤ 2 ^ ℓ * (k + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have h2 : 2 ^ (ℓ + 1) * (k + 1) = 2 * (2 ^ ℓ * (k + 1)) := by rw [pow_succ]; ring
      omega
    calc Fpow F (droot F hdiv u (n + (ℓ + 1))) (2 ^ (ℓ + 1) * (k + 1) - 1)
        = Fpow F (droot F hdiv u ((n + ℓ) + 1)) (2 * (2 ^ ℓ * (k + 1) - 1) + 1) := by rw [e]; rfl
      _ = Fpow F (droot F hdiv u (n + ℓ)) (2 ^ ℓ * (k + 1) - 1) :=
            Fpow_droot_succ hdiv hassoc u (n + ℓ) (2 ^ ℓ * (k + 1) - 1)
      _ = Fpow F (droot F hdiv u n) k := ih

/-! ### The convergence layer — from the ruler to the generator

With the ruler built and proved coherent, the generator is the limit of the dyadic readings
`gₙ(b) = countₙ(b) / 2ⁿ`, where `countₙ(b)` is how many copies of the `n`-th root sit at or below
`b`. This block assembles the facts that make that limit exist: the tower stays below the unit (so
the count is defined for `b ≥ u`); the count is *characterized* by `Fpow c m ≤ b ↔ m ≤ N`; and — the
crux — refining the ruler one level **roughly doubles** the count (`2N+1 ≤ N' ≤ 2N+2`). That last
fact is exactly monotonicity-plus-Cauchy for `gₙ` in disguise: `N/2ⁿ ≤ N'/2ⁿ⁺¹ ≤ N/2ⁿ + 2⁻ⁿ`. -/

/-- The tower is **strictly decreasing** as a sequence (packaged `StrictAnti`), given diagonal
positivity. Upgrade of `droot_strictAnti`. -/
theorem droot_strictAnti' {F : ℝ → ℝ → ℝ} (hdiv : ∀ c, ∃ x, F x x = c) (hdiag : ∀ x, x < F x x)
    (u : ℝ) : StrictAnti (droot F hdiv u) :=
  strictAnti_nat_of_succ_lt (droot_strictAnti F hdiv hdiag u)

/-- Every root in the tower lies **below the unit**: `droot u n ≤ u`. Hence for a target `b ≥ u`
the count is defined at every level (one copy of any root already fits). -/
theorem droot_le_unit {F : ℝ → ℝ → ℝ} (hdiv : ∀ c, ∃ x, F x x = c) (hdiag : ∀ x, x < F x x)
    (u : ℝ) (n : ℕ) : droot F hdiv u n ≤ u :=
  (droot_strictAnti' hdiv hdiag u).antitone (Nat.zero_le n)

/-- **The floor as a characterization.** For a positive base `c` (`x < F x c`, giving strict
monotonicity of the iterate) with `c ≤ b`, the count `N` is *the* index with
`Fpow F c m ≤ b ↔ m ≤ N` for all `m` — i.e. `N` is the largest number of copies fitting under `b`.
Upgrades `exists_Fpow_floor` (which gives the sandwiched value) to its order characterization, which
is what the count arithmetic below actually consumes. -/
theorem exists_Fpow_floor_iff {F : ℝ → ℝ → ℝ} {c b : ℝ} (hpos : ∀ x, x < F x c)
    (hcont : Continuous (fun x => F x c)) (hcb : c ≤ b) :
    ∃ N, ∀ m, Fpow F c m ≤ b ↔ m ≤ N := by
  obtain ⟨N, hN1, hN2⟩ := exists_Fpow_floor hpos hcont hcb
  have hsm := Fpow_strictMono hpos
  refine ⟨N, fun m => ⟨fun hm => ?_, fun hm => le_trans (hsm.monotone hm) hN1⟩⟩
  by_contra hlt
  rw [not_le] at hlt
  have hm1 : N + 1 ≤ m := hlt
  exact absurd (lt_of_lt_of_le hN2 (hsm.monotone hm1)) (not_lt.mpr hm)

/-- **The crux of convergence: refining the ruler roughly doubles the count.** If `N` copies of the
level-`n` root fit under `b` and `N'` copies of the level-`(n+1)` root fit under `b`, then
`2N+1 ≤ N' ≤ 2N+2`. Both counts come from their order characterizations (`exists_Fpow_floor_iff`).
The proof is pure ruler coherence: `Fpow_droot_succ` turns "`N` coarse copies" into "`2N+1`-index
(= `2(N+1)` fine copies)", so at least `2N+1` fine copies fit; and "`N+1` coarse copies overshoot"
becomes "`2N+3` fine index overshoots", so fewer than `2N+3` fine copies fit. Dividing by `2ⁿ⁺¹`:
`N/2ⁿ ≤ N'/2ⁿ⁺¹ ≤ N/2ⁿ + 2⁻ⁿ`, which is monotonicity and the Cauchy gap for `gₙ = countₙ/2ⁿ`. -/
theorem dcount_sandwich {F : ℝ → ℝ → ℝ} (hdiv : ∀ c, ∃ x, F x x = c)
    (hassoc : ∀ x y z, F (F x y) z = F x (F y z)) (u : ℝ) {b : ℝ} {n N N' : ℕ}
    (hN : ∀ m, Fpow F (droot F hdiv u n) m ≤ b ↔ m ≤ N)
    (hN' : ∀ m, Fpow F (droot F hdiv u (n + 1)) m ≤ b ↔ m ≤ N') :
    2 * N + 1 ≤ N' ∧ N' ≤ 2 * N + 2 := by
  refine ⟨?_, ?_⟩
  · apply (hN' (2 * N + 1)).mp
    rw [Fpow_droot_succ hdiv hassoc u n N]
    exact (hN N).mpr le_rfl
  · by_contra hlt
    rw [not_le] at hlt
    have h2 : Fpow F (droot F hdiv u (n + 1)) (2 * N + 3) ≤ b := (hN' (2 * N + 3)).mpr (by omega)
    rw [show 2 * N + 3 = 2 * (N + 1) + 1 from by ring] at h2
    rw [Fpow_droot_succ hdiv hassoc u n (N + 1)] at h2
    have hcontra := (hN (N + 1)).mp h2
    omega

/-- **Monotonicity of the approximants**, the real-level reading of the left half of the sandwich:
`gₙ(b) = N/2ⁿ ≤ N'/2ⁿ⁺¹ = g_{n+1}(b)`. Pure arithmetic from `2N+1 ≤ N'` (hence `2N ≤ N'`) and
`N/2ⁿ = 2N/2ⁿ⁺¹`. So the dyadic readings never decrease as the ruler refines. -/
theorem ratio_mono_of_sandwich (N N' n : ℕ) (h : 2 * N + 1 ≤ N') :
    (N : ℝ) / 2 ^ n ≤ (N' : ℝ) / 2 ^ (n + 1) := by
  have e : (N : ℝ) / 2 ^ n = (2 * N : ℝ) / 2 ^ (n + 1) := by rw [pow_succ]; ring
  rw [e]
  gcongr
  exact_mod_cast by omega

/-- **The Cauchy gap**, the real-level reading of the right half of the sandwich:
`g_{n+1}(b) = N'/2ⁿ⁺¹ ≤ N/2ⁿ + 1/2ⁿ = gₙ(b) + 2⁻ⁿ`. From `N' ≤ 2N+2` and
`N/2ⁿ + 1/2ⁿ = (2N+2)/2ⁿ⁺¹`. Since `2⁻ⁿ → 0`, together with monotonicity this makes `gₙ(b)` a
Cauchy (indeed monotone bounded) sequence — the generator value `g(b)` is its limit. -/
theorem ratio_gap_of_sandwich (N N' n : ℕ) (h : N' ≤ 2 * N + 2) :
    (N' : ℝ) / 2 ^ (n + 1) ≤ (N : ℝ) / 2 ^ n + 1 / 2 ^ n := by
  have e : (N : ℝ) / 2 ^ n + 1 / 2 ^ n = (2 * N + 2 : ℝ) / 2 ^ (n + 1) := by rw [pow_succ]; ring
  rw [e]
  gcongr
  exact_mod_cast by omega

/-! ### Packaging: the positive scale and its dyadic approximants

The lemmas above are stated for a bare `F` with side hypotheses. Here we bundle those hypotheses
into a `Scale` and turn the abstract count into an actual function `gₙ : ℝ → ℝ`, so the generator
can be written as a genuine limit. `hpos : ∀ c x, x < F x c` is the **positive-cone reduction**:
every combination strictly increases its argument, the standard setting in which Hölder's
embedding of an Archimedean ordered semigroup is carried out. -/

/-- A **positive, divisible, continuous, associative scale** with a chosen unit `u`: exactly the
hypothesis bundle Aczél's generator construction consumes. -/
structure Scale where
  /-- The conjunction/combination functional (a t-conorm-like operation on the scale). -/
  F : ℝ → ℝ → ℝ
  /-- Divisibility: every element has a halver. -/
  hdiv : ∀ c, ∃ x, F x x = c
  /-- Associativity (the product-rule content). -/
  hassoc : ∀ x y z, F (F x y) z = F x (F y z)
  /-- Positivity on the cone: every combination strictly increases. -/
  hpos : ∀ c x, x < F x c
  /-- Order-preservation: the combination is monotone in both arguments jointly. This is the
  standard ordered-semigroup hypothesis of Aczél's/Hölder's theorem, and is what makes the
  count additive — comparisons of a target against iterates of a root combine under `F`.
  (Satisfied, with everything else, by the archetype `F x y = log (eˣ + eʸ)`, `g = exp`.) -/
  hmono : ∀ x₁ x₂ y₁ y₂ : ℝ, x₁ ≤ x₂ → y₁ ≤ y₂ → F x₁ y₁ ≤ F x₂ y₂
  /-- Joint continuity. -/
  hcont : Continuous fun p : ℝ × ℝ => F p.1 p.2
  /-- **Identity at `−∞`.** As the second argument runs off to `−∞`, the combination returns its
  first argument: the additive identity of the ordered semigroup sits at the bottom of the scale.
  This is what makes the roots shrink to nothing, and is the last ingredient of strict
  monotonicity. (Satisfied by `F x y = log (eˣ + eʸ)`: `log (eˣ + eᶻ) → log eˣ = x` as `z → −∞`.) -/
  hbot : ∀ x, Filter.Tendsto (fun z => F x z) Filter.atBot (nhds x)
  /-- The chosen unit, assigned generator value `1`. -/
  u : ℝ

namespace Scale

variable (S : Scale)

/-- The dyadic root tower of the scale's unit. -/
noncomputable def droot : ℕ → ℝ := ConstructiveProb.Aczel.droot S.F S.hdiv S.u

theorem hdiag : ∀ x, x < S.F x x := fun x => S.hpos x x

theorem pos (n : ℕ) : ∀ x, x < S.F x (S.droot n) := fun x => S.hpos (S.droot n) x

theorem cont (n : ℕ) : Continuous (fun x => S.F x (S.droot n)) :=
  S.hcont.comp (continuous_id.prodMk continuous_const)

theorem droot_le_unit (n : ℕ) : S.droot n ≤ S.u :=
  ConstructiveProb.Aczel.droot_le_unit S.hdiv S.hdiag S.u n

open Classical in
/-- **The count**: how many copies of the level-`n` root fit at or below `b`. Defined (for `b ≥ u`,
where it is meaningful) as the characterizing floor `exists_Fpow_floor_iff`; `0` otherwise. -/
noncomputable def dcount (b : ℝ) (n : ℕ) : ℕ :=
  if h : S.u ≤ b then
    Classical.choose (exists_Fpow_floor_iff (S.pos n) (S.cont n) (le_trans (S.droot_le_unit n) h))
  else 0

/-- The defining property of the count for `b ≥ u`: `Fpow (droot n) m ≤ b ↔ m ≤ dcount b n`. -/
theorem dcount_spec {b : ℝ} (h : S.u ≤ b) (n m : ℕ) :
    Fpow S.F (S.droot n) m ≤ b ↔ m ≤ S.dcount b n := by
  simp only [dcount, dif_pos h]
  exact Classical.choose_spec
    (exists_Fpow_floor_iff (S.pos n) (S.cont n) (le_trans (S.droot_le_unit n) h)) m

/-- **The dyadic approximant** `gₙ(b) = countₙ(b) / 2ⁿ` — the level-`n` reading of the generator. -/
noncomputable def gapprox (b : ℝ) (n : ℕ) : ℝ := (S.dcount b n : ℝ) / 2 ^ n

/-- **The approximants increase with resolution** (for `b ≥ u`): `gₙ(b) ≤ g_{n+1}(b)`. This is the
sandwich's left half (`dcount_sandwich` ⟹ `ratio_mono_of_sandwich`) transported to the function. -/
theorem gapprox_mono {b : ℝ} (h : S.u ≤ b) (n : ℕ) : S.gapprox b n ≤ S.gapprox b (n + 1) := by
  have hs := dcount_sandwich S.hdiv S.hassoc S.u (S.dcount_spec h n) (S.dcount_spec h (n + 1))
  simpa only [gapprox] using ratio_mono_of_sandwich (S.dcount b n) (S.dcount b (n + 1)) n hs.1

/-- **The approximants are uniformly bounded** (for `b ≥ u`): `gₙ(b) ≤ g₀(b) + 2` for every `n`.
This is the *a priori* bound that (with monotonicity) forces the limit to exist. It comes from the
multi-level ruler coherence `Fpow_droot_add`: `2ⁿ·(M+2)` copies of the level-`n` root overshoot `b`
(because that many copies equal `M+1` copies of the unit, which already overshoots, as `M = g₀(b)`
copies of the unit is the most that fit), so `countₙ(b) < 2ⁿ·(M+2)` and `gₙ(b) < M + 2`. -/
theorem gapprox_le {b : ℝ} (h : S.u ≤ b) (n : ℕ) : S.gapprox b n ≤ (S.dcount b 0 : ℝ) + 2 := by
  set M := S.dcount b 0 with hM
  have hkey : Fpow S.F (S.droot n) (2 ^ n * (M + 1 + 1) - 1) = Fpow S.F (S.droot 0) (M + 1) := by
    have hh := Fpow_droot_add S.hdiv S.hassoc S.u 0 (M + 1) n
    simpa [Scale.droot] using hh
  have hb : ¬ Fpow S.F (S.droot 0) (M + 1) ≤ b := by
    rw [S.dcount_spec h 0 (M + 1)]; omega
  have hbn : ¬ 2 ^ n * (M + 1 + 1) - 1 ≤ S.dcount b n := by
    rw [← S.dcount_spec h n, hkey]; exact hb
  have hle : S.dcount b n ≤ 2 ^ n * (M + 1 + 1) := by have := not_le.mp hbn; omega
  rw [gapprox, div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ n)]
  calc (S.dcount b n : ℝ) ≤ ((2 ^ n * (M + 1 + 1) : ℕ) : ℝ) := by exact_mod_cast hle
    _ = ((M : ℝ) + 2) * 2 ^ n := by push_cast; ring

/-- Monotonicity of the approximant sequence (for `b ≥ u`), packaged as `Monotone`. -/
theorem gapprox_monotone {b : ℝ} (h : S.u ≤ b) : Monotone (S.gapprox b) :=
  monotone_nat_of_le_succ (S.gapprox_mono h)

/-- The approximant sequence is bounded above (for `b ≥ u`). -/
theorem gapprox_bddAbove {b : ℝ} (h : S.u ≤ b) : BddAbove (Set.range (S.gapprox b)) := by
  refine ⟨(S.dcount b 0 : ℝ) + 2, ?_⟩
  rintro y ⟨n, rfl⟩
  exact S.gapprox_le h n

/-- **The generator** (on the positive cone `b ≥ u`): the limit of the dyadic readings,
`g(b) = ⨆ₙ gₙ(b) = limₙ countₙ(b)/2ⁿ`. Defined as the supremum; `gapprox_tendsto` shows it *is* the
limit. This is the object whose additivity and continuity remain to be established, after which
`monotone_additive_linear` pins it to the linear generator Hölder's theorem promises. -/
noncomputable def g (b : ℝ) : ℝ := ⨆ n, S.gapprox b n

/-- The approximants **converge to the generator** (for `b ≥ u`): monotone + bounded, so by the
monotone convergence theorem `gₙ(b) → g(b)`. -/
theorem gapprox_tendsto {b : ℝ} (h : S.u ≤ b) :
    Filter.Tendsto (S.gapprox b) Filter.atTop (nhds (S.g b)) :=
  tendsto_atTop_ciSup (S.gapprox_monotone h) (S.gapprox_bddAbove h)

/-! ### Normalization: the generator sends the unit to `1`

The unit `u` is the yardstick, so `g u` must be `1`. Concretely, at level `n` exactly
`2ⁿ` copies of the `n`-th root recompose `u` (`Fpow_droot_pow`) and one more copy
overshoots it (positivity), so the count is exactly `dcount u n = 2ⁿ − 1` and the reading is
`gₙ(u) = (2ⁿ−1)/2ⁿ = 1 − 2⁻ⁿ`, which tends to `1`. Uniqueness of limits then pins `g u = 1`.
This is the first check that the constructed generator does the right thing on a known input. -/

/-- **Exact count at the unit.** `dcount u n = 2ⁿ − 1`: precisely `2ⁿ` copies of the level-`n`
root fit inside `u` (they recompose it), and `2ⁿ + 1` copies overshoot. -/
theorem dcount_unit (n : ℕ) : S.dcount S.u n = 2 ^ n - 1 := by
  have hge : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hpow : Fpow S.F (S.droot n) (2 ^ n - 1) = S.u := by
    have h := Fpow_droot_pow S.hdiv S.hassoc S.u n
    simpa [Scale.droot] using h
  -- `2ⁿ − 1` copies fit exactly (they equal `u`), so `2ⁿ − 1 ≤ dcount`.
  have hlow : 2 ^ n - 1 ≤ S.dcount S.u n :=
    (S.dcount_spec (le_refl S.u) n (2 ^ n - 1)).mp hpow.le
  -- one more copy is `F u (droot n) > u`, so `2ⁿ` copies overshoot: `¬ 2ⁿ ≤ dcount`.
  have hstep : Fpow S.F (S.droot n) (2 ^ n) = S.F S.u (S.droot n) := by
    conv_lhs => rw [show 2 ^ n = (2 ^ n - 1) + 1 from by omega]
    change S.F (Fpow S.F (S.droot n) (2 ^ n - 1)) (S.droot n) = S.F S.u (S.droot n)
    rw [hpow]
  have hgt : ¬ Fpow S.F (S.droot n) (2 ^ n) ≤ S.u := by
    rw [hstep]; exact not_le.mpr (S.pos n S.u)
  have hup : ¬ 2 ^ n ≤ S.dcount S.u n := by
    rw [← S.dcount_spec (le_refl S.u) n (2 ^ n)]; exact hgt
  omega

/-- **The reading at the unit is `1 − 2⁻ⁿ`.** Immediate from `dcount_unit`. -/
theorem gapprox_unit (n : ℕ) : S.gapprox S.u n = 1 - ((2 : ℝ)⁻¹) ^ n := by
  have hge : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hcast : (S.dcount S.u n : ℝ) = (2 : ℝ) ^ n - 1 := by
    rw [dcount_unit, Nat.cast_sub hge]; push_cast; ring
  simp only [Scale.gapprox, hcast]
  rw [sub_div, div_self (by positivity : (2 : ℝ) ^ n ≠ 0), one_div, ← inv_pow]

/-- The readings at the unit converge to `1` (as `1 − 2⁻ⁿ → 1`). -/
theorem gapprox_unit_tendsto :
    Filter.Tendsto (S.gapprox S.u) Filter.atTop (nhds 1) := by
  have h0 : Filter.Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 := h0.const_sub (1 : ℝ)
  rw [sub_zero] at h1
  exact h1.congr (fun n => (S.gapprox_unit n).symm)

/-- **Generator normalization:** `g u = 1`. The unit is assigned value one, by uniqueness of
limits (`gapprox_tendsto` sends `gₙ(u) → g u`, `gapprox_unit_tendsto` sends `gₙ(u) → 1`). -/
theorem g_unit : S.g S.u = 1 :=
  tendsto_nhds_unique (S.gapprox_tendsto (le_refl S.u)) S.gapprox_unit_tendsto

/-! ### Monotonicity in the argument

A larger target admits at least as many copies of every root, so each count — hence each
reading, hence the limit `g` — is monotone in `b` on the cone `b ≥ u`. This is the first half
of the eventual order-embedding property (`StrictMono g`); strictness will come later from the
Archimedean/density argument. -/

/-- **The count is monotone in the target.** If `u ≤ b ≤ b'` then `dcount b n ≤ dcount b' n`:
whatever number of copies fits under `b` also fits under the larger `b'`. -/
theorem dcount_mono {b b' : ℝ} (h : S.u ≤ b) (hb : b ≤ b') (n : ℕ) :
    S.dcount b n ≤ S.dcount b' n := by
  have hfit : Fpow S.F (S.droot n) (S.dcount b n) ≤ b :=
    (S.dcount_spec h n (S.dcount b n)).mpr le_rfl
  exact (S.dcount_spec (le_trans h hb) n (S.dcount b n)).mp (le_trans hfit hb)

/-- Each dyadic reading is monotone in the target. -/
theorem gapprox_mono_b {b b' : ℝ} (h : S.u ≤ b) (hb : b ≤ b') (n : ℕ) :
    S.gapprox b n ≤ S.gapprox b' n := by
  have hd := S.dcount_mono h hb n
  simp only [Scale.gapprox]
  gcongr

/-- **The generator is monotone** on the cone: `u ≤ b ≤ b' ⟹ g b ≤ g b'`. -/
theorem g_mono {b b' : ℝ} (h : S.u ≤ b) (hb : b ≤ b') : S.g b ≤ S.g b' := by
  simp only [Scale.g]
  refine ciSup_le (fun n => le_trans (S.gapprox_mono_b h hb n) ?_)
  exact le_ciSup (S.gapprox_bddAbove (le_trans h hb)) n

/-! ### Additivity — the analytic heart of Aczél's theorem

The generator turns `F` into `+`: `g (F x y) = g x + g y`. The mechanism is that counting is
*almost* additive at every finite level. If `P` copies of the level-`n` root fit under `x` and
`Q` under `y`, then combining shows `P + Q + 1` copies fit under `F x y` (order-preservation
lifts `Fpow a P ≤ x`, `Fpow a Q ≤ y` through `F`), while the maximality of `P`, `Q` caps the
count at `P + Q + 3`. So the level-`n` reading of `F x y` is within `[gₙx+gₙy+2⁻ⁿ, gₙx+gₙy+3·2⁻ⁿ]`;
as `n → ∞` the `2⁻ⁿ` slack vanishes and the readings converge to `g x + g y`. Exact additivity
is thus the limit of approximate additivity — the standard Aczél/Hölder passage. -/

/-- **Count is super-additive (with the natural off-by-one).** `dcount x n + dcount y n + 1 ≤
dcount (F x y) n`: the copies fitting under `x` and under `y`, combined via `F`, fit under
`F x y`. Uses order-preservation (`hmono`) and the iterate law `Fpow_add`. -/
theorem dcount_add_le {x y : ℝ} (hx : S.u ≤ x) (hy : S.u ≤ y) (n : ℕ) :
    S.dcount x n + S.dcount y n + 1 ≤ S.dcount (S.F x y) n := by
  set P := S.dcount x n
  set Q := S.dcount y n
  have hxy : S.u ≤ S.F x y := le_of_lt (lt_of_le_of_lt hx (S.hpos y x))
  have hP : Fpow S.F (S.droot n) P ≤ x := (S.dcount_spec hx n P).mpr le_rfl
  have hQ : Fpow S.F (S.droot n) Q ≤ y := (S.dcount_spec hy n Q).mpr le_rfl
  have hcomb : Fpow S.F (S.droot n) (P + Q + 1) ≤ S.F x y := by
    rw [Fpow_add S.hassoc]
    exact S.hmono _ _ _ _ hP hQ
  exact (S.dcount_spec hxy n (P + Q + 1)).mp hcomb

/-- **Count is sub-additive up to a constant.** `dcount (F x y) n ≤ dcount x n + dcount y n + 3`:
if `x` sits below `P+1` copies and `y` below `Q+1` copies of the root, then `F x y` sits below
`(P+1)+(Q+1)+1 = P+Q+3` copies, capping its count. -/
theorem dcount_le_add {x y : ℝ} (hx : S.u ≤ x) (hy : S.u ≤ y) (n : ℕ) :
    S.dcount (S.F x y) n ≤ S.dcount x n + S.dcount y n + 3 := by
  set P := S.dcount x n
  set Q := S.dcount y n
  have hxy : S.u ≤ S.F x y := le_of_lt (lt_of_le_of_lt hx (S.hpos y x))
  have hxle : x ≤ Fpow S.F (S.droot n) (P + 1) := by
    have hne : ¬ Fpow S.F (S.droot n) (P + 1) ≤ x := by rw [S.dcount_spec hx n (P + 1)]; omega
    exact le_of_lt (not_le.mp hne)
  have hyle : y ≤ Fpow S.F (S.droot n) (Q + 1) := by
    have hne : ¬ Fpow S.F (S.droot n) (Q + 1) ≤ y := by rw [S.dcount_spec hy n (Q + 1)]; omega
    exact le_of_lt (not_le.mp hne)
  have hcomb : S.F x y ≤ Fpow S.F (S.droot n) (P + Q + 3) := by
    have h1 : S.F x y ≤ Fpow S.F (S.droot n) ((P + 1) + (Q + 1) + 1) := by
      rw [Fpow_add S.hassoc]
      exact S.hmono _ _ _ _ hxle hyle
    rwa [show (P + 1) + (Q + 1) + 1 = P + Q + 3 from by ring] at h1
  have hR : Fpow S.F (S.droot n) (S.dcount (S.F x y) n) ≤ S.F x y :=
    (S.dcount_spec hxy n (S.dcount (S.F x y) n)).mpr le_rfl
  exact (Fpow_strictMono (S.pos n)).le_iff_le.mp (le_trans hR hcomb)

/-- Lower reading bound: `gₙx + gₙy + 2⁻ⁿ ≤ gₙ(F x y)`. Real form of `dcount_add_le`. -/
theorem gapprox_add_lower {x y : ℝ} (hx : S.u ≤ x) (hy : S.u ≤ y) (n : ℕ) :
    S.gapprox x n + S.gapprox y n + (1 / 2 ^ n : ℝ) ≤ S.gapprox (S.F x y) n := by
  have hd : (S.dcount x n : ℝ) + S.dcount y n + 1 ≤ S.dcount (S.F x y) n := by
    exact_mod_cast S.dcount_add_le hx hy n
  simp only [Scale.gapprox]
  rw [← add_div, ← add_div]
  gcongr

/-- Upper reading bound: `gₙ(F x y) ≤ gₙx + gₙy + 3·2⁻ⁿ`. Real form of `dcount_le_add`. -/
theorem gapprox_add_upper {x y : ℝ} (hx : S.u ≤ x) (hy : S.u ≤ y) (n : ℕ) :
    S.gapprox (S.F x y) n ≤ S.gapprox x n + S.gapprox y n + (3 / 2 ^ n : ℝ) := by
  have hd : (S.dcount (S.F x y) n : ℝ) ≤ S.dcount x n + S.dcount y n + 3 := by
    exact_mod_cast S.dcount_le_add hx hy n
  simp only [Scale.gapprox]
  rw [← add_div, ← add_div]
  gcongr

/-- **Additivity of the generator:** `g (F x y) = g x + g y` on the cone. The readings of
`F x y` are squeezed between two sequences both tending to `g x + g y` (the `2⁻ⁿ` slack from
the finite-level off-by-ones vanishing), and also tend to `g (F x y)`; uniqueness concludes.
This is the property that makes `g` an additive generator — Aczél's theorem, bar the final
order-embedding assembly. -/
theorem g_additive {x y : ℝ} (hx : S.u ≤ x) (hy : S.u ≤ y) :
    S.g (S.F x y) = S.g x + S.g y := by
  have hxy : S.u ≤ S.F x y := le_of_lt (lt_of_le_of_lt hx (S.hpos y x))
  have hz : Filter.Tendsto (fun n : ℕ => (1 / 2 ^ n : ℝ)) Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact h.congr (fun n => by rw [inv_pow, one_div])
  have hz3 : Filter.Tendsto (fun n : ℕ => (3 / 2 ^ n : ℝ)) Filter.atTop (nhds 0) := by
    have h := hz.const_mul (3 : ℝ)
    rw [mul_zero] at h
    exact h.congr (fun n => by rw [mul_one_div])
  have hlow : Filter.Tendsto (fun n => S.gapprox x n + S.gapprox y n + 1 / 2 ^ n)
      Filter.atTop (nhds (S.g x + S.g y)) := by
    have h := ((S.gapprox_tendsto hx).add (S.gapprox_tendsto hy)).add hz
    simpa using h
  have hupp : Filter.Tendsto (fun n => S.gapprox x n + S.gapprox y n + 3 / 2 ^ n)
      Filter.atTop (nhds (S.g x + S.g y)) := by
    have h := ((S.gapprox_tendsto hx).add (S.gapprox_tendsto hy)).add hz3
    simpa using h
  have hsq : Filter.Tendsto (S.gapprox (S.F x y)) Filter.atTop (nhds (S.g x + S.g y)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
      (fun n => S.gapprox_add_lower hx hy n) (fun n => S.gapprox_add_upper hx hy n)
  exact tendsto_nhds_unique (S.gapprox_tendsto hxy) hsq

/-- **The generator exists, with its defining properties, on the cone.** Packages the
construction: every `Scale` carries a real-valued `g` that is normalized (`g u = 1`), turns the
combination into addition (`g (F x y) = g x + g y`), and is monotone — an additive generator in
the sense of Aczél/Hölder, restricted to the positive cone `b ≥ u`. What remains to reach the
full `HasOrderedGenerator` (hence `AczelStatement`) is upgrading monotone to *strict* (the
dyadic-density/Archimedean argument) and extending off the cone. -/
theorem exists_additive_generator :
    ∃ g : ℝ → ℝ, g S.u = 1 ∧
      (∀ x y, S.u ≤ x → S.u ≤ y → g (S.F x y) = g x + g y) ∧
      (∀ x y, S.u ≤ x → x ≤ y → g x ≤ g y) :=
  ⟨S.g, S.g_unit, fun _ _ hx hy => S.g_additive hx hy, fun _ _ hx hxy => S.g_mono hx hxy⟩

/-! ### Strict growth in the large

Additivity + normalization already give strict monotonicity *at unit scale*: crossing a whole
unit raises `g` by at least one. This makes `g` unbounded and injective on any unit-spaced
subsequence. (Full `StrictMono` in the small — needing the roots to shrink to the additive
identity, `F x (droot n) → x` — is then proved below as `g_strictMono_cone`.) -/

/-- On the cone, `g ≥ 1` (monotonicity from the normalized unit). -/
theorem one_le_g {x : ℝ} (hx : S.u ≤ x) : 1 ≤ S.g x :=
  S.g_unit ▸ S.g_mono (le_refl S.u) hx

/-- **Strict growth in the large.** If `y` dominates `x` combined with a whole unit
(`F x u ≤ y`), then `g` jumps by at least one: `g x + 1 ≤ g y`. Immediate from additivity
(`g (F x u) = g x + g u = g x + 1`) and monotonicity. -/
theorem g_add_one_le {x y : ℝ} (hx : S.u ≤ x) (hxy : S.F x S.u ≤ y) :
    S.g x + 1 ≤ S.g y := by
  have hu : S.u ≤ S.F x S.u := le_of_lt (lt_of_le_of_lt hx (S.hpos S.u x))
  have hadd : S.g (S.F x S.u) = S.g x + 1 := by
    rw [S.g_additive hx (le_refl S.u), S.g_unit]
  rw [← hadd]
  exact S.g_mono hu hxy

/-- Consequently `g` is strictly monotone across a unit step: `F x u ≤ y ⟹ g x < g y`. -/
theorem g_lt_of_unit_le {x y : ℝ} (hx : S.u ≤ x) (hxy : S.F x S.u ≤ y) : S.g x < S.g y :=
  lt_of_lt_of_le (lt_add_one _) (S.g_add_one_le hx hxy)

/-! ### Full strict monotonicity

The roots shrink to the additive identity, which lets a target `y > x` always be reached from
`x` by adjoining a whole (fine) root. That root contributes a fixed positive amount `2⁻ᴹ` to the
count at every level, so `g y ≥ g x + 2⁻ᴹ`: strict monotonicity, with no continuity of `g`
needed. -/

/-- The root tower is **unbounded below** — mirror of `Fpow_not_bddAbove`. Were it bounded, it
would converge to a diagonal fixed point `F L L = L`, impossible since `L < F L L`. -/
theorem droot_not_bddBelow : ¬ BddBelow (Set.range S.droot) := by
  intro hbdd
  set L := ⨅ n, S.droot n with hLdef
  have hanti := (droot_strictAnti' S.hdiv S.hdiag S.u).antitone
  have hL : Filter.Tendsto S.droot Filter.atTop (nhds L) := tendsto_atTop_ciInf hanti hbdd
  have hshift : Filter.Tendsto (fun n => S.droot (n + 1)) Filter.atTop (nhds L) :=
    hL.comp (Filter.tendsto_add_atTop_nat 1)
  have hdiagcont : Continuous (fun x => S.F x x) :=
    S.hcont.comp (continuous_id.prodMk continuous_id)
  have hcomp : Filter.Tendsto (fun n => S.F (S.droot (n + 1)) (S.droot (n + 1)))
      Filter.atTop (nhds (S.F L L)) := (hdiagcont.tendsto L).comp hshift
  have heq : (fun n => S.F (S.droot (n + 1)) (S.droot (n + 1))) = fun n => S.droot n := by
    funext n; exact droot_succ_double S.F S.hdiv S.u n
  rw [heq] at hcomp
  exact absurd (tendsto_nhds_unique hcomp hL).symm (ne_of_lt (S.hdiag L))

/-- Hence the roots run off to `−∞`. -/
theorem droot_tendsto_atBot : Filter.Tendsto S.droot Filter.atTop Filter.atBot := by
  rw [Filter.tendsto_atBot]
  intro b
  have h := S.droot_not_bddBelow
  rw [not_bddBelow_iff] at h
  obtain ⟨c, ⟨N, rfl⟩, hcb⟩ := h b
  filter_upwards [Filter.eventually_ge_atTop N] with m hm
  exact le_of_lt (lt_of_le_of_lt ((droot_strictAnti' S.hdiv S.hdiag S.u).antitone hm) hcb)

/-- **The roots shrink to the identity:** `F x (droot n) → x`. Composition of the boundary
condition `hbot` with `droot → −∞`. -/
theorem roots_shrink (x : ℝ) :
    Filter.Tendsto (fun n => S.F x (S.droot n)) Filter.atTop (nhds x) :=
  (S.hbot x).comp S.droot_tendsto_atBot

/-- **Count amplification.** Adjoining the `M`-th root to `x` adds a *full block* of `2^(n-M)`
copies at every finer level `n ≥ M`: `dcount x n + 2^(n-M) ≤ dcount (F x (droot M)) n`. The block
is the level-`n` expansion of `droot M` (via `Fpow_droot_add`), lifted through `F` by `hmono`. -/
theorem dcount_shift_ge {x : ℝ} (hx : S.u ≤ x) (M : ℕ) {n : ℕ} (hMn : M ≤ n) :
    S.dcount x n + 2 ^ (n - M) ≤ S.dcount (S.F x (S.droot M)) n := by
  have hFu : S.u ≤ S.F x (S.droot M) := le_of_lt (lt_of_le_of_lt hx (S.hpos (S.droot M) x))
  have hP : Fpow S.F (S.droot n) (S.dcount x n) ≤ x := (S.dcount_spec hx n _).mpr le_rfl
  have hone : (1 : ℕ) ≤ 2 ^ (n - M) := Nat.one_le_pow _ 2 (by norm_num)
  have hdM : Fpow S.F (S.droot n) (2 ^ (n - M) - 1) = S.droot M := by
    have h := Fpow_droot_add S.hdiv S.hassoc S.u M 0 (n - M)
    rw [Nat.add_sub_cancel' hMn, zero_add, mul_one] at h
    simpa [Scale.droot] using h
  have hcomb : Fpow S.F (S.droot n) (S.dcount x n + 2 ^ (n - M)) ≤ S.F x (S.droot M) := by
    rw [show S.dcount x n + 2 ^ (n - M) = S.dcount x n + (2 ^ (n - M) - 1) + 1 from by omega,
      Fpow_add S.hassoc, hdM]
    exact S.hmono _ _ _ _ hP (le_refl _)
  exact (S.dcount_spec hFu n _).mp hcomb

/-- **`g` is strictly monotone on the cone.** For `u ≤ x < y`: shrink a root `droot M` small
enough that `F x (droot M) ≤ y` (possible by `roots_shrink`), then the block of `2^(n-M)` extra
copies gives `gₙ y ≥ gₙ x + 2⁻ᴹ` at every level, so in the limit `g y ≥ g x + 2⁻ᴹ > g x`. This
is the order-embedding property Hölder's theorem delivers. -/
theorem g_strictMono_cone {x y : ℝ} (hx : S.u ≤ x) (hxy : x < y) : S.g x < S.g y := by
  have hy : S.u ≤ y := le_of_lt (lt_of_le_of_lt hx hxy)
  obtain ⟨M, hM⟩ := ((S.roots_shrink x).eventually_mem (isOpen_Iio.mem_nhds hxy)).exists
  have hMy : S.F x (S.droot M) ≤ y := le_of_lt hM
  have hMu : S.u ≤ S.F x (S.droot M) := le_of_lt (lt_of_le_of_lt hx (S.hpos (S.droot M) x))
  -- reading bound at every level `n ≥ M`
  have hstep : ∀ n, M ≤ n → S.gapprox x n + 1 / 2 ^ M ≤ S.gapprox y n := by
    intro n hMn
    have hcnt : (S.dcount x n : ℝ) + 2 ^ (n - M) ≤ (S.dcount y n : ℝ) := by
      have h1 := S.dcount_shift_ge hx M hMn
      have h2 := S.dcount_mono hMu hMy n
      have : S.dcount x n + 2 ^ (n - M) ≤ S.dcount y n := le_trans h1 h2
      exact_mod_cast this
    have hpoweq : (2 : ℝ) ^ (n - M) / 2 ^ n = 1 / 2 ^ M := by
      rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
      congr 1
      omega
    simp only [Scale.gapprox]
    rw [← hpoweq, ← add_div]
    gcongr
  -- pass to the limit
  have hlim : S.g x + 1 / 2 ^ M ≤ S.g y :=
    le_of_tendsto_of_tendsto ((S.gapprox_tendsto hx).add_const (1 / 2 ^ M)) (S.gapprox_tendsto hy)
      (Filter.eventually_atTop.2 ⟨M, fun n hn => hstep n hn⟩)
  have hpos : (0 : ℝ) < 1 / 2 ^ M := by positivity
  linarith

/-- **Hölder's theorem on the cone (additive form).** Every scale carries a normalized, strictly
monotone, additive generator on its positive cone: the analytic content of Aczél's theorem,
complete and self-contained. What separates this from the global `HasOrderedGenerator` (hence
`AczelStatement`) is only the transport to the bounded `[0,1]` conjunction picture and the
extension below the unit — the axiom-choice questions, not further analysis. -/
theorem exists_ordered_generator :
    ∃ g : ℝ → ℝ, g S.u = 1 ∧
      (∀ x y, S.u ≤ x → S.u ≤ y → g (S.F x y) = g x + g y) ∧
      (∀ x y, S.u ≤ x → x < y → g x < g y) :=
  ⟨S.g, S.g_unit, fun _ _ hx hy => S.g_additive hx hy,
    fun _ _ hx hxy => S.g_strictMono_cone hx hxy⟩

/-- **Hölder's theorem on the cone (multiplicative form).** Regraduating by `exp` turns the
additive generator into a strictly monotone *multiplicative* one, `G (F x y) = G x * G y` — the
exact conclusion shape of `AczelStatement`, established on the cone. -/
theorem exists_mul_generator :
    ∃ G : ℝ → ℝ,
      (∀ x y, S.u ≤ x → S.u ≤ y → G (S.F x y) = G x * G y) ∧
      (∀ x y, S.u ≤ x → x < y → G x < G y) := by
  refine ⟨fun b => Real.exp (S.g b), fun x y hx hy => ?_, fun x y hx hxy => ?_⟩
  · change Real.exp (S.g (S.F x y)) = Real.exp (S.g x) * Real.exp (S.g y)
    rw [S.g_additive hx hy, Real.exp_add]
  · change Real.exp (S.g x) < Real.exp (S.g y)
    exact Real.exp_lt_exp.mpr (S.g_strictMono_cone hx hxy)

/-! ### M4 — the bridge to `AczelStatement` (the product-rule half of Cox)

`AczelStatement` (`Cox.lean`) asks that a continuous, per-argument strictly monotone, associative
`F` on `[0,1]` be conjugate to multiplication by a `StrictMonoOn` *and* `ContinuousOn` generator.
The theorem below delivers exactly that conclusion **on the positive cone** `[u, ∞)` and **minus
continuity**: a `Scale` (Aczél's hypotheses in the growing/positive-cone orientation) regraduates
its conjunction functional to multiplication by a generator that is strictly monotone on the cone.

Two gaps remain between this and the verbatim `AczelStatement`, and both are genuine analysis, not
bookkeeping:
* **Continuity.** The generator `g` built here is *discontinuous at the unit* — it is `0` below
  `u` and `1` at `u`, because additivity only holds on the cone. A continuous generator (e.g.
  `exp` for the archetype `F x y = log(eˣ+eʸ)`) requires extending `g` below the unit by group
  completion; that extension is the missing `ContinuousOn` half.
* **Reorientation.** `AczelStatement` lives on the bounded conjunction picture `[0,1]` (where
  `F x y ≤ x`), whereas a `Scale` is the growing/`t`-conorm orientation (`x < F x c`). The two are
  related by an order-reversing transport (`−log`), which must be supplied to land on `[0,1]`.

So M4 is *reduced*, not closed: the algebraic and order content of the product rule is proved on
the cone; the residual is the continuity/off-cone extension and the interval reorientation. -/
theorem aczelStatement_cone :
    ∃ G : ℝ → ℝ,
      (∀ x y, S.u ≤ x → S.u ≤ y → G (S.F x y) = G x * G y) ∧
      StrictMonoOn G (Set.Ici S.u) := by
  obtain ⟨G, hmul, hmono⟩ := S.exists_mul_generator
  exact ⟨G, hmul, fun _ hx _ _ hxy => hmono _ _ hx hxy⟩

end Scale

/-! ### A concrete `Scale`: the log-sum-exp archetype

Everything in the `Scale` namespace is quantified over `∀ S : Scale`, so it is only meaningful if
`Scale` is inhabited. It is: `F x y = log (eˣ + eʸ)` with unit `0` satisfies every field, and its
additive generator is `exp` (`exp (F x y) = eˣ + eʸ`). This guards the capstones against vacuity,
exactly as `nonempty_coxModel` guards the Cox side. -/

/-- The **log-sum-exp scale** `F x y = log (eˣ + eʸ)`, unit `0`. A concrete inhabitant of
`Scale`, so the Aczél/Hölder capstones are not vacuous. -/
noncomputable def logSumExpScale : Scale where
  F x y := Real.log (Real.exp x + Real.exp y)
  hdiv c := ⟨c - Real.log 2, by
    have h : Real.exp (c - Real.log 2) + Real.exp (c - Real.log 2) = Real.exp c := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring
    rw [h, Real.log_exp]⟩
  hassoc x y z := by
    rw [Real.exp_log (by positivity), Real.exp_log (by positivity), add_assoc]
  hpos c x :=
    calc x = Real.log (Real.exp x) := (Real.log_exp x).symm
      _ < Real.log (Real.exp x + Real.exp c) :=
          Real.log_lt_log (Real.exp_pos x) (by linarith [Real.exp_pos c])
  hmono x₁ x₂ y₁ y₂ hx hy :=
    Real.log_le_log (by positivity)
      (add_le_add (Real.exp_le_exp.mpr hx) (Real.exp_le_exp.mpr hy))
  hcont := by
    apply Continuous.log
    · exact (Real.continuous_exp.comp continuous_fst).add (Real.continuous_exp.comp continuous_snd)
    · intro p; positivity
  hbot x := by
    have h1 : Filter.Tendsto (fun z => Real.exp x + Real.exp z) Filter.atBot
        (nhds (Real.exp x)) := by
      simpa using tendsto_const_nhds.add Real.tendsto_exp_atBot
    have h2 := (Real.continuousAt_log (by positivity : Real.exp x ≠ 0)).tendsto.comp h1
    rwa [Real.log_exp] at h2
  u := 0

/-- The `Scale` hypotheses are consistent: the Aczél/Hölder capstones are non-vacuous. -/
theorem nonempty_scale : Nonempty Scale := ⟨logSumExpScale⟩

end ConstructiveProb.Aczel
