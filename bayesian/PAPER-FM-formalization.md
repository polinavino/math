# Paper 1 (FM) — planning doc: the machine-checked development

**Working titles**
- *A Machine-Checked Theory of Probability over Constructive Logic*
- *Localic Probability in Lean: Valuations, a Corrected Cox Theorem, and the Aczél Generator*
- *When You Drop Excluded Middle: Formalizing Intuitionistic Probability in Lean/mathlib*

**Target venue.** ITP (primary) — longer papers, formalization-first, room for the analytic
content. CPP (alternative — but note the companion `forcing-hoare` project is CPP-2027-bound, so
ITP avoids competing with your own submission in the same cycle). Journal escalation: JAR.
**Artifact evaluation:** the `ConstructiveProb/` repo *is* the artifact — sorry-free, axiom-clean,
builds against pinned Lean/mathlib `v4.31.0`. This is a strength; budget for the AE submission.

---

## One-paragraph thesis (FM framing)

Cox–Jaynes probability is "logic extended to handle uncertainty," but the logic is always tacitly
classical. We give the **first Lean/mathlib formalization** of what the same recipe yields over
**constructive (Heyting/localic) logic**: a modular *valuation* on a frame, whose failure of the
complement rule `v(¬A) = 1 − v(A)` is machine-checked to be *exactly* the failure of excluded
middle, and which coincides with a Dempster–Shafer belief function. The contribution is the
mechanization itself — a from-scratch analytic core (Aczél/Hölder) that mathlib lacked, sharp
results on what the constructive setting *forces* on the Cox program (the sum rule must be posited
and is provably underivable), and a reusable localic-valuation library.

**Why this is a formalization paper, not a mathematics paper:** the conceptual object is prior art
(Weatherson 2003; Paris 1994; Vickers 1989). We say so plainly. The novelty is (i) first machine
checking, (ii) the corrections mechanization surfaced, (iii) reusable infrastructure.

---

## The contributions to foreground (ranked)

*Overarching framing claim: this is the **first machine-checked development** of localic /
intuitionistic probability (valuations, Cox, Dempster–Shafer) in Lean/mathlib. That is the paper's
reason to exist; the ranked items below are the technical meat. Note none of the results "corrects
a known theorem" — Cox's and Aczél's classical theorems are fine. What the formalization delivers is
new infrastructure and sharp results about the **constructive** case.*

1. **The Aczél/Hölder generator, built from scratch** (`Aczel.lean`, ~1000 lines) — the hardest and
   most reusable part. Per the project's own survey, mathlib has no directly-applicable
   ordered-semigroup / one-parameter-subgroup embedding for interval operations, so we build it: the
   additive generator as a dyadic limit (`g_additive`), the order embedding *without* continuity
   (`g_strictMono_cone`), and Hölder **on the positive cone** (`exists_mul_generator`,
   `aczelStatement_cone`) — plus the order-reversing reorientation to the bounded Cox picture
   (`exists_bounded_mul_generator`) and a continuous *global* generator for the archetype
   (`hasOrderedGenerator_logSumExp`). Honest scope: this is the cone result; the verbatim
   `AczelStatement` on `[0,1]` (continuity + off-cone extension) stays open. A plausible
   mathlib-upstreaming candidate.

2. **The constructive Cox program: the product/sum split, and modularity is irreducible.** This is
   the real Cox content — and it is *not* "we corrected Cox." Classically the sum rule is derived
   from the product rule plus the negation axiom R3 (via De Morgan); constructively that route is
   blocked. We make the split explicit — the **product-rule half is logic-independent** (Aczél, #1)
   and the **sum-rule half is where the logic lives** — and show the sum rule must be *posited* as
   modularity because it is genuinely **underivable**: `modularity_irreducible` exhibits a monotone,
   normalized, disjoint-additive plausibility that is not modular, and `no_disjunction_functional`
   sharpens this to "`q(x⊔y)` is not even a function of the marginals `q x, q y`". Given modularity,
   the regraduation to a `Valuation` is then routine (`constructive_cox`, essentially
   `g = ENNReal.ofReal`; it does not touch `F` or its axioms). *(Formalizing the naive bare statement
   also surfaced that it was ill-posed — it asked for `StrictMono g : ℝ → ℝ≥0∞` with `g 0 = 0`,
   impossible since strictness forces `g(−1) < 0`; the fix restricts strictness to `[0,1]`. A
   formalization-hygiene point about our own first-pass encoding, **not** a flaw in Cox's theorem —
   worth a sentence, not a headline.)*

3. **The R3 hinge, both directions** (`hasClassicalNegation_of_em` /
   `em_of_forall_hasClassicalNegation`): the complement rule `v(¬A) = 1 − v(A)` holds for *every*
   valuation **iff** excluded middle holds. Locates probability's *additive* classicality in exactly
   one axiom (R3). The hard direction manufactures a slack-carrying valuation via the prime-ideal
   separation theorem.

4. **The representation cluster.** Finite representation (`eq_sum_mass`, `toPMF` — a valuation on a
   finite frame *is* a mathlib `PMF`); the infinite obstruction (`topIndicator` — mass escaping to a
   non-principal point); the general inequality (`tsum_mass_le` — atomic ≤ total, a constructive
   analogue of a Lebesgue decomposition); the **mixture characterization on finite frames**
   (`mix` + `deltaPoint` + `eq_mix_deltaPoint` — valuations = finite mixtures of points); and
   **Scott-continuity ⟹ purely atomic** on any locally-finite-below poset (`isPurelyAtomic_of_scott`,
   generalizing the previously `ℕ`-only result).

5. **The bridges.** GMT/measure (`toValuationOpens` — a classical measure read on the opens *is* a
   valuation; `slack = μ(∂U)`); the computability guard (`Halting.lean` — a semi-decidable
   proposition forces positive slack, so no axiom set can collapse the theory to classical logic);
   and the Dempster–Shafer bridge (`two_monotone` — `v↾Booleanization` is a 2-monotone capacity, the
   defining belief-function inequality; `∞`-monotonicity remains open).

6. **Hygiene.** Sorry-free; every landmark depends only on `propext, Classical.choice, Quot.sound`
   (verified by `#print axioms`); **~3,000 lines (3,021)** across nine modules; clean build, no
   warnings.

---

## Section outline

1. **Introduction.** Probability = extended logic; the tacit classical assumption; what changes over
   Heyting; why mechanize (first in Lean; what the constructive setting forces). Contributions list.
2. **The valuation structure.** `Valuation` on `Order.Frame`; monotone, normalized, modular, *no*
   complement law. Core API: `slack` and its two-gap decomposition, disjoint additivity vs. the
   complement rule, conditioning (`condVal`, product rule, Bayes symmetry), the classical fragment.
3. **Where classicality lives: the R3 hinge.** The ⟺ theorem; the prime-ideal construction.
4. **The constructive Cox program.** The product/sum split; modularity as the constructive
   replacement for R3, and why it must be posited (`modularity_irreducible` /
   `no_disjunction_functional`); the routine regraduation; the ill-posed-naive-statement hygiene note.
5. **The analytic core: Aczél/Hölder in Lean.** What mathlib lacked; the dyadic-limit generator; the
   cone results; reorientation; the archetype witness; the residual open analysis (continuity /
   off-cone extension) stated honestly.
6. **Representation theorems.** Finite → obstruction → general inequality → mixture characterization
   → Scott ⟹ atomic. The `PMF` identification.
7. **Bridges.** GMT/measure model; computability guard; Dempster–Shafer 2-monotonicity.
8. **Engineering & reuse.** Design of the `Valuation` API; mathlib-upstreaming candidates (Aczél
   generator; localic valuations); axiom audit; build/artifact notes.
9. **Related formalizations & open items.** Coq ALEA, cubical Agda (Sargsyan — Markov-category, does
   not overlap); the open analytic frontier and M3c.

---

## Positioning / novelty (defensive map — see `ConstructiveProb/RELATED_WORK.md`)

- **Object is not new:** localic valuation (Vickers), intuitionistic probability (Weatherson),
  non-classical prob = DS belief functions (Paris/Shafer), `Bel = P(□φ)` (Ruspini/Smets/Pearl), GMT
  bridge (standard). Lead with "first mechanization," not "new object."
- **mathlib has none of this** (confirmed by inspection: measure theory yes; MV-algebras / effect
  algebras / states-on-algebras / DS / localic valuations — none; mathlib's `Valuation` is the
  valued-field notion). Doing it in Lean is itself unclaimed.
- **Prior formalization — be precise (a reviewer will check).** The *object* (modular localic
  valuation) **is** already formalized, in Coq/HoTT, by Bidlingmaier–Faissole–Spitters
  (`FFaissole/Valuations`) — but as constructive *measure theory* (Riesz/Fubini, Lebesgue valuation,
  Giry monad), Scott-continuous, for probabilistic programming. What is unformalized anywhere is the
  development here: the logic-weakening reading, slack, the R3 hinge, Cox + Aczél, our
  representation/mixture/Scott-atomic theorems, the halting guard, the DS bridge. ALEA (Coq,
  distribution monad) and Sargsyan (cubical Agda, Markov categories) are a *different object*
  (additive distributions), no overlap. **Do not claim "first formalization of valuations"; claim
  "first formalization of the constructive/non-additive Cox–DS development on them."**

## Honest scoping (state as future work, do not hide)

- Continuity + off-cone extension of the Aczél generator (the group completion needs commutativity
  of `F` off the cone, ≈ the theorem itself) — the verbatim `AczelStatement` on `[0,1]` remains open.
- Full representation M3c: the diffuse part for non-spatial / non-Scott frames.
- `∞`-monotonicity of the DS bridge (only 2-monotonicity proved).

## Soundbites / hooks for the abstract

- "Probability's additivity *is* excluded middle — proved as an iff."
- "Constructively the sum rule cannot be earned, only assumed — we prove modularity is underivable."
- "A valuation on a finite frame is literally a mathlib `PMF`."
- "For a semi-decidable proposition, classical probability is provably wrong — the slack is forced."
- "First machine-checked account of what probability becomes when you drop excluded middle."

## Sequencing note

Ship this **first**. Beyond its own merit it is the citable rigor anchor for Paper 2
(`PAPER-PHIL-foundations.md`): "every claim machine-checked, see [1]" pre-empts a philosophy
referee's rigor worries.
