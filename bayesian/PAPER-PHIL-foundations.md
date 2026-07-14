# Paper 2 (Phil / FoM) — planning doc: the conceptual & foundational take

*Self-contained: everything the paper needs is stated here, not deferred to the handoff notes.
Where it draws on your metaphysics, it restates the position in-line. Two places are flagged
**[reconcile]** where the plan should be checked against your latest private notes before drafting.*

**Working titles**
- *The Logic Fixes the Probability: Constructive Logic and Non-Additive Credence*
- *Probability Without Points: Localic Credence and the Measure of the Undecided*
- *Excluded Middle Is Additivity: What Probability Becomes over Constructive Logic*

**Target venue.** *Review of Symbolic Logic* (RSL) — bridges formal and philosophical work; its
readers know locale theory and constructive logic. Alternatives: *Journal of Philosophical Logic*
(more logic, less metaphysics room), *Studia Logica* (strongest for the algebraic-logic / DS-on-
Heyting spine), *Philosophia Mathematica* (if the FoM/structuralism thesis leads). Ship the FM paper
(`PAPER-FM-formalization.md`) first as the rigor anchor: "every claim machine-checked, see [1]".

---

## 0. One-paragraph thesis

Cox and Jaynes argued that probability is the unique rational way to extend *logic* to graded
certainty — but the logic they extend is silently **classical**. Make the logic a dial. Extend
**constructive (Heyting / localic) logic** instead, and the complement rule `P(¬A) = 1 − P(A)`
*must* break; what appears is a non-additive calculus — a Dempster–Shafer belief function — whose
"missing mass", the **slack** `1 − P(A) − P(¬A)`, is not anyone's ignorance but a **structural**
quantity: the measure of the region excluded middle leaves undecided (concretely `μ(∂U)`, the
measure of a topological boundary). Three claims follow. **(1) Additivity is classicality**: the
complement rule holds for every credence *iff* excluded middle holds, so for genuinely non-classical
propositions — paradigmatically the undecidable — additive probability is provably inappropriate,
and the slack *measures* undecidedness. **(2) Credence is structure, not belief**: read through
pointless topology a credence is a measure on a locale and its slack is geometry — matching an
ontology on which structure is primary and "points"/"objects" derived. **(3) The choice of logic is
the missing dial** that turns one theory of graded certainty into another: classical logic →
Kolmogorov probability, Heyting logic → Dempster–Shafer. This *resolves* a standing problem in the
broader program (§7 below): non-additive credences are not ad hoc rivals to probability but *what
probability becomes* when its underlying logic is weakened, exactly as probability is what logic
becomes when certainty is weakened. Every formal claim is machine-checked (Paper 1).

---

## 1. The metaphysical setting (stated in-line, so the paper is self-contained)

The paper does **not** need to win the reader to a full metaphysics; it needs to state a coherent
ontology on which constructive/localic probability is the *natural*, not arbitrary, choice. That
ontology is **Humean structural realism** (eternalist, anti-plenitude):

- **Structure is fundamental.** The world *is* a mathematical structure — identity, not
  implementation-in-a-substrate ("content without a vehicle": structure that obtains directly, not
  encoded in any medium). **[reconcile]** with your latest formulation; an older note said "minimal
  physical implementation of a structure", the refined position is no-vehicle identity.
- **Points/objects are derived, not primitive.** Individuals are positions in structure; "this
  electron" is a node, not a substance. This is the ontological hinge the probability story needs.
- **Laws are Humean.** In an eternalist block, laws/chances/determinism *supervene* on the total
  mosaic (Best-Systems style); they do not generate it. Corollary (the *Humean constraint*): the
  dynamical rules are not provable a priori — that gravity holds tomorrow, or that one stick and one
  stick make two sticks, is observed-to-be-instantiated, never proved from first principles.
- **Divergence from canonical OSR.** Ladyman–Ross OSR is *anti*-Humean (it wants modal structure
  built in); this position keeps Humean supervenience. Say so — it is where the view is
  under-occupied rather than merely a restatement. (Honest self-assessment: the *fusion* — Humean +
  eternalist + anti-plenitude + no-vehicle identity — is an under-occupied spot, a modest
  contribution, not a landmark. The paper's novelty is the *link* to the logic-of-probability
  thesis and the formal results, not the metaphysics as such.)

**Why probability enters, and why it needs a prior.** Probability is itself a mathematical structure
— like the derivative or the integral — for which there is no proof the world follows it, only
observation that it is instantiated (the Humean constraint again). What distinguishes it from other
mathematical structures is that it is *constitutively designed for incomplete information*, and so
requires an extra input — a **prior** — that is not read off any single fact but supplied by the
structure of the situation.

**Epistemic situation, not epistemic agent (the central refinement).** Framing probability around an
*agent* smuggles in a believing subject, a perspective, intentionality — psychologism that clashes
with structure-first realism. Replace the agent with the **epistemic situation**: the set of
available structural information (facts, constraints, symmetries, known relations) from which
inferences follow, with or without a mind to draw them.

- **Logic** = the conclusions *fully* determined by the epistemic situation.
- **Probability** = the unique well-behaved measure *partially* determined by it.
- The **prior** is the background structural information already in the situation (symmetries, known
  constraints) — *read off* the situation's structure, not chosen by anyone.

This is the philosophical counterpart of the code's de-psychologized stance ("an epistemic
situation, not an epistemic agent"), and it is what lets `slack` be geometry rather than doubt.

---

## 2. Probability as extended logic — and the hidden parameter

- Recap Cox/Jaynes: a consistent calculus of graded certainty that reproduces the logic's truth
  tables in the certain limit is (a rescaling of) probability. The Boolean-algebra special case: the
  `{0,1}`-valued restriction of a probability measure *is* classical propositional logic.
- The *reverse* direction (Paris–Vencovská): a logic of partial belief that reduces to classical
  logic at the extremes, is continuous, and respects symmetry/consistency *must* be probability.
  Together these say classical logic and classical probability are two ends of one axis (certainty
  ↔ uncertainty).
- **The hidden parameter.** All of this fixes the logic to be classical. That is a *free choice*,
  and it is exactly what the rest of the paper varies. (Precedent that "the logic fixes the shape of
  the probability" is a genuine theorem, not a slogan: Gleason for quantum/orthomodular logic.)

---

## 3. Turning the dial to Heyting: what breaks, what survives

- **Breaks:** the complement rule `P(¬A) = 1 − P(A)`; total probability over `{A, ¬A}` (they no
  longer tile ⊤); the clean "distribution on points" picture; Cox's own uniqueness proof (it uses
  double-negation elimination).
- **Survives:** modularity (inclusion–exclusion), disjoint additivity, conditioning and Bayes' rule.
- **Moral:** classical probability *bundles* several things that are only separately true.
  Unbundling them — seeing which were secretly excluded middle — is the content of the paper.

---

## 4. The hinge: additivity *is* excluded middle

The centerpiece argument. `P(¬A) = 1 − P(A)` holds for *every* credence **iff** `A ∨ ¬A = ⊤`
(machine-checked: `hasClassicalNegation_of_em` / `em_of_forall_hasClassicalNegation`). So additivity
is not a neutral norm of rationality (contra the usual Dutch-book reading) but a *commitment to
classical logic about the propositions in play*. Engage the Cox / Dutch-book / "why be a Bayesian"
literature here: the norm is conditional on the logic, and the logic is a substantive assumption.

---

## 5. Why this resolves an open problem in the framework

A standing problem in the broader program: Dempster–Shafer belief functions, possibility theory, and
imprecise probabilities *also* reduce to logic at the extremes and are continuous in some sense, yet
violate Kolmogorov additivity. The unified "probability = extended logic" picture had to either
**exclude** them or **accommodate** them as legitimate generalizations — and had no principled way to
decide. **This paper's thesis decides it: they are accommodated, and non-arbitrarily.** DS belief
functions are *precisely* what the Cox recipe yields when the underlying logic is Heyting rather than
Boolean (`two_monotone`: a valuation restricted to the Booleanization is a 2-monotone capacity, i.e.
a belief function). The generalization ladder is now uniform:

> logic  ⟵(weaken certainty)⟵  Kolmogorov probability  ⟵(weaken the logic: Boolean→Heyting)⟵  Dempster–Shafer

Non-additivity is not a defect or a rival framework; it is the shadow of a weaker logic, exactly as
uncertainty is the shadow of weaker-than-deductive information.

---

## 6. Decidability made measurable; de-psychologizing belief and priors

- **Decidability as a measurable quantity.** `slack` is zero for decided propositions and positive
  otherwise, so it *measures* how undecided a proposition is. The halting theorem: a semi-decidable
  ("machine halts") proposition is an open in the Sierpiński/observational topology, cannot be
  refuted by a finite computation, and its natural credence (morally Chaitin's Ω) *provably* violates
  the complement rule (`haltingValuation_not_classical`). So for computational propositions classical
  probability is false, not merely inconvenient. **Connect to logical uncertainty** (Garrabrant et
  al.): same phenomenon, but resolved *structurally*, with no logically-non-omniscient agent.
- **Belief without a believer.** DS calls the object a *belief function* and the slack *ignorance*;
  keep the mathematics, drop the agent. The slack is `μ(∂U)` — the measure of a boundary, a fact
  about the space true with no reasoner present (`toValuationOpens`, `slack = μ(∂U)`). `two_monotone`
  makes "`v` is a belief function on the Booleanization" a *structural* statement.
- **Priors without a chooser.** Read the same way, a prior is not an agent's antecedent credence but
  a **choice of measure on the locale** — content, but not agent-content; the "background structural
  information" of §1 made formal. `eq_mix_deltaPoint`/`toPMF` exhibit a credence on a finite frame as
  literally a distribution (a prior) over its points. This also cleanly separates the two things Cox
  leaves free: the *scale* (regraduation `g`) is gauge with no content; the *prior* (the valuation
  `v`) is the genuine content — and note this is a *different* freedom from the notorious
  reparametrization-dependence of maximum-entropy priors (whose fix is the invariant Jeffreys prior).

---

## 7. The structural-realist / foundations-of-mathematics picture

- **Why locales.** If structure is primary and points/objects are derived, the natural mathematics of
  "spaces of possibilities" is **locale theory** (pointless topology), whose internal logic is
  constructive. So extending *constructive* logic is not an arbitrary variation — it is *the*
  probability theory matching the ontology. The classical/point-based picture is the special case
  that presupposes primitive individuals.
- **Spatiality ⟺ decidability.** A locale is *spatial* iff it has "enough decided points"; a
  non-spatial locale (a halting locale, a measure algebra) has too few, and diffuse credence then has
  no point to sit on (`tsum_mass_le`, `isPurelyAtomic_of_scott`, `topIndicator`). Points-as-derived
  at the level of *ontology* mirrors point-representability-as-special at the level of *probability*
  — the same phenomenon twice. This is the paper's deepest structural claim.
- **Constructive/predicative measure theory** (Coquand–Spitters, Vickers) as the mathematical home;
  cite as the setting the full representation problem lives in.

---

## 8. Positioning against named views

| Feature of the view | Closest named view | Where it diverges |
|---|---|---|
| Probability = partial structural determination | Carnap's logical probability | Carnap found no unique confirmation function; here it is grounded in limit behaviour + the logic dial |
| Priors read off structure | Objective Bayes (Jaynes, Williamson) | Drops the agent; priors are structural facts, not prescriptions |
| Coherence / proper scoring | Subjective Bayes (de Finetti, Ramsey) | Drops subjectivity; the epistemic *situation* replaces the agent |
| Certain limit reproduces logic | Cox/Jaynes | Adds the *reverse* (Paris–Vencovská) **and the logic dial** |
| Structure-first ontology | Ontic structural realism (Ladyman–Ross) | Theirs is anti-Humean; this is Humean + eternalist + anti-plenitude |
| Chances supervene on the mosaic | Lewis Humean supervenience / Best Systems | Combined with no-vehicle structural identity |
| Non-additive credence | Weatherson (intuitionistic prob.), Paris/Shafer (DS) | The *object* is theirs; new here is the logic-dial thesis, the structural reading, the decidability results, and machine-checked rigor |
| Quantum extension | QBism | QBism keeps the agent; this does not |

Anticipated objection — "isn't this just Dempster–Shafer relabelled?" — answered by the logical
grounding (the hinge), the decidability theorem, and the ontology; the DS object is a *consequence*,
not the thesis.

---

## 9. What machine-checking buys the philosophy

Not decoration. It converts "one can check that…" into cited theorems, and it *caught a substantive
error*: the informal Cox statement, formalized, was **unsatisfiable** (Paper 1) — itself
philosophically instructive about the gap between the Cox *program* and any rigorous version, and a
concrete rebuttal to the worry that these foundational arguments are too informal to trust. Cite
Paper 1 throughout for proofs; this paper carries the argument.

---

## 10. The broader program — context, NOT this paper

State these as the horizon the thesis sits in, and explicitly defer them (each is its own project):

- **The iterated-limit hierarchy:** classical logic ⟵ classical probability ⟵ (ℏ→0) ⟵ quantum
  (non-commutative) probability. Whether the logic dial extends "downward" to the non-commutative
  case is open.
- **Epistemic vs. ontological gaps:** whether the uncertainty is in-principle removable (hidden
  variables) or not (Copenhagen/GRW); the framework is consistent with both.
- **Principal Principle interface** (Lewis): why an epistemic situation should be constrained by
  objective chances — the level-crossing between quantum and classical probability. Unfinished.
- **Prior uniqueness:** does the epistemic situation *uniquely* fix the prior? Bertrand paradoxes /
  parametrization-dependent Jeffreys priors say not always. Needs an account of when structure
  determines a prior.
- **Emergent probability:** how macro-level credence (a table) relates to micro-level (amplitudes);
  statistical mechanics as the paradigm case.
- **Feyerabend / methodological pluralism:** "situation-relative not agent-relative" reframes
  "anything goes" as "everything conditioned on its epistemic situation."
- **Information-theoretic grounding:** developing "partial structural determination" measured in
  bits (Shannon), grounding the limit behaviour information-theoretically.
- **The law-likeness fork** (from your metaphysics notes, **[reconcile]**): almost all consistent
  structures are noise, so our block's law-likeness is either brute or explained by a real,
  simplicity-weighted (Solomonoff / universal-prior) ensemble — which would cost strict
  anti-plenitude. Bears on "which prior the world carries" but is not needed for this paper's thesis.

---

## 11. Section outline (the actual paper)

1. Probability as extended logic; the tacit classical boundary condition (the free parameter).
2. The metaphysical setting: structure-first realism; epistemic situation not agent; prior as
   structural input. (Compact — enough to motivate, not a full defense.)
3. Turning the dial to Heyting: what breaks, what survives.
4. The hinge: additivity ⟺ excluded middle; consequences for the norms-of-rationality reading.
5. Resolving the accommodation problem: DS = probability over Heyting logic; the uniform ladder.
6. Decidability made measurable; the halting theorem; logical uncertainty.
7. De-psychologizing belief and priors: slack as `μ(∂U)`; prior as measure on the locale.
8. The structural-realist / FoM picture: locales; points-as-derived; spatiality ⟺ decidability.
9. Positioning, objections, and what the formalization buys.
10. Horizon: the broader program (deferred), and the unifying open frontier (M3c = non-spatiality =
    undecidability).

---

## 12. Formal facts to cite (all machine-checked; see Paper 1 / `ConstructiveProb`)

- Additivity ⟺ EM: `hasClassicalNegation_of_em`, `em_of_forall_hasClassicalNegation`.
- Slack = undecided region; two-gap split: `slack_eq_dnGap_add_deMorganGap`; measure model
  `toValuationOpens`, `slack = μ(∂U)`.
- Halting / non-collapse: `exists_halting_slack`, `haltingValuation_not_classical`.
- DS belief function, structurally: `two_monotone`, `self_le_plausibility`, `plausibility_sub_self`.
- Credence = mixture of points ("prior as measure" made precise): `eq_mix_deltaPoint`, `toPMF`.
- Conditioning survives; total probability over `{A,¬A}` fails: `condVal`, `cond_add_compl_le`,
  `total_prob_of_partition`.
- Spatiality ⟺ decidability / atomic–diffuse split: `tsum_mass_le`, `isPurelyAtomic_of_scott`,
  `topIndicator`.
- Constructive Cox (regraduation, positing modularity) + why modularity must be posited:
  `constructive_cox`, `modularity_irreducible`, `no_disjunction_functional`.

---

## 13. What NOT to lead with · soundbites

**Not the lead:** proof-engineering detail (Paper 1's job); a claim of a *new probabilistic object*
(it is Weatherson/Paris) — lead with the *thesis*, the *reading*, and the *ontology*.

**Soundbites**
- "Additivity is not a law of thought; it is a commitment to excluded middle."
- "The missing probability mass is not ignorance — it is the measure of a boundary."
- "A prior is not what an agent believes beforehand; it is which measure the world carries."
- "Undecidability is not a gap the calculus must tolerate; it is a quantity the calculus measures."
- "Probability is what logic becomes under uncertainty; Dempster–Shafer is what probability becomes
  under a weaker logic."
- "If structure is primary and objects derived, credence lives on a locale — and then it is not
  additive."
