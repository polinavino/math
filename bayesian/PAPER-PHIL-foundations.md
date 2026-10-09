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

## 14. Worked-example candidate: noisy mathematics (Wolpert–Kinney) — added 2026-08-10

**Source.** Complexity podcast ep. 94 (thermodynamics of communication) → Wolpert & Kinney,
*Noisy Deductive Reasoning* (arXiv 2012.08298, in the FQXi *Undecidability, Uncomputability,
and Unpredictability* volume, Springer 2021), expanded as *A Stochastic Model of Mathematics
and Science*, Foundations of Physics 54:21 (2024), arXiv 2209.00543. Their move: theoremhood
is governed by a probability distribution, because every physical reasoner is noisy and
noise-free logic is thermodynamically expensive.

**Three machine-checked things our framework says about that program:**

1. **Theoremhood is a Σ₁/semidecidable event** — an *open* in the observational topology —
   so the event logic of noisy mathematics is intuitionistic, not Boolean. The halting guard
   (`sharpReadout_not_computable`) is the computability-theoretic twin of their thermodynamic
   claim: a slack-free (classically additive) credence about a semidecidable event decides the
   halting problem. Where they say a physical reasoner *happens* to be noisy, we say a
   computable reasoner's credences about theoremhood *provably cannot* satisfy the complement
   rule. If their distribution assumes P(thm φ) + P(not-thm φ) = 1, the R3 hinge says they
   have silently assumed theoremhood is decided — false for r.e. theories. **Caveat: verify
   against the full text before making this charge in print; the abstract does not pin down
   their axioms.**

2. **Independence bookkeeping comes for free.** ⊢φ and ⊢¬φ are both semidecidable opens,
   disjoint by consistency, join ≠ ⊤ (incompleteness *is* failure of excluded middle in this
   frame). Disjoint additivity gives v(⊢φ) + v(⊢¬φ) + slack = 1 with slack = credence in
   independence / never-resolved. The binary framing conflates "not provable" with
   "refutable"; the valuation makes independence a first-class mass carrier. Clay-problem
   odds are three-way credences; multiple proofs = Bayesian confirmation of an open; evidence
   for ⊢¬φ lowers Pl(⊢φ) through the pseudo-complement.

3. **Their "objective distribution" speculation is our structural reading.** Slack = boundary
   mass, a fact about the space of proof-search outcomes, no believing subject — the
   epistemic-situation-not-agent principle. This example directly serves handoff §7.3
   (accommodating DS/non-additive objects in the unified picture).

**Optional Lean corollary** (if the example is used): a frame with two disjoint semidecidable
generators and the three-way decomposition above, ~20 lines from `additive_of_disjoint` +
the slack definition, natural home next to the Sierpiński model.

**FM paper:** one-sentence related-work mention added to sec-related (non-Boolean paragraph),
bib key `wolpert-kinney2024` (needs the DBLP verification pass like the rest).

**Adjacent literature for Paper 2:** Garrabrant et al., *Logical Induction* (credences on
sentences of arithmetic including undecidables) — natural comparison; our framework gives the
logic-level explanation of why such credences must be non-classical.

---

## 15. New points from the FM paper's later results (2026-10), ordered by interest

Results referred to are in the FM paper: Section 3 (metatheory), Section 10 (probability calculi from certain states), Section 11 (second-order linear types), Section 12 (quantum event logic), and `FiniteConstructive.lean`.

**1. Probability from points needs choice; probability from structure does not.**
The construction "probability = mixtures of certain states" is a points-first account: certain states are points (sharp valuations = points of the locale). Whether a logic's certain states reconstruct it (criterion (1)) is, for infinite frames, the prime ideal theorem, a choice principle. Without it a locale can have no points and the points-first account produces nothing, while valuations on the locale still exist. On finite lattices the points are found by search, with no choice (proved choice-free). So the points-first picture of probability is a classical (choice-dependent) commitment, and the structure-first picture (valuations on the frame) is the constructively available one. This is a precise sense in which the Humean structural realist ontology ("points derived, structure primary") is the constructively honest one. Strongest point; ties the formal results to the ontology.
- Prediction (conjecture, not proved): in a constructive metatheory the mixture calculus and the valuation calculus should come apart on infinite frames, not only on quantum logic.

**2. Quantum probability is probability without points.**
Quantum logic has states (Gleason) and no certain states (Kochen–Specker; proved for Cabello's 18-ray set). Every points-first account of probability fails exactly there. So point 1 is not an artifact of constructive mathematics: physics already supplies a logic whose probabilities are not ignorance over any point. Sharper than the QBism row of §8: quantum credences are not ignorance over anything, and no agent is needed to say so.

**3. Probability is extended semantics, not extended syntax (a second dial).**
For one logic (linear logic at a second-order type) two semantics disagree: mixtures of deterministic sequential programs, and the probabilistic coherence space, which is strictly larger. One tensor further they disagree about what is certain (a Girard clique is not a PCS element). So the logic dial does not determine the calculus; a second dial, what counts as a deterministic process, is needed. Refines the thesis of §0.

**4. Humeanism needs mixtures of mosaics.**
A Humean mosaic is a certain state; Humean chance on a logic must be a mixture of mosaics. Kochen–Specker blocks this for quantum observables (known; hence primitive-ontology Humeanism), and the PCS result exhibits a standard semantics with probabilities over no mosaic. Gives a criterion for which logics a Humean about chance can accept. Directly relevant to the user's own Humean commitment. (Framing is new; physics is known.)

**5. The axioms are the logic's linear shadow (generalized probabilism).**
The calculus's axioms are exactly the affine laws valid on certain states; monotonicity, normalization, modularity are what they are on frames. Generalizes the hinge of §4 from one axiom to all. Prior art to engage: de Finetti (classical), Paris 2001 (non-classical Dutch book), J. R. G. Williams, "Generalized probabilism" (J. Phil. Logic 2012) and accuracy papers. New: Cox framing, completeness as "axioms = affine laws", linear and quantum cases, mechanization.

**6. Slack is not ignorance, even given full information.**
On a finite frame a single point can leave a undecided (δ_p(a) + δ_p(¬a) = 0 when p is on the boundary). Slack is present inside a certain state, not only in uncertainty about which state obtains. Strengthens "belief without believer" (§6).

**7. Classical metatheory, intuitionistic object: coherent, and auditable.**
Studying intuitionistic event logics with classical tools is not self-undermining: the thesis concerns the event logic of semidecidable properties, not the logic of mathematicians (as for Kripke semantics). What matters is where the metatheory's classicality is essential: four places (prime ideal theorem, Hahn–Banach, compactness of probability measures, the sharp readout's definition), checkable with `#print axioms`. Methodological point: mechanization turns debates about classical commitments into audits.

**8. What a Rocq development would change.**
The kernels agree (neither assumes choice); the libraries differ. MathComp would give constructive, extractable proofs of all finite results. Values would become lower reals (approximable from below) instead of [0,∞]; Chaitin's Ω is exactly such a lower real, so the constructive value type matches semidecidability. The barycenter theorem needs compactness of Cantor space, i.e. the fan theorem, not provable in Rocq's logic without an axiom. The sharp classical readout cannot be defined; the uncomputability result becomes a synthetic statement (Forster–Kirst–Smolka), needing Church's thesis to state negatively. Philosophical upshot: in a constructive metatheory the claim "the sharp classical credence exists but cannot be computed" becomes "there is no sharp classical credence", which is closer to the paper's thesis that slack is forced.

**9. De Finetti survives the change of logic; Cox does not.**
Cox's functional-equation route to the sum rule fails intuitionistically (a disjunction's value is not a function of its disjuncts'), while the representational route (mixtures of certain states) still derives modularity. A comparative claim about which foundation of probability is robust under change of logic.

**10. Classical updating on undecidable hypotheses credits all undecided mass to refutation.**
The classical posterior of the complement exceeds the intuitionistic one by exactly μ(∂A ∩ B)/μ(B). Normative point for computational epistemology; contrast with logical-uncertainty frameworks that treat sentences classically (Garrabrant et al.). Modest, but has a theorem behind it.

**11. (Speculative) Link to the law-likeness fork.**
Chaitin's Ω and the universal semimeasure are mixtures over programs with total mass below 1, the same deficit as slack and as PCS subnormalization. If branch (b) of the law-likeness fork (simplicity-weighted ensemble) is taken, its measure is a mixture of certain states with structural slack. Flag as speculative.

**Honest assessment.** 1, 2, 3 are the most original. 4 is a new framing of known physics. 5 is largely known (Paris, Williams) and must be cited. 7–8 are methodological. 10 is modest. 11 is speculative.

---

## 16. Additions 2026-10-09: literature, the lattice of logics, uniqueness, ravens

### 16.1 Recent literature to engage (none cited in the old draft)

| Work | What it does | Relation to us |
|---|---|---|
| Colyvan 2004, "The philosophical significance of Cox's theorem", IJAR ([pdf](http://www.colyvan.com/papers/cox.pdf)) | Cox's theorem presupposes excluded middle; probability can't be the only coherent representation of uncertainty (fiction, constructive maths, vagueness) | Our hinge theorem is the exact form of his objection (complement rule for every valuation ⇔ EM) |
| Van Horn 2017, "From propositional logic to plausible reasoning" ([arXiv](https://arxiv.org/abs/1706.05261)) | Current careful statement of the Jaynes thesis (classical) | The view we relativize |
| Knuth & Skilling 2012, "Foundations of Inference" ([arXiv](https://arxiv.org/abs/1008.4831)) | Sum rule from disjoint additivity; scope claimed: distributive lattices | Our 5-element frame shows the derivation does not reach frames (paper, Section cox) |
| Goertzel 2017 ([arXiv](https://arxiv.org/abs/1703.04382)) | Knuth–Skilling symmetries applied to Heyting algebras | Same gap applies |
| Molinari 2023, RSL ([pdf](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/FBB20E26E4AD4A0C23EE87BED355379B/S1755020322000053a.pdf/towards-the-inevitability-of-non-classical-probability.pdf)) | Accuracy argument for non-classical probabilism, {0,1} truth values | Accuracy route to our calculus; compare |
| Gil Sanchez, Gyenis, Wroński 2022, Episteme 21(2) | Axiomatizes convex hulls of non-classical evaluations; doubts Dutch books outside classical logic | Our recipe = convex hull of certain states; our local-certainty result says *where* Dutch books stop gluing |
| Gyenis 2025 ([arXiv](https://arxiv.org/abs/2511.00228)) | Convex hulls of evaluations of any finite-matrix logic are effectively axiomatizable, not always finitely | Now cited and compared in paper, Section recipe |
| Bradley 2016, Erkenntnis | Non-classical probability and convex hulls | Cited |
| Klein, Majer, Rafiee Rad 2021, JPL ([arXiv](https://arxiv.org/abs/2003.07408)) | Probability for Belnap–Dunn logic, gaps and gluts | Their gaps ~ our slack. Our split of slack into two parts has no analogue there |
| Steele & Stefánsson 2021, *Beyond Uncertainty*; de Canson 2024 "On algebra relativisation" ([philsci](https://philsci-archive.pitt.edu/23905)) | Which algebra credences live on (awareness) | We relativize to the *logic* of the algebra, not only its atoms |
| Genin & Kelly 2017, "The topology of statistical verifiability" ([arXiv](https://arxiv.org/abs/1707.09378)) | Opens = verifiable hypotheses, closed = refutable | Our event logic is exactly theirs; we add the calculus |
| Pitowsky 1994 BJPS; Pitowsky 2006 ([arXiv](https://arxiv.org/abs/quant-ph/0510095)); Abramsky 2020 ([arXiv](https://arxiv.org/abs/2010.13326)) | Boole's "conditions of possible experience"; event structure dictates probability | Our third uniqueness criterion *is* Boole's conditions, relativized to the logic |
| "Coherence without complementarity" 2026 ([philarchive](https://philarchive.org/rec/BRUCWC-4)) | Dutch books for paraconsistent LP | Neighbour |

### 16.2 The lattice of logics (question 1)

**Facts.**
- Superintuitionistic logics form a lattice under inclusion, with IPC at the bottom. Classical logic is the unique maximal consistent one, because {⊥,⊤} is a subalgebra of every nontrivial Heyting algebra, so the Boolean algebras are the least nontrivial variety (no PIT needed).
- The orthomodular ("quantum") logics also have classical logic as their unique maximal consistent extension, since every nontrivial OML contains {0,1}.
- Linear logic sits in the substructural lattice. Adding weakening and contraction collapses ⊗ into ∧, giving intuitionistic or classical logic. Classical logic is one of continuum many maximal consistent substructural logics (Galatos 2004, "Minimal varieties of residuated lattices", Algebra Universalis 52; now cited in sec-lattice).

**Picture: there are two ways down from the top, and they fail dually.**

| Branch | What is dropped | What is kept | Probabilistic consequence |
|---|---|---|---|
| Intuitionistic (Heyting) | excluded middle | distributivity | Certain states (points) exist and reconstruct the order; the complement rule fails; **slack appears** |
| Quantum (orthomodular) | distributivity | excluded middle (a ∨ a′ = 1) | The complement rule holds (no slack); **certain states vanish** (Kochen–Specker); extension must be local; Gleason fixes the calculus on the full lattice |
| Linear (substructural) | contraction/weakening (idempotence of ⊗) | — | Probability over *formulas* collapses (a and a⊗a get the same value); probability must live on semantic states (webs); mixtures of certain states fall strictly inside the PCS from second order on |

**Formal backing:**
- Complement rule ⇔ EM: `hinge`.
- Sharp valuations reconstruct the order exactly on distributive lattices, with M₃ having none: sec-lattice.
- Kochen–Specker for Cabello's set: `no_ks`.
- Tensor collapse: `IsTensorValuation.collapse`.
- **NEW (proved today, `SlackLogics.lean`):** inside the intuitionistic branch, slack's two parts track the chain IPC ⊂ KC ⊂ CPC. deMorganGap ≡ 0 for all valuations ⇔ weak excluded middle (KC), and dnGap ≡ 0 for all valuations ⇔ Boolean (CPC). This is in a classical metatheory, and is now Theorem `thm:slack-logics` in the paper.

**Thesis.** Criterion (1), certain states reconstruct the logic, tracks distributivity. The complement rule tracks excluded middle. Criterion (2) holds at the top for every branch. Classical probability is the only point where all of them hold.

### 16.3 Uniqueness and "not conflating events" (question 2)

**PROVED (`Uniqueness.lean`, now paper Theorem `thm:unique`).** Criteria (1) and (2) alone do not fix the calculus: the PCS of `!Bool` and of T satisfy (1) and are strictly larger. Add a third criterion: *every affine law valid on all certain states holds on the whole calculus.* Then any convex set containing the certain states and satisfying criterion 3 equals Mix(S). The proof is two lines: convexity gives the lower bound, and completeness gives the upper bound.

**Reading of criterion 3.** "Uncertainty cannot violate what certainty guarantees." These are Boole's conditions of possible experience relative to the logic (Pitowsky), and they are equivalent to every extreme state being certain. This is the ignorance interpretation, noncontextuality in quantum terms. It is substantive:
- the PCS violates it (the pentagon point violates the law Σ ≤ 2);
- quantum states violate it on Cabello's set (9/2 > 4).

So: *the extension is unique exactly under the ignorance reading of probability, and the PCS and quantum mechanics are the two places where that reading fails.*

**"Not conflating events": three precise senses, all available.**
1. *Separation.* The calculus distinguishes every pair of events the logic distinguishes, iff the certain states separate them. That is criterion (1), and holds on distributive lattices in a classical metatheory.
2. *Negation is not complement.* **[cite: Pettis 1951, Horn–Tarski 1948; check positivity]** Valuations on a frame Ω correspond one-to-one to finitely additive probabilities on its Boolean envelope B(Ω).
   - So intuitionistic and classical credal states are *the same data*. Choosing the logic changes no number on verifiable events.
   - It changes which events count, and how negation is read: classical ¬ = complement aᶜ ("not verified") versus pseudo-complement ¬a ("refuted").
   - The conflation costs exactly the slack (= boundary mass), and changes the update rule (Dempster ≠ Bayes on undecided evidence).
   - This is the cleanest statement of "discriminating relevant events": **the logic doesn't change your credences, it changes which of them are credences in events.**
3. *a vs a⊗a.* Lattice valuations on linear logic conflate them (tensor collapse); the certain-state calculus on webs does not.

**Status 2026-10-09 (later): now in the paper, sec-recipe §"Uniqueness".**
- Criterion (3) is in the intro and abstract, with four readings: coherence (Dutch book, Paris), accuracy (Williams, Brier), ignorance (extreme points are certain; Minkowski, not formalized), and no new behaviours (every known failure is a PCS or quantum state).
- Independence: each of S ⊆ C, mixture closure and (3) is needed (counterexamples: proper convex subsets, S itself, !Bool). Criterion (2) is then a *consequence*, so it serves as a calibration check, not an axiom.
- Infinite events: `calculus_unique_closed` (Lean) needs closure in the product topology, justified as "a state is checked finitely many events at a time".
- Corollary `cor:frame-unique` (not formalized, classical metatheory): on *every* frame the valuations are the closure of Mix of the sharp valuations. So the first fix is the unique calculus of the criteria too.
- **Non-conflation is not a fourth criterion.** It is (1) and (3) read together. (1) gives "no more laws": a set containing every certain state satisfies no law that some certain state violates. (3) gives "no fewer laws". So the calculus obeys exactly the laws of the certain states (`calculus_laws_iff`). On a frame this gives two sharp forms: distinct events are separated (`exists_sharp_ne_of_ne`), and the complement rule holds at a only where a ⊔ ¬a = ⊤ (`em_of_sharp_compl`, pointwise).
- Pettis now settles positivity: a monotone modular function extends to a nonnegative finitely additive measure on the generated Boolean algebra (decompose into differences b∖a with a ≤ b). So the "same data" point is in the paper, citing pettis1951.

### 16.4 The indoor ornithologist (question 3)

**Correction made today.** The old paper claimed that intuitionistic contraposition dissolves the paradox. It does only for *non-regular* predicates (¬¬black ≠ black). If both colours are observable, black is regular, contraposition is an equivalence intuitionistically too, and the paradox returns. The paper sentence is now fixed (sec-valuation).

**What the verification logic does say (stronger diagnosis).**
- **(a) Universal laws are not events.** Over an unbounded domain, "all ravens are black", H, is *closed* (refutable), not open (verifiable).
  - Its refutation C = "some non-black raven is observed" is open.
  - Every finite observation leaves room for a counterexample, so C is dense and ¬C = int(Cᶜ) = ∅.
  - Hence **intuitionistic credence in the law is 0 under every valuation, and no finite evidence confirms it** (Popper, Kelly).
- **(b) The classical confidence in the law is all boundary.** The classical credence is μ(H) = μ(Cᶜ) = slack(C) = μ(∂C). By the overconfidence theorem, the classical posterior of H given any evidence e equals μ(∂C ∩ e)/μ(e), and all of it is "not yet refuted" mass.
  - So black ravens and white socks both "confirm" H classically, for the same reason: they don't refute it.
  - **The paradox is the classical calculus treating boundary mass as if it were a decided event.**
  - Backing: Lean `thm:slack-frontier`, `classical_posterior_compl_eq`, and now `Ravens.interior_compl_cex` (density, for any infinite set of objects and any space of kinds).
- **(c) Correction: confirm only events of the logic.** The law enters only through its refutation event C. Evidence e is relevant through v(C | e) versus v(C).
  - A white sock at object j removes j as a candidate counterexample, and so does a black raven.
  - The size of the effect is the prior probability that *that object* was a counterexample. A sampled raven is a far likelier candidate than a sampled non-black thing.
  - This recovers the Hosiasson/Good/Fitelson–Hawthorne asymmetry, *derived from the logic's own events* and without ever treating H as an event.
  - **Now a theorem** (`Ravens.lean`, paper `thm:ravens` in sec-bridges §Universal Laws). Independence is an explicit hypothesis.
- **(d) Optional refinement: report two numbers for a law.** Verification credence v(int H) is 0 for laws. Non-refutation credence is μ(cl H) = 1 − v(C).
  - Confirmation moves the first, corroboration (Popper) moves the second, and their difference is the slack.
  - Indoor ornithology changes only corroboration, and only by eliminating one candidate.

**Prior work to check before claiming novelty:**
- Bayesian ravens: Fitelson & Hawthorne 2010, "How Bayesian confirmation theory handles the paradox of the ravens".
- Kelly, *The Logic of Reliable Inquiry* (1996), on falsifiable laws.
- Popper on corroboration.
- Whether anyone has treated the ravens via verification topology or a Bel/Pl gap.

### 16.5 Novel points, consolidated (with 2026-10-09 results)

1. **Extending the wrong logic has a measurable cost:** slack = boundary mass; the classical posterior overstates refutation by μ(∂A∩B)/μ(B); Dempster ≠ Bayes exactly on undecided evidence. [16.3(2) sharpens this: same data, different events.]
2. **The update rule is decided by the logic** (Dempster = Bayes ⇔ zero slack at the evidence).
3. **Colyvan's objection made exact:** R3 ⇔ EM (hinge), and the Knuth–Skilling route fails on frames (5-element counterexample). Product rule is logic-free; the sum rule carries the logic.
4. **Uniqueness under the ignorance reading** (16.3, proved).
5. **Two ways down from classical logic fail dually:** intuitionistic gives slack; quantum loses certain states; linear loses formula-probability (16.2). The slack parts track IPC ⊂ KC ⊂ CPC (proved).
6. **Contextuality without physics:** in linear logic, coherence on each test does not imply a mixture of worlds (pentagon), and the PCS sits between the global and local calculi.
7. **Ravens:** the paradox is boundary mass treated as an event; confirm through refutation events (16.4).

### 16.6 The ravens in plain language (formalized 2026-10-09, `Ravens.lean`)

**The setup.**
- A world is a complete list saying, for each object in the universe, what kind of thing it is.
- You can only ever inspect finitely many objects. A *verifiable* claim is one that some finite inspection can establish.
- "Some raven is non-black" is verifiable: find one.
- "All ravens are black" is never verifiable. However many objects you have checked, an unchecked one might be a white raven. You can only fail to refute it.

**What follows.**
1. In the logic of verifiable claims, the law has no verifiable part. Its credence is 0, before and after any evidence (`compl_cexOpens`, `condVal_compl_cex`).
2. What a classical Bayesian calls "credence in the law" is credence in "not yet refuted". This is exactly the slack at the counterexample event, the mass of worlds the evidence has neither refuted nor verified (`classical_law_eq_slack`, `classical_posterior_law`).
3. So classically "confirming the law" just means lowering the probability that a counterexample exists.

**The paradox.** Classically, a white sock is an instance of "all non-black things are non-ravens", hence of the law, and so it confirms the law.
- In our terms, learning that object j is a white sock rules out j as a counterexample. Learning that j is a black raven does exactly the same. Under independence, both give the same posterior for "some counterexample exists".
- What differs is how much you expected j to be the counterexample before the final check (`posterior_cex_select`).
  - Picked j because it is a raven? There was a real chance it was a white raven. Seeing it black lowers the counterexample probability noticeably.
  - Picked j because it is non-black? The chance it was a raven was tiny. Seeing it is a sock lowers the counterexample probability by a tiny amount.
- So the sock does bear on the law. It does so negligibly, and only by ruling out one candidate counterexample.

**What is and isn't new.**
- The numbers are the classical Bayesian resolution (Hosiasson-Lindenbaum 1940, surveyed by Fitelson–Hawthorne 2010). Both are now cited.
- What the logic adds:
  - (a) The resolution never needs to treat the law as an event.
  - (b) The classical "confirmation of the law" is identified with the shrinking of slack: unrefuted mass that no evidence ever turns into verification.
  - (c) Observational evidence ("object j is a raven") is clopen. So its slack is 0, and Bayes and Dempster agree on it. The paradox does not depend on the update rule.
- Popper/Kelly already have "universal laws are refutable, not verifiable". A search found no treatment of the ravens through a verification topology or a belief/plausibility gap. That search was not exhaustive.

**Does conditioning follow from the criteria?** No.
- Criteria (1)–(3) constrain which credal states exist, not how they update.
- In the certain-state picture there is a natural reading of each rule (sec-ds, finite frames, not formalized). After evidence b:
  - Bayes/geometric conditioning averages over the certain states that **verify** b.
  - Dempster averages over those that **do not refute** b.
- They agree iff no weight sits on states that leave b undecided, which is the slack(b) = 0 condition of `thm:cond-hinge`.
- Choosing an update rule therefore means choosing which certain states remain possible after the evidence. That is an extra decision, not a consequence of the calculus.

### 16.7 Novelty verdict: the lattice of logics and the three criteria (2026-10-09)

**Lattice of logics: a synthesis of known facts plus two small new theorems.**
- Known facts:
  - Classical logic is the unique maximal consistent intermediate logic, and the unique maximal consistent extension of OML logic. The reason is that {⊥,⊤} is a subalgebra of every nontrivial Heyting algebra and OML, and no PIT is needed.
  - Among substructural logics, classical logic is one of continuum many maximal consistent logics (Galatos 2004, now cited).
- The dual-failure table (intuitionistic: slack; quantum: certain states vanish; linear: tensor collapse) is our organization of known and own results.
- The two small new theorems:
  - `thm:slack-logics`: the slack parts detect IPC ⊂ KC ⊂ CPC.
  - Tensor collapse.
- Now in the paper: sec-lattice §"The lattice of logics".

**Three criteria plus uniqueness: the mathematics is known, the use as criteria is ours.**
- Known: Mix = laws is de Finetti/Paris (Paris 2001 Thm 2, Cor 4), and the barycenter form is Choquet-style. Criterion (3) is Boole/Pitowsky's "conditions of possible experience".
- Gyenis axiomatizes convex hulls of truth-value assignments, but he does not use them as criteria for a calculus.
- New, at a modest level:
  - the three-criteria framing with an independence analysis;
  - the observation that (2) follows from the others;
  - the identification of (3)'s failures with PCS extra behaviours and quantum contextuality;
  - the "no more laws / no fewer laws" reading of non-conflation;
  - the corollary that frame valuations are the unique such calculus;
  - the mechanization.
- Present this as a clean statement with counterexamples, not as a headline theorem.

### 16.8 Arguing "necessary and sufficient", and categorical ties

**What can be proved, and what must be argued.**
- *Sufficiency* means categoricity: the criteria determine the calculus. This is proved (`calculus_unique`, `calculus_unique_closed`).
  - It has the shape of an **interval collapse**. The sets that contain the certain states and are closed under mixtures form an up-set with least element Mix(S). The sets that obey the certain states' laws form a down-set with greatest element the law-solution set. Completeness (de Finetti/Paris) says the two extremes coincide.
- *Minimality* means each condition is needed. This is also proved, by counterexamples: proper convex subsets, S itself, !Bool.
- *Necessity* means every adequate extension must satisfy the criteria. This is not a theorem. Argue it per criterion from one independent commitment each:
  - (1) "probability extends logic";
  - (3) coherence (Dutch book), or accuracy, or the ignorance reading;
  - mixture closure: ignorance about which of two admissible states holds.
- The strongest form of the argument is **classificatory**. Rejecting a criterion gives a known, different calculus: drop (3) and you get PCS (extra behaviours) or quantum states (contextuality). So the criteria sort the alternatives rather than excluding them by fiat. This is the von Neumann–Morgenstern/Cox template: axioms, then a unique representation, then a list of what each axiom rules out.

**Categorical concepts to tie it to, ranked by fit.**
1. **Free algebra of the distribution monad (best for paper A).**
   - Convex sets are the Eilenberg–Moore algebras of the finite distribution monad D (Świrszcz 1974; Fritz, "Convex spaces I", 2009; Jacobs 2010/2011).
   - Mix(S) is the image of the free algebra D(S) under the unique affine map extending S ↪ [0,1]^E. The certain states are the monad's unit (Dirac).
   - So the calculus is the least D-subalgebra containing the unit's image, and uniqueness says it is also the largest set satisfying the unit's laws.
   - For frames, the infinite analogue is the valuation monad: Jones–Plotkin; Vickers' valuation locale; Keimel–Plotkin 2017, where valuations form the free Kegelspitze. Dirac valuations are the certain states.
2. **Orthogonality/bipolar closure (best for paper B).**
   - States and laws form a Galois connection, and Mix(S) is the bipolar of S for affine tests.
   - The PCS is the bipolar for nonnegative tests under ⟨x,y⟩ ≤ 1 (Girard), an instance of Hyland–Schalk orthogonality categories (TCS 294, 2003).
   - recipe(A), P(A) and loc(A) = orth(sharp(A^⊥)) are then three orthogonality closures, and the sandwich recipe ⊆ P ⊆ loc compares them. Criterion (3) becomes "closed under the logic's own orthogonality, generated by certain states".
3. **Extension of scalars / free effect modules (fits quantum, and contrasts with intuitionistic).**
   - Jacobs–Mandemaker ("The expectation monad in quantum foundations", arXiv:1112.3805) obtain probability from a logic by tensoring an effect algebra with [0,1]. Gleason's theorem becomes "effects on Hilbert space are the free effect module on projections".
   - Effect algebras build in the orthosupplement a ⊕ a^⊥ = 1, that is, the complement rule. By our hinge, this framework cannot cover intuitionistic logic without modification.
   - Our construction is what remains of "tensoring with [0,1]" once the complement rule is dropped. This is a good related-work point.
4. **Codensity monads / Kan extensions (most literally "extension").**
   - The ultrafilter monad, whose points are the certain states on P(X), is the codensity monad of FinSet ↪ Set (Leinster 2013).
   - Probability monads, including the finitely additive one, are codensity monads of functors sending finite or countable sets to distributions on them (Avery 2016; Van Belle 2022, TAC 38). In Van Belle's words, probability measures arise "canonically as the extension of probability distributions on countable sets".
   - Our infinite uniqueness theorem has this flavour: the calculus on arbitrary events is the limit of the finite-window calculi (`laws_iff_local_Mix` plus closure). Making this a real Kan-extension statement would be new work. It is a candidate for future work, not a claim.

**Recommendation.**
- Paper A: state the criteria as an axiomatization with interval collapse and independence. Mention the distribution-monad reading in one paragraph, and contrast with effect-algebra scalar extension (point 3) in related work.
- Paper B: use the orthogonality framing (point 2) as the organizing idea.
- Keep codensity (point 4) as future work.

### 16.9 Ravens: what differs between classical and intuitionistic (2026-10-09, answering the user)

- **Does a white sock lower the probability of a counterexample?** Not in all cases. It depends on the prior, not on finiteness.
  - Under independence of object j from the rest (the hypothesis of `posterior_cex_select`), a non-counterexample observation never raises P(C). It lowers it by P(j bad | selection)·P(no other counterexample). This holds with finitely or infinitely many objects.
  - Without independence the sign can flip. Good 1967 ("The white shoe is a red herring", BJPS 17:322) gives a prior under which a black raven *lowers* P(H).
  - With infinitely many independent objects, each a counterexample with probability ≥ ε, Borel–Cantelli gives P(C) = 1. Then P(H) = 0 and nothing moves (Carnap's zero-probability-of-laws problem).
- **Classical vs intuitionistic.** The user's reading is correct, but only for infinitely many objects.
  - Classically, the drop in P(C) is an equal rise in P(H) = 1 − P(C).
  - Intuitionistically, v(¬C) = 0 before and after any evidence, so the drop goes into slack(C) (unrefuted and unverified), not into the law.
  - With finitely many objects and discrete kinds, every set of worlds is open, ¬C = H, and the two calculi coincide.
- All of this is now in the paper (sec-bridges, §Universal Laws).

### 16.10 Categorical readings (new paper section `sec:categorical`, appended to sec-quantum.tex)

There are four readings. The mathematics of each is standard. What is ours is the application to the calculi plus the mechanization (`Categorical.lean`).

1. **Free convex algebra.** Mix(S) is the image of D(S), and the certain states are the monad unit (Świrszcz, Fritz, Jacobs; Abramsky–Brandenburger global sections; Pitowsky correlation polytopes).
   - Simplex = unique decomposition. Finite frames are simplices (Möbius; `mix_deltaPoint_inj`). Bool⊸Bool is not (gbit; `lin_not_simplex`).
   - Representing measures are unique on the σ-algebra of the events for presentations with meets, which includes all frames (`trim_eq_of_meet`, `frame_rep_unique`).
   - **GPT reading (not found in the literature):** intuitionistic probability has a classical (simplex) state space with a restricted effect set (opens, closed under ∧ and ∨ but not under complement). That makes it not a Janotta–Lal restricted GPT, but a restricted theory in Plávala's sense.
   - Caveat (Heunen–Landsman–Spitters): quantum states are valuations on a pointless locale in the Bohr topos. So "intuitionistic is simplicial, quantum is not" needs a classical metatheory, that is, enough certain states.
2. **Orthogonality.** orth(recipe A) = loc(A^⊥) and orth(loc A) = recipe(A^⊥).
   - (recipe A, recipe A^⊥) is tight iff recipe A = loc A iff there is no gap at A and at A^⊥. It is not tight at the core (`tight_iff`, `not_tight_core`).
   - This is Fulkerson/Lovász antiblocking duality (Knuth §30). For clique families, tightness means the graph is perfect.
   - The new part is the MALL reading: the certain-state calculus is not a model of linear negation, and P is the self-dual set between the two. P is not the theta body.
3. **Effect algebras.**
   - Orthosupplements exist only in Boolean frames (`em_of_complemented`; Foulis 2000 in substance).
   - Partial-sum states contain the valuations, strictly on Darst's lattice (`partialSum_not_modular`), so they can violate criterion (3).
   - Bosbach/Riečan states keep the complement rule, so they fail criterion (1) on non-Boolean frames.
   - The scalar extension that works is the valuation monoid (Tarski, Horn–Tarski).
4. **Limits.** The closed calculus is the limit of the finite-window calculi (`closedCalcEquivLimit`, in Type). For distributive lattices, Val = Ran of D∘pt along finite lattices. This is folklore (Gehrke–Jakl–Reggio, Van Belle Rem 4.3) and not formalized.
   - Codensity theorems (Leinster for ultrafilters, Avery/Van Belle for finitely additive Giry) are the certain-state and calculus instances at the powerset frame.

**Corrections made from the first literature pass:**
- The Low(V) counterexample is Darst 1970. It is now cited in sec-cox and in the intro's Cox bullet, which is now narrowed.
- The valuation monoid and its normal form for distributive lattices are Tarski 1938, Horn–Tarski 1948 and Coquand–Spitters. They are now cited in sec-lattice.
- The quantum `h` state is *not* shown non-quantum. It is only not a mixture of Born states of the fixed rays. AFLS say they do not know whether Q(H_KS) = G(H_KS). sec-quantum is fixed accordingly.
- Gaines 1978 is now cited for the easy direction of the hinge.

**Second literature pass on 13.2 (orthogonality), 2026-10-09.** The linear-logic reading is partly anticipated.
- Ehrhard's MPRI 2-02 exercise sheet TD 2 (2021, Ex. 1.1–1.10, verified):
  - p(E) = {x ≥ 0 | weight ≤ 1 on every clique of E^⊥} is a PCS and a functor Coh → Pcoh, commuting with & and ⊕;
  - p(E^⊥) = p(E)^⊥ for E generated from 1 by ⊥ and & (cographs);
  - it fails whenever C5 embeds, and for odd C_k.
- Borodulin-Nadzieja–Farkas–Pelczar-Barwacz (arXiv:2605.14072, Thm 4.6): geometric duality of F and F^⊥ holds iff they are the cliques and anticliques of a perfect graph.
- Both are now cited in 13.2 and sec-second-order.
- Still not found:
  - the tight-pair formulation for the certain-state calculus (whose certain states can be fewer than the cliques, as in Shannon);
  - the equivalence with "no gap at A and at A^⊥";
  - non-tightness at the core.
- A lead, not checked: on T⊗T the local calculus may be local orthogonality, which is no-signalling for two parties (Fritz et al. 2013). That would make the primal gap Bell's theorem.

**Lead finished, and contributions audit (2026-10-09, end).**
- **Bell at the core (Lean `Bell.lean`, paper Thm `thm:cat-bell`).**
  - The {0,1}-elements of P(T) are sets of pairwise exclusive events, i.e. local orthogonality.
  - The PR box is in loc(core) and not in P(core), by the CHSH bound 3 < 4.
  - So P(core) ⊊ loc(core).
  - On normalized boxes: P = the local polytope, and loc = no-signalling (Fritz et al. 2013, LO = NS for two parties; not formalized). loc is also Kissinger–Uijlen's causal tensor.
  - By P_eq_loc_iff, the pentagon gap at T and Bell's theorem at the core are equivalent.
- **The hinge's converse is Nachbin 1947 in substance** (prime filters all maximal ⇒ Boolean). It is now cited in sec-hinge and sec-related, and removed from the contributions list.
