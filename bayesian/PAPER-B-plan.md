# Paper B plan: linear logic and contextuality

Status: skeleton paper in `bayesian/paperB/` (LNCS, anonymous). Section 2 is written, and the other sections hold only this plan (2026-10-09). Source material is in the current `bayesian/paper/` files. Each section below names the file and section it comes from.

## Working title

*Mixtures of Deterministic Programs in Probabilistic Coherence Spaces*

Venue fit: FoSSaCS 2027 (deadline 2026-10-15, see "Venue" below), LICS or FSCD (logic), or QPL (if the Bell/contextuality angle leads).

## Abstract (draft)

Probabilistic coherence spaces are the standard denotational model of higher-order probabilistic programs. We ask which of their elements are mixtures of deterministic ones. For each type we take the mixtures of its certain states, the elements with values in {0,1}, as its probability calculus.

At every formula of multiplicative–additive linear logic over finite data types, the certain states are cliques of Girard's coherence space and the calculus lies inside the probabilistic coherence space. The two agree at first order and differ from second order on. For a program with two functional arguments, the calculus is the stable set polytope of a graph whose clique-constrained polytope is the coherence space, and five web points separate them, with the bounds of the KCBS inequality.

For the dual of a tensor of two additive types, the two coincide iff one of the two coherence graphs has no induced four-cycle. The gap transfers to every formula in which such a tensor occurs negatively.

Linear negation exchanges the calculus with a local calculus cut out by the certain states of the dual, and the coherence space is the self-dual set between them. The calculus is not compositional: first-order types are tight, but their tensor is not. At the dual of the second-order type, the gap is Bell's theorem, witnessed by the Popescu–Rohrlich box.

All results are mechanized in Lean 4.

## Introduction: paragraph topics

1. Mixtures of determinism
2. Coherence spaces model
3. Definability question
4. Certain-state calculus
5. First order agrees
6. Second-order gap
7. Exact condition
8. Transfer
9. Duality, Bell
10. Quantum contrast
11. Mechanization
12. Contributions

## Contributions (one sentence each, new work only)

1. **Cliques.** At every multiplicative–additive formula, the certain elements of the coherence space are cliques of the coherence space and incoherent pairs carry total weight at most 1, so Girard's intuition holds throughout. The converse fails at (T⊗T)^⊥ through Shannon's set.
2. **Second order.** At T the calculus is STAB and the coherence space is QSTAB of one exclusivity graph. An explicit pentagon point lies outside the calculus, and with three arguments there is a gap among always-halting programs.
3. **Exact condition.** For formulas built from data types with & and ⊕, the calculus and the coherence space of (X⊗Y)^⊥ coincide iff one coherence graph has no induced 4-cycle. The mechanized proof avoids perfect graph theory and extends Ravindra's theorem.
4. **Transfer.** Coordinate retracts carry the gap to every formula with a negative occurrence of a tensor whose factors both have induced 4-cycles. Beyond second order, a gap also exists without such a tensor.
5. **Duality and Bell.** Linear negation exchanges the calculus and the local calculus, and the two are tight iff neither the formula nor its dual has a gap. Tightness holds at every n⊸m and fails at the tensor of two of them, so the certain-state calculus is not compositional. At the core the gap is Bell's theorem, equivalent to the pentagon gap at T.
6. **Mechanization.** All of the above is in Lean 4 over mathlib, with no `sorry` and standard axioms. The results take about 9,200 lines in 29 files. The general theorems hold for arbitrary finite data types, and the finite facts behind the witnesses are checked by evaluation (`decide`) on explicit finite types (Appendix A).

## Sections and subsections

1. **Introduction**
2. **Calculi from Certain States** (from sec-recipe §10.1–10.2 and §10.4)
   - 2.1 Presentations and mixtures
   - 2.2 Affine laws and completeness (credit de Finetti, Paris)
   - 2.3 Laws of deterministic programs: the calculus is the unique convex set containing the certain states and obeying exactly their affine laws (uniqueness, credit de Finetti/Paris). A gap is a coherence-space element that violates a law obeyed by every deterministic program, as the pentagon and CHSH inequalities are. No justification of the criteria here (that is paper A).
   - 2.4 Why not lattice valuations (tensor collapse, from sec-lattice)
3. **Linear Logic Background** (from sec-recipe §10.3 and §10.5)
   - 3.1 Coherence spaces, data types, first order
   - 3.2 MALL formulas and their semantics
   - 3.3 Coherence at every formula
   - 3.4 The exponential !Bool (credit Danos–Ehrhard)
4. **Second Order** (from sec-second-order §11.1)
   - 4.1 Sequential programs and Kuhn
   - 4.2 A language for T
   - 4.3 The pentagon gap
   - 4.4 Divergence and total programs (Baumeler–Wolf, T₃)
5. **The Exact Condition** (from §11.4)
   - 5.1 STAB and QSTAB
   - 5.2 Clique property and perfection
   - 5.3 Four-cycles: a direct proof
   - 5.4 Beyond second order
6. **Other Formulas** (from §11.2)
   - 6.1 Coordinate retracts
   - 6.2 Negative occurrences and four-cycles
7. **Local Certainty and Duality** (from §12.2, §11.3, §13.2)
   - 7.1 The local calculus
   - 7.2 A clique outside the coherence space (Shannon)
   - 7.3 Negation, tightness, and the tensor (Cor `cor:cat-tensor`)
   - 7.4 Bell's theorem at the core
8. **Quantum Event Logic** (from §12)
   - 8.1 Kochen–Specker for Cabello's set
   - 8.2 Divergence and the stable-set bound
   - 8.3 Local certainty and Born states
9. **Related Work**
    - Probabilistic coherence spaces and full abstraction (Ehrhard–Pagani–Tasson, Castellan et al.)
    - Generalized probabilism (Paris, Williams, Gyenis)
    - Contextuality (Cabello–Severini–Winter, Acín–Fritz–Leverrier–Sainz, Abramsky–Brandenburger)
    - Causal processes (Baumeler–Wolf, Kissinger–Uijlen, Simmons–Kissinger)
    - Antiblocking duality and perfect graphs (Fulkerson, Knuth, Ravindra); Ehrhard TD 2; Borodulin-Nadzieja–Farkas–Pelczar-Barwacz

10. **Conclusion**

Mechanization has no section of its own. It is a short paragraph in the intro and the elaboration of contribution 6. The file map, finite checks, axioms and size are in Appendix A (Lean definitions and theorems).

## Conclusion plan

- Calculus vs coherence space: they are equal at first order and differ from second order on. The difference is exactly the non-sequential behaviours.
- At second order the gap is governed by induced 4-cycles, and it transfers along negative occurrences.
- Negation swaps the global and local calculi, and the coherence space is self-dual between them. The gap at T and the Bell gap at the core are two sides of one gap.
- The certain-state calculus is not compositional (tight factors, non-tight tensor). The coherence space is compositional by construction, which is what it pays for with extra behaviours.
- Consequence: reasoning in the coherence space certifies weaker guarantees than sequential programs satisfy.
- Open questions:
  - an exact condition beyond second order;
  - a theta-body (quantum) calculus for programs;
  - exponentials beyond !Bool;
  - a characterization of the tight formulas;
  - whether h is quantum (Acín–Fritz–Leverrier–Sainz);
  - a comparison with Kissinger–Uijlen's causal processes.

## Decisions

- **Tensor lemma: done.** In Lean: `Categorical.lean`, `P_lolli_eq_loc`, `tight_lolli`, `not_tight_core'`, `tight_not_tensor_closed`. In the current paper: Cor `cor:cat-tensor` in §13.2.
- **Section 2 is self-contained.** It gives short versions of the construction, completeness, uniqueness, and the tensor collapse. It cites paper A for the criteria and their justification.
- **The three criteria in paper B.** Only criterion (3) does work here, read as "every behaviour is uncertainty about a deterministic program". A gap is exactly a failure of (3) by the coherence space. Criterion (1) appears as "certain states are cliques" (contribution 1). Criterion (2) is trivial at data types and is not discussed.

## Venue: FoSSaCS 2027 (ETAPS, Copenhagen, 10–15 April 2027)

- Deadline **Thursday 2026-10-15** (firm). 18 pp, LNCS (`llncs.cls`), double-blind. Rebuttal 7–9 Dec, notification 2026-12-22, voluntary artifact evaluation from 2027-01-11. Source: etaps.org/2027/cfp.
- The appendix policy is not stated in the joint CfP. Check the FoSSaCS page before relying on one.
- **No dual-submission conflict with CPP.** CPP notification is 2026-11-10, after this deadline. All paper-B material (sec-recipe, sec-second-order, sec-quantum, §13.2, sec-lattice tensor collapse) was committed after the 2026-09-10 CPP submission.
- **Scope fit.** FoSSaCS covers semantics, logics, and probabilistic and quantum computation, and coherence-space papers have appeared there (e.g. the free exponential of probabilistic coherence spaces, 2017).
- **Cut to 18 pp (target page budget):**

  | Section | Pages |
  |---|---|
  | Intro | 1.5 |
  | §2 | 1.5 |
  | §3 | 2 |
  | §4 | 3 |
  | §5 | 3 |
  | §6 | 1.5 |
  | §7 | 3 |
  | §8 (quantum) | 0.5, as a remark |
  | §9 (related work) | 1 |
  | §10 (conclusion) | 0.5 |

  If space is short, drop the !Bool subsection (3.4) and the language subsection (4.2) first.
- Anonymized Lean supplement: same recipe as CPP (Lean and build files only, archive upload).
