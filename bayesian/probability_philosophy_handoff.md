# Philosophy of Probability & Structural Realism — Conversation Summary

*Handoff document for continuation in a new conversation.*

---

## 1. Core Positions Established

### 1.1 Interpretations of Probability (Standard Survey)

The main philosophical interpretations of probability discussed:

- **Frequentism** (von Mises, Fisher, Neyman): probability as limiting relative frequency in a reference class. Core problem: the reference class problem — no neutral way to pick the "right" class.
- **Propensity** (Popper): probability as objective physical tendency of a setup. Problem: risks circularity.
- **Logical/Epistemic probability** (Carnap): probability as a logical relation between propositions, a generalisation of deductive confirmation. Programme largely stalled — no unique language-independent confirmation function.
- **Subjective Bayesianism** (de Finetti, Ramsey, Savage): probability as degree of belief, constrained only by coherence. Too permissive about priors.
- **Objective Bayesianism** (Jaynes, Williamson): adds constraints (maximum entropy, symmetry) to priors. Closer to the view developed here.
- **Best Systems Analysis / Humean chance** (David Lewis): objective chances are whatever probabilities appear in the Best System — the theory best balancing simplicity, strength, and fit with the totality of actual facts.

### 1.2 The "Bayesian Functionalist" Attitude

The attitude *"probability is the thing that is updated by Bayesian inference"* was identified as:

- Closest to **subjective/functionalist Bayesianism** with a deflationary, pragmatist flavour
- Defines probability by its **functional role** (what it does) rather than its metaphysical nature (what it is)
- Distinguished from Movellan & Nelson's **probabilistic functionalism** (2001, *Behavioral and Brain Sciences*), which goes further: probabilities are tools used by *scientists* to understand adaptive behaviour, and do not need to be represented or computed by the organism itself. This is instrumentalism about probabilistic models, not a claim about probability's nature.

### 1.3 Feyerabend's *Against Method* and Probability

- Feyerabend's challenge: no single method is valid in all circumstances — "anything goes."
- **Bayesianism as partial reconciliation**: provides a meta-methodology for comparing methods via posterior probabilities; pluralistic by design, no method privileged a priori. Operationalises fallibilism.
- **Limits of reconciliation**: choice of priors is itself a methodological commitment; Bayesianism is one tradition that can itself be questioned. Feyerabend's deeper political/sociological critique is not dissolved by probabilism.

---

## 2. The User's Metaphysical Framework

### 2.1 Ontic Structural Realism (OSR)

The user holds a position closely related to OSR (Ladyman, Ross) with original features:

- The most elementary thing in the world is **structure** in the logical/mathematical sense
- Things at their core are compositions of structures expressed as relations between elementary components
- If elementary particles have properties beyond their mathematical structure, those properties should themselves be expressible as mathematical relations — otherwise they are metaphysically idle
- The world is the **minimal physical implementation** of some structure (distinct from Tegmark's Mathematical Universe Hypothesis, which eliminates the implementation entirely)

### 2.2 Instances vs. Non-Instances

- **Non-instances** (general cases: "a table", "2", "a triangle") are descriptions of structure
- **Instances** (this table, these 2 sticks) are real-world items observed to match the structure
- Higher-level structures are formed from lower-level ones; we can observe them but can only *prove* their correctness from first principles
- Without complete first-principle knowledge of the universe's dynamical rules, we cannot prove that 1 stick + 1 stick = 2 sticks, or that gravity will hold tomorrow — **Humean constraint**

### 2.3 Probability as Mathematical Structure

Proposed addition to the framework:

- Probability is a mathematical structure (like the derivative or integral) for which we have no proof that the world follows it, but which appears observationally to be instantiated
- What sets it apart from other mathematical structures: it is **constitutively designed for incomplete information**, and it requires a **prior** — a structural input not read off from the world but brought to it by the epistemic situation
- Probability is uniquely honest about the gap between abstract structure and instance: it makes that gap a *parameter* (the prior) rather than a hidden assumption

---

## 3. The Limit Proposal

### 3.1 Core Idea

> Classical logic/mathematics is the limiting case of probabilistic reasoning as available information approaches completeness. Probability is the general framework for reasoning under incomplete information; deductive inference is what it collapses to at the limit.

### 3.2 Formal Support

- **Cox's Theorem** (Cox 1946): any system of plausible reasoning that reduces to classical logic when propositions are certain, and satisfies minimal consistency requirements, must use the probability calculus. Probability is the unique consistent extension of logic to degrees of belief.
- **Boolean algebra as special case**: the {0,1}-valued restriction of a probability measure just *is* classical propositional logic.
- **Paris & Vencovská**: if a logic of partial belief (a) reduces to classical logic at the extremes, (b) is continuous, and (c) satisfies symmetry/consistency conditions, it must be the probability calculus. This is the closest thing to a "reverse Cox" theorem.

### 3.3 The Quantum Extension — An Iterated Limit

Quantum probability requires a non-commutative generalisation of classical probability. This suggests a hierarchy:

```
Classical logic
    ↑  limit as uncertainty → 0
Classical probability
    ↑  limit as ℏ → 0 (commutative limit)
Quantum probability (non-commutative)
```

- **Epistemic gaps** (hidden variables): the limit is in principle reachable with complete information
- **Ontological gaps** (Copenhagen, GRW): the limit is unreachable in principle — probability remains irreducibly non-degenerate
- The framework accommodates both; QM doesn't break the picture but adds a layer to it

### 3.4 Tension: The Prior at the Limit

- Bernstein-von Mises theorem: under regularity conditions, posteriors converge to a Gaussian centred on the true parameter regardless of prior — prior washes out asymptotically
- But convergence is *empirical*, not deductive — you never reach 100% by deduction alone, only by accumulating instances
- The Humean constraint reappears *inside* the probability formalism: the convergence to the logical limit is itself not provable from first principles

---

## 4. Does the Unified Picture Entail Bayes' Theorem?

Yes — delivered as a consequence, not an assumption, via multiple routes:

- **Proper scoring rules** → coherence across conditional/unconditional statements → multiplication rule → Bayes as algebra
- **Cox's theorem** → full probability calculus → Bayes from definition of conditional probability
- **De Finetti's representation theorem** → coherent exchangeable beliefs → Bayesian updating is the *unique* coherent update rule (deepest justification)
- **Bernstein-von Mises** → presupposes Bayes; tells you what it looks like in the limit (downstream, not upstream)

---

## 5. The Key Refinement: Epistemic Situation, Not Epistemic Agent

### 5.1 The Problem with "Agent"

Framing probability around an epistemic *agent* smuggles in:
- A subject who holds beliefs
- A perspective doing the reasoning
- Intentionality — beliefs are about something from someone's point of view

This makes probability psychologistic and mind-dependent in a way that conflicts with the user's structural realism.

### 5.2 The Replacement

**Epistemic situation**: a set of available structural information — facts, constraints, symmetries, known relations — from which inferences can be drawn, without requiring a mind to draw them.

- **Logic** = conclusions fully determined by the epistemic situation
- **Probability** = unique well-behaved measure of what is *partially* determined by the epistemic situation
- The prior = background structural information already contained in the epistemic situation (symmetries, known constraints) — not chosen but *read off* from the situation's structure
- No agent required — the probability distribution is a structural feature of the epistemic situation, just as logical consequences are

### 5.3 The Refined Interpretation

> **Probability is the mathematics of partial structural determination within an epistemic situation.** An epistemic situation is a set of structural information — constraints, symmetries, known relations — that may fully determine some conclusions (logic applies) or partially determine others (probability applies). The prior is not chosen but read off from the structure of the situation itself. No agent is required.

This is a novel position drawing on:
- Carnap's spirit (probability as logical relation, not mental state)
- Jaynes's practice (priors from symmetry/maximum entropy)
- The user's structural realism as the metaphysical foundation

---

## 6. Connections to Named Views

| Feature | Closest named view | Where it diverges |
|---|---|---|
| Probability as partial determination | Carnap's logical probability | Carnap failed to find unique confirmation function; this grounds it in limit behaviour instead |
| Priors from structure | Objective Bayesianism (Jaynes) | Drops the agent; priors are structural facts, not prescriptions |
| Coherence + proper scoring | Subjective Bayesianism | Drops the subjectivity; replaces agent with epistemic situation |
| Limit behaviour | Cox/Jaynes | Adds the reverse direction: probability *defined by* its limit behaviour |
| Quantum extension | Quantum Bayesianism (QBism) | QBism keeps the agent; this view does not |

---

## 7. Open Problems and Future Directions

### 7.1 The Principal Principle Interface

Lewis's Principal Principle says: credences should match known objective chances. In this framework, this becomes the interface between the quantum probability level and the classical probability level in the hierarchy. This interface is philosophically unfinished — it's not fully explained *why* the epistemic situation should be constrained by ontological chances, or what grounds those chances. This is perhaps the deepest open problem inherited from QM foundations.

### 7.2 The Prior Without an Agent

If priors are read off from the structure of the epistemic situation (via maximum entropy, symmetry, etc.), is this procedure *unique*? There are known cases where symmetry arguments for priors conflict (Bertrand paradoxes, different parameterisations giving different Jeffreys priors). A full account needs to explain when the epistemic situation uniquely determines a prior and when it underdetermines it.

### 7.3 Non-Additive Uncertainty Measures

Dempster-Shafer belief functions, possibility theory, and imprecise probabilities also reduce to logic at the extremes and are continuous in some sense, but don't satisfy Kolmogorov additivity. The unified picture needs either to exclude these (by deriving additivity from the limit/smoothness conditions more rigorously) or to accommodate them as legitimate generalisations of probability in the same way probability generalises logic.

### 7.4 The Ontological/Epistemic Gap at the Quantum Level

The framework places quantum probability one level below classical probability in the hierarchy, with ontological gaps potentially preventing the limit from being reached. But whether quantum indeterminacy is epistemic or ontological remains unresolved. The framework is *consistent* with both, but a full account would need to take a position — or explain why the distinction doesn't matter structurally.

### 7.5 Higher-Level Structures and Emergence

The user's framework says higher-level structures (tables, feelings, the number 2) are formed from lower-level ones and can be observed but only proven from first principles. How does probability at the higher level (e.g. the probability that this is a table) relate to probability at the lower level (quantum amplitudes of elementary particles)? This is the problem of **emergent probability** — whether and how macro-level probabilistic regularities reduce to or supervene on micro-level ones. Statistical mechanics is the paradigm case; the general question is open.

### 7.6 Feyerabend Revisited

The framework developed here — probability as partial structural determination within an epistemic situation — may offer a cleaner response to Feyerabend than standard Bayesianism. If probability is not agent-relative but situation-relative, then methodological pluralism is not just tolerated but *structurally explained*: different epistemic situations (different background constraints, different priors read off from different structural information) legitimately yield different probability distributions. "Anything goes" becomes "everything is conditioned on its epistemic situation." Whether this fully answers Feyerabend's political/sociological critique remains to be examined.

### 7.7 Connection to Information Theory

The link between probability, entropy (Shannon), and structural information is implicit throughout but not fully developed. Maximum entropy as the prior-selection principle connects information theory to the epistemic situation framing. A fuller account might develop probability as the mathematics of partial structural determination *measured in bits* — making the connection to Shannon explicit and grounding the limit behaviour in information-theoretic terms.

---

## 8. Key References

- Cox, R. (1946). Probability, frequency, and reasonable expectation. *American Journal of Physics*.
- De Finetti, B. (1972). *Probability, Induction and Statistics*.
- Jaynes, E.T. (2003). *Probability Theory: The Logic of Science*.
- Ladyman, J. & Ross, D. (2007). *Every Thing Must Go: Metaphysics Naturalised*. (OSR)
- Lewis, D. (1980). A subjectivist's guide to objective chance. (Principal Principle, Best Systems)
- Movellan, J.R. & Nelson, J.D. (2001). Probabilistic functionalism: A unifying paradigm for the cognitive sciences. *Behavioral and Brain Sciences* 24:4.
- Paris, J. & Vencovská, A. (1990). A note on the inevitability of maximum entropy. *International Journal of Approximate Reasoning*.
- Feyerabend, P. (1975). *Against Method*.
- Williamson, J. (2010). *In Defence of Objective Bayesianism*.
