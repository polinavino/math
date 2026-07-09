# Conversation Summary: Algorithmic Information Theory and Related Ideas

## Topics Covered

### 1. Turing Patterns
Self-organizing spatial structures arising from the interaction of a fast-diffusing **inhibitor** and a slow-diffusing **activator**. Proposed by Alan Turing (1952) as a mechanism for morphogenesis. Produce spots, stripes, and labyrinthine patterns seen in animal coats, digit spacing, and seashells. Key insight: biological complexity can arise from simple local chemical rules without a blueprint.

---

### 2. Kolmogorov Complexity (KC)
The length of the shortest program on a universal Turing machine (UTM) that outputs a given string x:

> **K(x) = min{ |p| : U(p) = x }**

- Defined up to an additive constant (invariance theorem — choice of UTM doesn't matter asymptotically)
- Uncomputable in general
- Formalizes Occam's Razor: simpler explanations get shorter descriptions
- **Conditional KC**: K(x|y) = shortest program outputting x given y as free input
- **Kolmogorov optimality**: achieving the theoretical minimum description length, up to a constant

---

### 3. Solomonoff Induction
Universal Bayesian prediction grounded in KC. Defines a **universal prior**:

> **M(x) = Σ 2^(-|p|)** over all programs p that output x

- Shorter programs get higher prior weight — Occam's Razor is built in
- Dominates all computable priors (up to a multiplicative constant)
- Converges to the true data-generating distribution with probability 1, if computable
- **Uncomputable** — a theoretical gold standard
- Extended by Hutter into **AIXI**: the theoretically optimal (uncomputable) reinforcement learning agent

---

### 4. Information Geometry
Application of differential geometry to probability distributions, treating parametric families as smooth manifolds.

- **Fisher information metric**: the natural Riemannian metric on a statistical manifold; governs how beliefs update
- **α-connections** (Amari): exponential (α=+1) and mixture (α=-1) connections, dual to each other
- **Exponential families** are dually flat → generalized Pythagorean theorem for KL divergence
- **Natural gradient**: gradient descent using the Fisher metric rather than Euclidean metric; parameter-update invariant to reparametrization; underlies K-FAC and informs Adam
- Key figures: Shun-ichi Amari

---

### 5. Karl Friston's Free Energy Principle (FEP)
A unified theory of how biological systems maintain existence by minimizing **variational free energy** — a tractable upper bound on surprise (improbability of sensory states under the agent's model):

> **Free Energy ≥ Surprise**

- **Active inference**: both action and perception are inference; agents minimize *expected* free energy over future states
- **Generative model**: an internal probabilistic model P(sensations, causes) the agent refines over time
- Free energy decomposes as **Accuracy − Complexity**, penalizing model bloat (analogous to Occam's Razor / KC)
- Lives squarely in information geometry: variational FE minimization is gradient flow on a statistical manifold

#### Connections between FEP and KC
- MDL (practical cousin of KC) is formally equivalent to variational Bayesian inference
- The complexity term in free energy mirrors description length
- An agent doing perfect FE minimization over all generative models would asymptotically approach Solomonoff-optimal inference
- The FEP is nature's **computable, embodied approximation** to the uncomputable ideal of Kolmogorov-grounded universal induction

| | Kolmogorov / Solomonoff | Friston FEP |
|---|---|---|
| Core operation | Find shortest program for data | Minimize variational free energy |
| Occam's Razor | Shorter programs preferred | Complexity term penalizes model bloat |
| Ideal agent | AIXI (uncomputable) | Active inference agent (biological) |
| Tractability | Uncomputable in general | Approximate, implementable |

---

### 6. Relative KC and Information as a Relational Property

The encrypted file thought experiment: K(file) is high (file looks random), but K(file|key) is low. Information content is not intrinsic — it depends on what the describer already knows.

This motivated asking whether **information of one system relative to another** is better formalized using relative/conditional KC. Key points:

- **K(x|y)**: standard conditional KC — shortest program for x given y
- **Oracle TMs**: K^y(x) using y as oracle is strictly more powerful than K(x|y)
- **Resource-bounded relativization**: K^k_poly(file) — poly-time programs with oracle k — maps to computational indistinguishability in cryptography
- **Proposed formal definition**:
  > I_y(x) = K_∅(x) - K_y(x)
  
  Measures how much background knowledge y reduces description length of x. Zero when y is irrelevant; maximal when y is the decryption key.

- Information is **relational**: the UTM plays the role of shared computational ontology between two agents

---

### 7. Game-Theoretic Framing of Relative Information

A two-player game between **Oracle** (holds x) and **Guesser** (holds background knowledge y, asks binary questions) operationalizes relative KC:

- **50/50** performance: y is useless, x is algorithmically random relative to y (e.g. encrypted file, unknown key)
- **100%** performance: y fully determines x (known key, or y = x)

The Guesser's optimal success rate is governed by K(x|y) via the algorithmic coding theorem. This gives a **normalized directed mutual information**:

> **Î(x:y) = 1 - K(x|y) / K(x) ∈ [0, 1]**

Extending to any two strings under a fixed UTM U gives a **three-way relation** R_U(x, y) — the information x carries about y as mediated by shared computational substrate U. Key properties:
- **Asymmetric**: R(x,y) ≠ R(y,x) in general (one-way functions)
- **Transitivity failures**: information triangles exist
- **Fixed point at randomness**: truly random x satisfies R(x,y) = 1/2 for all y

---

### 8. Existing Literature Survey

**Directly relevant papers:**

| Paper | Authors | Relevance |
|---|---|---|
| "Game Interpretation of Kolmogorov Complexity" (arXiv:1003.4712) | Muchnik, Mezhirov, Shen, Vereshchagin (2010) | Games as proof technique for KC; relativized KC via Martin's determinacy theorem |
| "Kolmogorov Complexity and Information Theory: With an Interpretation in Terms of Questions and Answers" | Grünwald & Vitányi (2003) | Most direct: KC and mutual information framed via sequential question-answer sessions |
| "Information Distance" | Bennett, Gács, Li, Vitányi, Zurek (1998) | Symmetric pairwise information metric: min program length to transform x↔y; universal cognitive similarity distance |
| "The Similarity Metric" | Li, Chen, Li, Ma, Vitányi (2004) | Normalized Information Distance (NID): symmetric [0,1] similarity via KC |
| "Kolmogorov Complexity and Games" | Vereshchagin (2008, EATCS survey) | Survey of game-theoretic proof methods in AIT |
| Li & Vitányi textbook | Li & Vitányi | Standard reference; Chapter 8 covers algorithmic mutual information in full |

**What exists vs. what's novel in the proposed framing:**

- Directed, normalized Î(x:y) = 1 - K(x|y)/K(x) is **not studied systematically** — NID symmetrizes
- Guessing game as an *empirical approximation scheme* (using real compressors) is **not formalized**
- Three-way R_U(x,y) treating UTM as explicit variable is **not studied as such**

---

### 9. Algorithmic Mutual Information — Formal Definition

For individual objects x, y (not requiring probability distributions):

> **I(x : y) = K(x) - K(x | y) = K(x) + K(y) - K(x, y)**

- Symmetric up to additive logarithmic term (**symmetry of information** theorem)
- Shannon mutual information I(X;Y) = E[I(x:y)] in an appropriate sense — Shannon is the expectation of the algorithmic version
- Answers: *given I already have y, how much does x tell me?*
- Direction matters: I(y:x) = K(y) - K(y|x) answers the reversed question

**Practical examples:**
- x = dictionary, y = text: I(x:y) measures how much the dictionary compresses the text
- x = weather model, y = observed forecast: I(x:y) measures how much the model reduces forecast complexity

---

### 10. Open Questions / Low-Hanging Fruit

1. **Directed normalized algorithmic mutual information** — axiomatic study of Î(x:y) = 1 - K(x|y)/K(x): does it satisfy monotonicity, chain rules? How does it compose? What is the right normalization? Seems writable without proving major new computability results.

2. **Guessing game as approximation scheme** — formally connecting the game success rate to NCD (Normalized Compression Distance) using real compressors as UTM proxies; deriving error bounds or calibration guarantees.

3. **Resource-bounded version for cryptography** — I^poly(x:y) where Guesser is computationally bounded; formalizes cryptographic intuition (ciphertext looks random to poly-time agents without key) in mutual information language. May already exist in crypto complexity literature.

4. **Three-way R_U(x,y)** — studying how I_U(x:y) varies with U; formalizing the idea that agents with different computational substrates disagree about informativeness by a quantifiable amount.

5. **Formal connection FEP ↔ AIT** — rigorously showing that free energy minimization approximates I(sensations:model) in the algorithmic sense. Active area (Ramstead, Sakthivadivel et al.) but not yet rigorous.
