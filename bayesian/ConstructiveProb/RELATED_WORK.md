# Related work & novelty assessment

*Prior-art map for the "modular valuation on a Frame, with a constructive-logic limit"
program (see [`README.md`](README.md) and [`ConstructiveProb/Basic.lean`](ConstructiveProb/Basic.lean)).*

Compiled from a fanned-out literature search (≈100 extracted claims, 73/75 surviving
adversarial verification) plus targeted follow-up fetches. Confidence is noted per item.
**Read this before claiming novelty anywhere.**

---

## TL;DR — what is and isn't new

Most individual pieces of this project **already exist**. Be honest about that:

- The **object** (modular valuation on a frame, no complement law) is Vickers' *localic
  valuation*, essentially verbatim.
- **"Intuitionistic probability" with `P(a)+P(¬a) ≤ 1`** is Weatherson (2003).
- The **identification of such non-classical probabilities with Dempster–Shafer belief
  functions is a theorem** — Paris (1994), drawing on Shafer (1976); Williams reports the
  intuitionistic case citing Weatherson.
- **"Recovers Kolmogorov on Boolean algebras"** has a precedent in states on MV-algebras.
- The **`Bel = P(□φ)` "probability of provability"** reading of DS is classical
  (Ruspini/Smets/Pearl), and the **Gödel–McKinsey–Tarski** translation is the standard
  bridge between intuitionistic logic and the modal S4 in which that reading lives.

What appears **genuinely open / defensibly ours**:

1. **A constructive (intuitionistic) Cox-style *uniqueness* theorem.** No one has one;
   existing Cox proofs use double-negation elimination, so it is a real departure, not a
   reuse.
2. **A machine-checked (Lean/mathlib) development.** All existing formalization is in
   Coq/Agda/HoTT; mathlib has none of this.
3. **The explicit synthesis** tying together localic valuation ↔ Weatherson intuitionistic
   probability ↔ Paris's DS theorem ↔ `Bel=P(□φ)` modal reading ↔ GMT ↔ a uniqueness result.
   No single source assembles all of these.

Net: reposition the contribution as **"the uniqueness theorem + the formalization + the
synthesis,"** not "a new probability object" and not "the DS/excluded-middle link."

---

## Thread A — Non-classical / intuitionistic probability (most decisive prior art)

- **Brian Weatherson (2003), "From Classical to Intuitionistic Probability,"** *Notre Dame
  J. Formal Logic* 44(2):111–123. Defines probability over intuitionistic propositional
  logic with normalization, monotonicity, and the modular/inclusion–exclusion law, **without**
  `P(¬a)=1−P(a)` — so `P(a)+P(¬a) ≤ 1`, and classical probability returns when excluded
  middle is added. *This is the closest single antecedent to our `Valuation` +
  `classical_additivity` + `add_compl_le_one`.* (High confidence on framing; I have not
  re-read the paper line-by-line — verify the exact axiom list before citing specifics.)
  [Semantic Scholar](https://www.semanticscholar.org/paper/From-Classical-to-Intuitionistic-Probability-Weatherson/06f277bb4fba61541e84f7aa7d5bc409ae7ae6c5)

- **J. Robert G. Williams, "Probability and Non-Classical Logic"** (preprint 2012; in *The
  Oxford Handbook of Probability and Philosophy*). Survey of the whole area. Reports that
  **Paris gives a theorem (drawing on Shafer 1976) that convex combinations of non-classical
  truth values are exactly Dempster–Shafer belief functions**, the modular law replacing
  classical inclusion–exclusion, "for the intuitionistic case compare Weatherson (2003)."
  *This is the sentence that most constrains our novelty.*
  [PDF](https://fitelson.org/few/few_12/williams_paper.pdf)

- **Jeff B. Paris (1994), *The Uncertain Reasoner's Companion*,** Cambridge UP. Source of the
  belief-function result Williams cites; also the modern home of the "belief-as-probability
  must be a probability" justification tradition (distinct from Paris–Vencovská's *maximum
  entropy* uniqueness result — don't conflate them).

- **Mark Colyvan (2004), "The philosophical significance of Cox's theorem,"** *IJAR* 37:71–85.
  Argues Cox smuggles in classical logic; proposes non-classical probability where `P∨¬P` is
  not forced to 1 — matching the "slack" idea, and pointing to Weatherson.

**Takeaway:** the *definition* and the *DS identification* are not new. Cite these front and
center; do not present the DS/excluded-middle link as our discovery.

---

## Thread B — Localic / constructive valuations (our object, already built)

- **Steven Vickers, "A localic theory of lower and upper integrals"** (*MLQ* 2008) and
  **"A monad of valuation locales"** (2011). Defines a valuation on a frame `L` as
  `m:L→[0,∞]`, `m(⊥)=0`, **modular**, Scott-continuous — *no complement assumption*. Isolates
  the "modular monoid" `M(L)` (`a+b=(a∨b)+(a∧b)`). Builds the localic analogue of the **Giry
  monad**. *Our `Valuation` is this.* (High confidence.)

- **Thierry Coquand & Bas Spitters (2009), "Integrals and Valuations,"** *J. Logic & Analysis*
  1(3):1–22. Constructive, point-free Riesz-representation correspondence between integrals
  and valuations; probability valuations = the total-mass-1 subspace.

- **Bidlingmaier, Faissole & Spitters** — point-free valuations / lower integrals in
  **Homotopy Type Theory**, grounded in the **ALEA** Coq library (Giry monad in Coq). *Nearest
  existing formalization of constructive valuations — in Coq/HoTT, not Lean.*

- **Jones & Plotkin (1989), "A probabilistic powerdomain of evaluations,"** LICS. The
  domain-theory ancestor; this is the **Dana Scott** lineage (valuations on dcpos), which is
  the "Scott" relevant to us.

- Standard "measurable space ↔ locale, σ-additivity ↔ Scott continuity, additivity ↔
  modularity" dictionary (nLab; Vickers). Note: none of these connect the localic theory to
  Cox or to Dempster–Shafer — **that bridge is unbuilt**, and is part of our opening.

---

## Thread C — DS as "probability of provability," and the GMT bridge

- **`Bel(A) = P(□A)`**: originates with **Ruspini (1986/87)**, crystallized by **Smets
  (1988, 1991)** ("probability of fully believing φ") and **Pearl (1988)** ("probability of
  provability"). The modal reading reproduces all the belief-function inequalities. Modal
  axiomatization: **Harmanec, Klir & Resconi (1994)**, *IJIS* 9:941–951. Historically open
  point: whether Dempster conditioning matches modal conditioning.

- **Gödel–McKinsey–Tarski translation** (Gödel 1933; McKinsey & Tarski 1948): intuitionistic
  logic embeds faithfully into modal **S4** by prefixing `□` to every subformula, and the
  soundness is grounded in the *same open-set/topological semantics* as Heyting algebras
  (`□` = interior). [Modal companion (Wikipedia)](https://en.wikipedia.org/wiki/Modal_companion)

- **Why this matters for us (conjecture worth chasing):** via GMT, our Heyting valuation
  `v(a)` and the modal belief `Bel = P(□φ)` may be *the same construction* — `□` ≈ interior ≈
  the regular/open part, and `v` on opens ≈ `P(interior)` ≈ `P(□)`. The follow-up search
  found **no single source unifying** intuitionistic probability + Heyting + belief functions
  + GMT/S4 + non-additivity. That unification is a concrete, apparently-open target.

- Adjacent: **Bílková et al., "Reasoning with belief functions over Belnap–Dunn logic"**
  (arXiv:2203.01060) and **"An elementary belief function logic"** (J. Applied Non-Classical
  Logics, 2023) — belief/plausibility operators over *paraconsistent* (4-valued) logic, where
  again `P(φ)+P(¬φ)` need not be 1. Different logic (paraconsistent vs. intuitionistic), same
  non-additivity phenomenon.
  [Belnap–Dunn belief functions](https://arxiv.org/pdf/2203.01060) ·
  [Elementary belief function logic](https://www.tandfonline.com/doi/pdf/10.1080/11663081.2023.2244366)

---

## Thread D — Algebraic logic of probability (a *different* non-classical axis)

- **States on MV-algebras** (Łukasiewicz logic): **Mundici** ("Averaging the truth-value,"
  *Studia Logica* 1995), **Kroupa**, **Flaminio**. A state `s:A→[0,1]`, `s(⊤)=1`, additive on
  `⊙`-disjoint pairs — a normalized finitely-additive valuation that **reduces exactly to
  Kolmogorov probability when the MV-algebra is Boolean**. A direct precedent for our
  Boolean-limit result.
  - **Crucial contrast:** in the MV/Łukasiewicz setting the **complement law is *retained***
    (`¬x = 1−x`, so `P(¬φ)=1−P(φ)`). MV weakens *bivalence of truth*; **we** weaken *the
    complement / excluded middle* on a Heyting algebra. These are **different generalizations**
    — MV keeps additivity, we don't. Say so explicitly.
- **Flaminio, Godo & Hosni** — belief functions on MV-algebras with a de-Finetti-style
  Dutch-book ("coherence in the aggregate"). Prior art on DS inside a non-classical logic.

---

## Thread E — Cox's theorem and its repairs

- **Cox (1946); Cox (1961), *The Algebra of Probable Inference*.** The original derivation.
- **Halpern (1999), "A counterexample to theorems of Cox and Fine,"** *JAIR* 10:67–85. Cox's
  theorem as stated is false on finite domains; needs a **denseness axiom (R4)**.
- **Van Horn (2003), "Constructing a logic of plausible inference: a guide to Cox's theorem,"**
  *IJAR* 34:3–24. The standard repaired axiomatization — **explicitly over classical Boolean
  logic**. Its negation axiom **R3** `(¬A|X)=S(A|X)` is the exact hinge: **drop R3 and you get
  a "two-dimensional theory needing two numbers per proposition" — precisely the
  non-additive/slack regime.** This is the pinpoint entry for our uniqueness theorem.
- Existing Cox proofs (**Cox, Van Horn**) use **double-negation elimination** — so a
  constructive Cox theorem **cannot** reuse them; it is a genuine departure. (Encouraging.)
- **Terenin & Draper** — their Cox repair was **withdrawn by the authors for an unrepairable
  error.** Cite as retracted, not as a result.

---

## Thread F — Proof-assistant formalizations

- **Lean / mathlib: none of the relevant structures.** Confirmed by direct inspection:
  classical measure theory, Markov kernels, disintegration, KL divergence, independence — but
  **no** MV-algebras, effect algebras, states-on-algebras, Dempster–Shafer/capacities, or
  localic valuations (mathlib's `Valuation` is the *valued-field* notion). **Doing this in
  Lean is itself unclaimed.**
- **Coq (ALEA):** measure theory as a Giry-monad variant; underpins the HoTT valuation work.
- **Cubical Agda (Sargsyan, 2026):** Bayesian conditioning, Pearl d-separation, probability
  monad as a higher inductive type — constructive, but Markov-category tradition; does **not**
  touch modular valuations / MV / DS / Cox / Gleason, so it does not pre-empt us.

---

## The "Scott" disambiguation (a resolved lead)

- **Philip J. Scott** (U. Ottawa, 1947–2023): categorical/**linear** logic, Geometry of
  Interaction, co-author with Lambek of *Introduction to Higher-Order Categorical Logic*
  (1986). **No work on probability or probabilistic coherence spaces.** A dead end for us.
- The probabilistic-coherence-space people are **Ehrhard, Danos, Pagani, Tasson** — but that
  is *denotational semantics of probabilistic programming*, not foundations of
  probability/Cox/DS. Also not our thread.
- The relevant Scott is **Dana Scott** — probabilistic powerdomain (via Jones & Plotkin),
  i.e. Thread B.

---

## Corrections to earlier notes

- The paper sometimes filed under "Coquand & Spitters" on constructive measure via metric
  Boolean algebras is actually **Coquand & Palmgren (2002)**, *Arch. Math. Logic* 41:687–704 —
  distinct from Coquand & Spitters (2009) *Integrals and Valuations*.
- "Cox proves probability is unique" is **too strong**: Cox is a *representation* theorem
  (probability is *a* legitimate calculus), unique only up to rescaling and under contested
  regularity axioms; the strong Jaynes/Lindley uniqueness reading is not supported once the
  classical-logic assumption is made explicit.

---

## Where this leaves the research

Concentrate originality on **Thread E's open door**: drop Van Horn's R3 over a Heyting base
and prove a uniqueness-up-to-regraduation theorem selecting the localic modular valuation —
formalized in Lean — and make the **GMT unification** (Thread C) explicit. Everything else is
scaffolding to cite: Weatherson, Paris, Williams, Vickers, Coquand–Spitters, Mundici,
Flaminio–Godo–Hosni, Ruspini/Smets/Pearl.
