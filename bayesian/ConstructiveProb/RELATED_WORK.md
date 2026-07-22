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

What appears **genuinely open / defensibly ours** (updated to the *proved* state of the repo):

1. **The machine-checked (Lean/mathlib) development of the *constructive* theory.** The
   valuation *object* is already formalized elsewhere (Coq/HoTT — see Thread F), but as
   constructive *measure theory*; the Cox / Dempster–Shafer / slack / decidability development on
   top of it is formalized here for the first time, and mathlib has none of it. *(Do not claim
   "first formalization of valuations"; claim "first formalization of this development on them.")*
2. **The sum rule is irreducible** (`modularity_irreducible`, `no_disjunction_functional`):
   modularity cannot be derived from the disjunction/marginal data and must be posited. This is a
   genuine, apparently-new result — and it means the naive "uniqueness" goal below is unreachable
   as stated.
3. **A constructive Cox *regraduation* theorem** (`constructive_cox`) — **not** a uniqueness
   theorem. Given modularity, the plausibility regraduates to a valuation (`g = ENNReal.ofReal`);
   the product-rule half is Aczél (logic-independent), the sum-rule half is modularity. A full
   *uniqueness* result (deriving modularity from a more primitive desideratum) remains open; the
   honest substitute is the **mixture characterization** (`eq_mix_deltaPoint`: on a finite frame,
   valuations = finite mixtures of point-valuations — "modularity = the mixing-closure of point
   additivity").
4. **The synthesis + concrete bridges, machine-checked.** Localic valuation ↔ Weatherson ↔
   Paris's DS theorem ↔ `Bel=P(□φ)` ↔ GMT, assembled in one place — now with the **DS
   2-monotonicity bridge** (`two_monotone`), the **decidability/halting guard** (`Halting.lean`),
   the **slack decomposition**, and **Scott-continuity ⟹ purely atomic in general**
   (`isPurelyAtomic_of_scott`) as theorems, not just motivations.

Net: reposition the contribution as **"the formalization of the constructive development + the
irreducibility/characterization results + the synthesis and its concrete bridges,"** *not* "a new
probability object," *not* "a uniqueness theorem," and *not* "the DS/excluded-middle link."

---

## Thread A — Non-classical / intuitionistic probability (most decisive prior art)

- **Brian Weatherson (2003), "From Classical to Intuitionistic Probability,"** *Notre Dame
  J. Formal Logic* 44(2):111–123. **Verified against the paper (axioms quoted verbatim):** a
  `⊢`-probability function satisfies **(P0)** `Pr(A)=0` if `A` is a `⊢`-antithesis, **(P1)**
  `Pr(A)=1` if `A` is a `⊢`-thesis, **(P2)** `A⊢B ⟹ Pr(A)≤Pr(B)` (monotonicity), **(P3)**
  `Pr(A)+Pr(B)=Pr(A∨B)+Pr(A∧B)` (modularity/inclusion–exclusion), with conditional
  `Pr(A,B)=Pr(A∧B)/Pr(B)`. `Pr(¬A)=1−Pr(A)` is **not assumed** — it is *derived* classically from
  (P3)+(P0)+(P1) (since `A∧¬A` is a classical antithesis and `A∨¬A` a classical thesis) and
  **fails intuitionistically** (`A∨¬A` is not an IL-thesis), giving `Pr(A)+Pr(¬A) ≤ 1`. **These
  are exactly our `Valuation` axioms** (`map_bot`/`map_top`/`mono'`/`modular'`) plus `condVal`; this
  is the closest single antecedent, now confirmed precisely (the object is *not* new — our
  `Valuation` on a frame is Weatherson's `⊢_IL`-probability function). He also gives a weaker
  disjoint-additive variant **(P3′)** `⊢¬(A∧B) ⟹ Pr(A∨B)=Pr(A)+Pr(B)` (cf. our
  `additive_of_disjoint`).
  [Semantic Scholar](https://www.semanticscholar.org/paper/From-Classical-to-Intuitionistic-Probability-Weatherson/06f277bb4fba61541e84f7aa7d5bc409ae7ae6c5)
  · [author PDF](https://brian.weatherson.org/quarto/posts/conprob/From%20Classical%20to%20Intuitionistic%20Probability.pdf)

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

- **Bidlingmaier, Faissole & Spitters (2019/2021), "Synthetic topology in HoTT for probabilistic
  programming,"** *MSCS*; Coq/HoTT library [`FFaissole/Valuations`](https://github.com/FFaissole/Valuations)
  (`Valuations.v`, `LowerIntegrals.v`). Point-free **valuations and lower integrals** on sets via
  synthetic topology, with Riesz/Fubini and the Lebesgue valuation, for probabilistic-programming
  semantics. **This is the existing formalization of our object** — the modular localic valuation —
  and the single most important prior-formalization citation. *But note the differences* (verified
  against the paper): their valuations are **Scott-continuous** (ω-cpo-valued, for fixpoint
  semantics) and are used as the constructive analogue of a **measure**; we deliberately **omit
  Scott-continuity** (which is what exposes the non-representable valuations, `topIndicator`, and
  the atomic/diffuse gap) and read the object as **logic-weakened credence**. A third difference
  a comparing reviewer will notice: their valuations take values in the **lower reals**
  (`RlowPos`), the device that makes their development constructive at the *meta*-theory level,
  whereas ours take values in mathlib's classical `ℝ≥0∞` — so our constructivity is object-level
  only (no excluded middle on the frame; classical Lean meta-logic), and comparisons should not
  read "ConstructiveProb" as a claim of constructive meta-theory. See the README's meta-logic
  note. It was **motivated by,
  and reimplemented in HoTT to fix limitations of, the ALEA Coq library** (which uses setoids and a
  Giry-style monad on `Set` and cannot even prove the monad laws without funext) — *not* built on
  top of ALEA.

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

- Adjacent (interior/closure reading): **rough sets** identify a belief/plausibility pair with the
  **lower/upper approximation** operators. **Verified:** Skowron ("The rough sets theory and evidence
  theory," *Fundamenta Informaticae* XIII, 1990, 245–262; and *Bull. Polish Acad. Sci.* 37, 1989)
  gives one direction, Yao & Lingras ("Interpretations of belief functions in the theory of rough
  sets") the converse — the probabilities of lower/upper approximations in an approximation space are
  a dual belief/plausibility pair, and every belief structure so arises. Note this is the
  *approximation-operator* (equivalence-relation / partition) version of interior/closure, a special
  case of the general topological `□` in our GMT reading — the same structural idea, cite as an
  analogue, not the same theorem.
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
- **The product-rule engine is classical Aczél/Hölder — cite it; we mechanize, not invent.** The
  associativity functional equation `F(F(x,y),z)=F(x,F(y,z))` forcing a regraduation to
  multiplication is **Aczél** (*Lectures on Functional Equations and Their Applications*, 1966); the
  ordered-semigroup embedding into `(ℝ,+)` is **Hölder's theorem** (1901), also the backbone of the
  t-norm/t-conorm representation literature (Klement–Mesiar–Pap, *Triangular Norms*, 2000). Our
  `Aczel.lean` is a **from-scratch Lean proof on the positive cone** of this classical result; the
  theorem itself is not ours, and the verbatim `[0,1]` version (continuity + off-cone extension) is
  not yet done. **Mathlib-gap claim, verified by inspecting the vendored mathlib (`v4.31.0`):** it
  *has* the archimedean ordered-**field** → ℝ embedding (`CompleteField.inducedMap`) and
  archimedean-group structure theory (`Archimedean/Class.lean`; the discrete-or-densely-ordered
  dichotomy in `ArchimedeanDensely.lean`), **but not** Hölder's embedding of an archimedean ordered
  *group* into `(ℝ,+)`, and **no** triangular-norm / t-conorm / divisible-ordered-semigroup-on-an-
  interval machinery at all (a grep for `t-norm`/`triangular norm` returns nothing; the only "Hölder"
  in mathlib is Jordan–Hölder and the Hölder norm/inequality). So the specific object the Cox scale
  needs — a divisible ordered semigroup on an interval with a boundary identity, generator built by a
  root/dyadic-limit — is genuinely absent; building it is the work.
- **Terenin & Draper** — their Cox repair was **withdrawn by the authors for an unrepairable
  error.** Cite as retracted, not as a result.
- **Current status in this repo (what came of Thread E's "open door").** Dropping R3 over a
  Heyting base and asking for uniqueness turned out to be more subtle than "prove the theorem":
  `modularity_irreducible` shows the sum rule is *not derivable* from the disjunction data, so R3's
  replacement (modularity) must be **posited**, not earned. What is proved: `constructive_cox` (a
  regraduation theorem, positing modularity; product half = Aczél, sum half = modularity), plus the
  mixture characterization (`eq_mix_deltaPoint`) as the honest stand-in for uniqueness. A genuine
  uniqueness theorem — deriving modularity from a more primitive desideratum — remains open.

---

## Thread F — Proof-assistant formalizations

- **The precise overlap (do not overclaim).** The valuation *object* **is** already
  formalized — in Coq/HoTT, by Bidlingmaier–Faissole–Spitters (Thread B), as constructive measure
  theory. So the accurate claim is **not** "first formalization of valuations" but "first
  formalization of the constructive/non-additive **Cox–DS development** on them" (slack, the R3
  hinge, Cox + Aczél, the representation/mixture/Scott-atomic theorems, the halting guard, the DS
  2-monotonicity bridge). "Most of this is already done in Coq/Agda/HoTT" is **false** and must not
  be written.
- **Lean / mathlib: none of the relevant structures.** Confirmed by direct inspection:
  classical measure theory, Markov kernels, disintegration, KL divergence, independence — but
  **no** MV-algebras, effect algebras, states-on-algebras, Dempster–Shafer/capacities, or
  localic valuations (mathlib's `Valuation` is the *valued-field* notion). So doing the whole
  development in Lean is unclaimed.
- **Coq (ALEA):** measure theory as a Giry-monad variant on `Set`; the library the HoTT valuation
  work was built to improve on. A *different object* from ours (additive distributions).
- **Cubical Agda — Karen Sargsyan (2026), "A cubical formalisation of conditional independence,
  Bayesian conditioning, and Pearl's d-separation soundness"** ([arXiv:2606.20351](https://arxiv.org/abs/2606.20351)).
  Finite-distribution monad `FDist` as a Markov-category instance (HIT), conditioning, d-separation
  soundness. *Verified:* Markov-category tradition, additive distributions — does **not** touch
  modular valuations / MV / DS / Cox / Gleason, so it does not pre-empt us.

---

## Thread G — Choquet capacities and imprecise probability (where our DS bridge sits)

Added because `two_monotone` now places our object precisely in a well-studied hierarchy — a
reviewer from the imprecise-probability community (IJAR / ISIPTA–SIPTA) will expect these citations.

- **The nesting** (Choquet 1953; Shafer 1976; Walley 1991, *Statistical Reasoning with Imprecise
  Probabilities*): additive probability ⊂ **belief functions** (∞-/totally-monotone capacities;
  equivalently non-negative Möbius transform) ⊂ **2-monotone (convex / Choquet) capacities** ⊂
  coherent lower probabilities ⊂ Walley's coherent **lower previsions**. The defining inequality of
  a 2-monotone capacity is `P(A) + P(B) ≤ P(A∪B) + P(A∩B)`.
- **Where we land — state exactly.** On the frame our `v` is a *modular* valuation (Thread B). On
  the **Booleanization**, `Valuation.two_monotone` proves `v(A) + v(B) ≤ v((A⊔B)ᶜᶜ) + v(A⊓B)` — i.e.
  `v` is a **2-monotone capacity**, verbatim the inequality above. By Paris's theorem (Thread A) it
  is in fact a **belief function** (∞-monotone); but we have machine-checked only the **2-monotone
  hallmark**, not the full ∞-monotone (Möbius ≥ 0) tower. So: *do not call `v` a "belief function"
  in the formalization without the caveat "2-monotone proved, ∞-monotone open."* The belief/
  plausibility gap is the slack (`plausibility_sub_self`) — the "imprecision" of this literature.
- **Adjacent framing to cite, not claim:** DS belief functions as coherent lower probabilities
  (Walley; Miranda–de Cooman); this is also the natural reading of a valuation as a *lower*
  prevision. A venue signal: IJAR/ISIPTA is a natural home for the DS-facing version of this work.

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

## Where this leaves the research (updated to the proved state)

The originality is no longer "the open door" — much of Thread E has been walked through. Concretely:

- **Done and defensible:** the machine-checked *constructive* development (Thread F caveat: the
  object, not the development, is prior-formalized); the irreducibility of the sum rule
  (`modularity_irreducible`, `no_disjunction_functional`); the constructive Cox *regraduation*
  theorem + Aczél generator; the mixture characterization; the DS 2-monotonicity bridge; the
  Scott-⟹-atomic generalization; the halting/decidability guard; the explicit GMT/measure synthesis.
- **Still open (honest):** a genuine *uniqueness* theorem (deriving modularity from a more primitive
  desideratum); the verbatim Aczél/`AczelStatement` on `[0,1]` (continuity + off-cone extension);
  full representation for non-spatial frames (M3c); and ∞-monotonicity of the DS bridge (only
  2-monotone proved).
- **To cite, not claim:** Weatherson, Paris, Williams, Colyvan (Thread A); Vickers, Coquand–Spitters,
  Bidlingmaier–Faissole–Spitters (Threads B, F); Ruspini/Smets/Pearl, GMT (Thread C); Mundici,
  Flaminio–Godo–Hosni (Thread D); Cox, Halpern, Van Horn (Thread E); Choquet, Shafer, Walley
  (Thread G).

**Provenance note.** This document began as a pre-formalization literature scan (≈100 claims,
73/75 adversarially verified); it has since been updated against the *proved* repo and
fact-checked by follow-up search. **Verified this pass:** Weatherson's axioms P0–P3 (quoted verbatim
from the paper — they are exactly our `Valuation` axioms; negation derived, not assumed); the
Faissole–Spitters overlap (their valuations are Scott-continuous measure theory in Coq/HoTT); the
Sargsyan cubical-Agda reference ([arXiv:2606.20351](https://arxiv.org/abs/2606.20351), Markov
categories, different object); the Choquet/Walley capacity hierarchy (our `two_monotone` sits at the
2-monotone level); the Skowron/Yao rough-set correspondence (approximation-operator version); and the
mathlib gap (archimedean field→ℝ embedding present; Hölder-for-groups and interval-semigroup machinery
absent; no t-norms). No confidence flags remain open in the theses above; any *further* specifics (e.g.
exact statements of secondary rough-set extensions) should still be checked before a paper cites them.
