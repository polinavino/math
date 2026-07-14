# ConstructiveProb

A Lean 4 formalization exploring one question:

> **What is probability, really — and what happens to it if we change the logic underneath it?**

This README explains the idea in plain language. You should be able to follow it with a
first course in probability, a little bit of logic, and curiosity. The formal details live
in [`ConstructiveProb/Basic.lean`](ConstructiveProb/Basic.lean); everything below is a map of
what that file is doing and why.

---

## 1. The starting question: what *is* a probability?

You already know how to *use* probabilities. But what are they? There are several classic
answers — "long-run frequencies," "physical tendencies," "personal degrees of belief" — and
each has known problems.

This project follows a different tradition, associated with **Cox** and **Jaynes**:

> **Probability is logic extended to handle uncertainty.**

Start from something no theory of probability disputes: uncertainty is represented by a
function that takes a proposition and, instead of returning just *true* or *false*, returns a
number in `[0,1]`. Frequentists, Bayesians, everyone agrees that far. That much says nothing
specific.

The specific claim comes next, and it is about the **certain limit**. We require that the way
these numbers combine be governed by the underlying logic once the uncertainty is gone: on
propositions that have collapsed to `0` or `1`, the operations `and`/`or`/`not` must reproduce
that logic's own truth tables. A `1` means "true," a `0` means "false," and in that limit the
rules of probability must become the rules of logic — equivalently, the two-valued valuations
are exactly the logic's models. The *hope* is that this requirement, together with internal
consistency, pins down a **unique** such calculus (up to a choice of scale). That is the sense
in which probability is logic extended to handle uncertainty.

This is essentially **Cox's theorem** (1946): a consistent calculus of "degrees of certainty"
that agrees with logic in the certain limit is essentially forced into the usual rules of
probability. (The word "forced" needs qualification — Cox's original argument has a well-known
gap; see the note at the top of `Basic.lean` — but that's the spirit.)

The logic run through this recipe is almost always **classical** logic. The wager of this
project is that the same recipe can be run over *other* logics, and that the choice of logic is
precisely what fixes the shape of the resulting probability. (Which logic, and what changes, is
§2.)

---

## 2. The twist this project explores

Cox's story quietly assumes the logic you collapse into is **classical logic** — the logic
where every statement is either true or false, and `P or (not P)` is always true (the "law
of excluded middle").

But classical logic is not the only logic. **Constructive (intuitionistic) logic** is a
weaker, very natural system used across mathematics and computer science. Its motto is:

> To assert a statement, you must be able to *construct evidence* for it. "P or not-P" is
> **not** automatically true, because you might have evidence for neither.

So here is the question driving this repository:

> **What calculus of uncertainty do you get if you insist its "certain limit" is
> *constructive* logic instead of classical logic?**

Nobody's answer is "ordinary probability," because — as we'll see — the moment you drop the
law of excluded middle, the familiar rule `P(not A) = 1 − P(A)` **has to break**. Something
more general than probability appears. Pinning down *what*, and whether it's unique, is the
research program.

---

## 3. The cast of characters (in plain terms)

To do this precisely we need to name the logics as algebraic objects.

- **Boolean algebra** = the algebra of *classical* logic. Think of it as "collections of
  possibilities" with `and` (∩), `or` (∪), and a genuine `not` (complement). The key
  feature: `A or (not A)` fills up *everything* — excluded middle holds.

- **Heyting algebra** = the algebra of *constructive* logic. Same `and` and `or`, but `not`
  is weaker. The key difference: `A or (not A)` need **not** fill up everything. There can be
  a "leftover region" that neither `A` nor `not A` covers. In Lean this is packaged as a
  **`Frame`** (a Heyting algebra that also has infinite `or`s — technically the algebra of
  open sets of a space, a.k.a. a *locale*).

A concrete picture you can hold onto: take the **open subsets of the real line**. `and` is
intersection, `or` is union. But what is `not U`? It can't just be the set-complement,
because that usually isn't open. The best *open* answer is "the interior of the complement."
Now take `U = (−∞, 0)`. Its constructive negation is `(0, ∞)`. And `U or (not U)` =
`(−∞,0) ∪ (0,∞)` — which misses the single point `0`. That missing point is excluded middle
failing. **Open sets are a Heyting algebra, not a Boolean one**, and that gap is the whole
story in miniature.

One fact survives the switch and does a lot of work: even constructively, `A and (not A)` is
still *empty* (`⊥`). It's only `A or (not A) = ⊤` that fails. That asymmetry is what makes
everything below tick.

---

## 4. What "probability" becomes here

We define (see `Valuation` in the file) a **plausibility valuation** `v`: it assigns each
statement a number in `[0, ∞]`, with `v(⊥) = 0` (impossible ⟶ 0), `v(⊤) = 1` (certain ⟶ 1),
it's monotone (more inclusive statement ⟶ at least as much weight), and it obeys the

> **modular law:** `v(A) + v(B) = v(A or B) + v(A and B)`.

The modular law is just **inclusion–exclusion**, the one piece of additivity that makes
sense without a well-behaved complement. Notice what we did *not* assume: we never said
`v(not A) = 1 − v(A)`. Whether that holds is now something to *discover*, not to build in.

Here's the punchline. Combine the modular law with the surviving fact `A and (not A) = ⊥`:

```
v(A) + v(not A) = v(A or not A) + v(A and not A)
               = v(A or not A) + 0
               = v(A or not A)   ≤   v(⊤) = 1.
```

So `v(A) + v(not A) ≤ 1`, with a **gap** exactly equal to how far `A or (not A)` falls short
of "everything." We call that gap the **slack**:

```
slack(A) = 1 − ( v(A) + v(not A) ).
```

- In **classical** logic, `A or (not A) = ⊤` always, so the slack is always `0` and we
  recover the familiar `v(A) + v(not A) = 1`. Ordinary probability.
- In **constructive** logic, the slack can be **positive**. That positive-slack object
  coincides with what **Dempster–Shafer theory** calls a *belief function* — a well-known
  non-additive generalization of probability.

This is not a new observation, and the README should not pretend otherwise: **Weatherson
(2003)** already defined this "intuitionistic probability," and a theorem of **Paris (1994),
building on Shafer (1976)**, identifies such non-classical probabilities *with* Dempster–Shafer
belief functions. What this project adds is not the object but (i) a machine-checked
development of it, and (ii) toward *uniqueness*: a corrected constructive Cox regraduation theorem
(`constructive_cox`, §6.4) together with a characterization pinning modularity down as the
mixing-closure of point additivity (`eq_mix_deltaPoint`, §6) — the honest stand-in for a full
uniqueness result, whose remaining form (deriving modularity from a more primitive desideratum)
is still open (see §6, §7, and [`RELATED_WORK.md`](RELATED_WORK.md)).

### Splitting the slack into two obstructions

The slack looks like one number, but it is really two different failures added together, and
you can see this by feeding the pair `(not not A, not A)` through the modular law. Constructively
`not A` and `not not A` are always **disjoint** (`(not A) and (not not A) = ⊥`) but their union
is usually *not* everything — so, exactly as above, `v(not not A) + v(not A) = v(not not A or
not A) ≤ 1`. Because `A ≤ not not A`, subtracting this from the original slack telescopes cleanly
(the `v(not not A)` cancels) and leaves

```
slack(A)  =  ( v(not not A) − v(A) )   +   ( 1 − v(not not A) − v(not A) ).
                   ‖                              ‖
          double-negation gap             De Morgan / weak-LEM gap
```

Both pieces are `≥ 0`, and each is its own kind of non-classicality:

- The **double-negation gap** `v(not not A) − v(A)` measures how far `A` is from being
  **regular** (`not not A = A`). It is `0` exactly when `A` equals its own double negation.
- The **De Morgan gap** `1 − v(not not A) − v(not A)` measures the failure of *weak* excluded
  middle `not not A or not A = ⊤` (a strictly weaker law than `A or not A = ⊤`). The element
  `not not A or not A` is always **dense** — its negation is `⊥` — so this gap is the weight
  sitting between a dense element and the top.

The whole slack vanishes iff *both* do, which is exactly `A` being **complemented** — so this
refines the earlier "slack `= 0` ⟺ classical" into its two independent causes. It also
**explains a puzzle** the formalization turned up: a valuation can carry slack on a
*regular-but-uncomplemented* element. With the split that is a one-liner — regularity zeroes the
first gap, so for a regular `A` all the slack is the De Morgan gap `1 − v(A or not A)`.
(Formalized in `Basic.lean`: `slack_eq_dnGap_add_deMorganGap`, `slack_eq_zero_iff`,
`slack_eq_deMorganGap_of_regular`.)

**A frontier this opens (now partly proved).** The map `A ↦ not not A` is the *double-negation
nucleus*: the regular elements form a genuine **Boolean** algebra (the Booleanization, à la
Glivenko), and there `(not not A, not A)` really *is* a complementary pair. Restricting `v` to the
regular elements gives — one checks the modularity defect is one-signed — a **supermodular
(2-monotone) capacity**: `v(A ∨_B B) + v(A ∧ B) ≥ v A + v B`, where `A ∨_B B = (A ⊔ B)ᶜᶜ` is the
Boolean join. That is exactly the defining convex-capacity inequality of a **Dempster–Shafer
belief function** *on a Boolean algebra*, with the belief/plausibility interval width being the
slack. This is now a **theorem** — `Valuation.two_monotone` and `plausibility_sub_self` in
[`Belief.lean`](ConstructiveProb/Belief.lean) — proved in one line from modularity plus
`A ⊔ B ≤ (A ⊔ B)ᶜᶜ`. (A *bona-fide* belief function is `∞`-monotone, a whole tower of inequalities;
the `2`-monotone hallmark is proved, the full tower remains future work.) The Booleanization is also
exactly where a classical (R3/Cox) argument would live — so it is the principled way to extract
"the classical probability inside `v`." *(Note: an earlier draft mislabelled this "submodular";
belief functions are supermodular / 2-monotone — the `≥` direction proved here.)*

### A note on the word "belief"

Dempster–Shafer calls its objects *belief functions* and calls the slack *ignorance*; the
modal reading in §8 even writes `Bel(A) = P(□A)`, "the probability of *believing* `A`". We
borrow the mathematics but **deliberately drop that vocabulary.** This project follows the
companion notes' principle of an *epistemic situation, not an epistemic agent* — there is no
believing subject anywhere in it. The slack is **not** what someone fails to believe; it is a
**structural** quantity: the valuation of the region excluded middle leaves undecided. In the
concrete model of §8 it is literally `μ(∂U)`, the measure of a topological **boundary** — a
fact about the space, true whether or not anyone is reasoning. So wherever the literature (or
an older comment) says "belief function" or "ignorance mass," read *non-additive valuation*
and *the measure of the undecided region.* We keep the DS name only to point at the same
mathematical object, never at a state of mind.

---

## 5. Why this is hard: the obstacles to intuitionistic probability

It is tempting to think this is just "probability, but over a Heyting algebra." The reason that
doesn't work — and the reason this is a research project rather than an exercise — is that
almost every convenience of ordinary probability is quietly powered by the law of excluded
middle. Remove it and the following break, in rough order of severity:

1. **There is no `1 − P(A)`.** The single most-used move in probability — "the probability of
   *not* `A` is one minus the probability of `A`" — is *defined* by complementation, and a
   Heyting algebra has no genuine complement. `v(not A)` becomes an **independent quantity** you
   cannot compute from `v(A)`. Odds, normalization, "probability of the complement" — every
   reflex built on `1 − p` has to be dropped or rebuilt.

2. **"Additive" splits into two different things.** Classically, *disjoint-additivity*
   (`A ⊓ B = ⊥ ⟹ v(A ⊔ B) = v(A) + v(B)`) and the *complement rule* (`v(A) + v(¬A) = 1`) are
   two faces of one coin. Constructively they come apart: disjoint-additivity **survives** (it
   follows from the modular law and the surviving fact `A ⊓ ¬A = ⊥`), but the complement rule
   **fails**. So you must always say *which* additivity you mean — a distinction that is
   invisible classically.

3. **The failure cannot be localized and patched.** The gap `slack(A) = 1 − (v(A)+v(¬A))` is
   exactly `v` of the region excluded middle leaves undecided, and it is *generic*, not
   exceptional: on a **connected** space the only elements obeying the classical complement rule
   are `⊥` and `⊤` themselves (`add_compl_eq_one_of_complemented` + the connectedness remark in
   §6). Classicality isn't a small correction to sand off; it is a special property that most
   elements simply lack.

4. **Even "certainty" is a theorem, not a definition.** In Cox's classical picture the
   fully-certain (0/1-valued) valuations are the *points* of the space, with a clean bijection.
   Constructively the certain valuations correspond to **prime** ideals/filters, and there are
   two inequivalent notions — *finitely* prime and *completely* prime (spatial) — agreeing only
   under a continuity hypothesis. So "what does a state of complete information even look like?"
   already needs the prime separation theorem to answer (`sharp_iff_point`, §6).

5. **Partitions and total probability collapse.** The law of total probability marginalizes over
   a partition, and the workhorse partition is `{A, ¬A}`. But constructively `A ⊔ ¬A ≠ ⊤`, so
   `{A, ¬A}` **is not a partition** — it does not tile the space. Marginalizing over a
   proposition and its negation therefore fails; Bayesian updating survives, but only over
   families that *genuinely* join to `⊤` (`total_prob_of_partition` vs. the `{A,¬A}` failure,
   §6).

6. **Probability mass can have nowhere to live.** The most concrete picture of probability is "a
   distribution over outcomes" — mass sitting on points. Constructively the relevant spaces
   (locales) may have **too few points, or none at all**, to carry the mass: some of it can
   escape to a "point at infinity" (our `topIndicator` example) or be irreducibly **diffuse** on
   a pointless locale. So "probability = distribution on outcomes" is recoverable only under
   finiteness or a continuity condition; in general there is an unavoidable diffuse remainder.
   Charting exactly when the mass *does* live on points is the representation problem (§6, §8).

7. **Cox's own proof does not survive the switch.** The classical Cox/Jaynes derivations lean on
   double-negation elimination and a functional equation for negation (Van Horn's axiom "R3").
   Those steps *are* excluded middle in disguise — indeed R3 holds for all valuations **iff**
   excluded middle does (`hasClassicalNegation_of_em` and its converse, §6). A constructive
   uniqueness theorem therefore cannot re-run the classical argument; it needs a genuinely new
   one. That is why `constructive_cox`, in its corrected form, must **posit** modularity rather
   than derive it (§6.4): the classical route to the sum rule is gone, and `modularity_irreducible`
   confirms modularity cannot be recovered from the disjunction data. The honest replacement is to
   *characterize* modularity as the mixing-closure of point additivity (`eq_mix_deltaPoint`, §6),
   not to re-run Cox's uniqueness proof.

The through-line: **classical probability bundles together several things that are only
separately true.** Intuitionistic probability is what you get when you unbundle them, and the
work is figuring out which pieces survive alone (modularity, disjoint-additivity, conditioning,
finite representation) and which were secretly excluded middle all along (the complement rule,
total probability over `{A,¬A}`, the clean point picture, Cox uniqueness).

---

## 6. What the Lean file actually proves

Everything across the modules is checked by the Lean proof assistant, so the ✅ items are
theorems with zero gaps (a computer verified every step). **The project is now `sorry`-free:**
the central `constructive_cox` — long the one open target — is proved, in a *corrected* statement
(§6.4). What remains is not a `sorry` but genuine mathematics stated *outside* the formal
theorems: the analytic frontier flagged as ⬜ in §6.5.

### In plain terms: which results are hard, and why

Most of the ✅ list below is careful bookkeeping. A handful of items carry the real weight — the
three foundational ones below, plus the Aczél generator (`g_additive`, the analytic heart of the
product rule, built as a dyadic limit) and the resolution of `constructive_cox` (which turned out
to be *unsatisfiable as originally stated*, and true only once modularity is posited — itself
justified by `modularity_irreducible`):

- **The hinge (`hasClassicalNegation_of_em` and its converse)** is the conceptual heart. It
  proves the complement rule `v(¬A) = 1 − v(A)` holds for *every* valuation **exactly when**
  excluded middle holds — surgically locating *all* of probability's classicality in one axiom
  (Van Horn's R3). The easy direction is a calculation; the hard direction must *manufacture* a
  counterexample wherever excluded middle fails — a valuation with genuine slack — which it does
  with a prime-ideal indicator built from the prime separation theorem. This is what upgrades
  "the complement rule looks optional" to "the complement rule *is* excluded middle."

- **The finite representation theorem (`eq_sum_mass`)** is the headline, because it says
  intuitionistic probability is not an exotic new animal: on a finite frame it *is* ordinary
  classical probability on the points, seen through the interior operator `□`. The difficulty is
  that you cannot read the "points" straight off the algebra — you recover them by peeling one
  maximal element at a time and using the modular law to show the leftover is exactly a point
  mass. The induction (and getting the `[0,∞]` truncated-subtraction arithmetic right) is the
  work.

- **The general decomposition (`tsum_mass_le`)** is what remains once you know full
  representation is *false* (the counterexample below). The honest general statement is an
  inequality: the point-masses are always a sub-probability, `∑ₚ v.mass p ≤ v ⊤`, and the
  shortfall is a diffuse remainder — a constructive analogue of the **Lebesgue decomposition**
  (atomic + diffuse), holding for *every* frame with no finiteness and no classical logic. The
  proof reuses the maximal-element peel, now over arbitrary finite subsets bounded by the whole,
  then passes to the supremum.

Everything else — conditioning, disjoint-additivity, the classical fragment, the concrete
measure model — is a direct calculation or a corollary of these.

**✅ Proved:**

- `add_compl_eq_sup` — the identity `v(A) + v(not A) = v(A or not A)` from §4.
- `add_compl_le_one` — the Dempster–Shafer inequality `v(A) + v(not A) ≤ 1`, *derived* from
  constructive logic rather than assumed.
- `slack_eq_dnGap_add_deMorganGap` (with `slack_eq_zero_iff`, `slack_eq_deMorganGap_of_regular`)
  — the **slack decomposition** from §4: `slack A = (double-negation gap) + (De Morgan gap)`,
  splitting the single DS "ignorance" number into its two independent obstructions.
- `Valuation.two_monotone` / `self_le_plausibility` / `plausibility_sub_self` (in
  [`Belief.lean`](ConstructiveProb/Belief.lean)) — **the Dempster–Shafer bridge (§4 frontier,
  now a theorem).** `v A + v B ≤ v (A ⊔ B)ᶜᶜ + v (A ⊓ B)`: read on the Booleanization (regular
  elements), where `(A ⊔ B)ᶜᶜ` is the Boolean join, this is `Bel(A∨B) + Bel(A∧B) ≥ Bel A + Bel B`
  — **2-monotonicity**, the defining convex-capacity inequality of a belief function. With the dual
  plausibility `Pl A = 1 − v Aᶜ`, the belief/plausibility interval has width exactly the slack
  (`Pl A − v A = slack A`). So `v` restricted to the regulars *is* a (2-monotone) DS belief
  function; full `∞`-monotonicity remains future work.
- `classical_additivity` — in the classical (Boolean) case, `v(A) + v(not A) = 1` exactly.
  This is the "certain limit recovers ordinary probability" claim, machine-checked.
- `exists_positive_slack` — a concrete example where the slack is genuinely **positive**
  (built on the chain `[0,∞]`). This matters: it proves the whole idea isn't vacuous. If the
  slack were secretly always `0`, constructive logic would give nothing new. It doesn't.
- `hasClassicalNegation_of_em` / `em_of_forall_hasClassicalNegation` — **both directions of
  the hinge**, so `v(¬A) = 1 − v(A)` for every valuation **⟺** excluded middle holds. This
  pinpoints exactly which Cox axiom (Van Horn's negation axiom "R3") is the one that assumes
  classical logic. The hard direction builds, wherever excluded middle fails, a valuation with
  slack (via a prime-ideal-complement indicator + the prime separation theorem).
- `sharp_iff_point` — the "fully certain" (0/1-valued) valuations are **exactly** the
  complement-indicators of prime ideals: the certain limit recovers the underlying logic and
  its points. (These are the finitely-prime points; the completely-prime/spatial ones would
  need Scott-continuity, which our `Valuation` omits.)
- `additive_of_disjoint` / `add_compl_eq_one_of_complemented` — **the classical fragment.**
  Disjoint additivity holds unconditionally; the complement rule `v(A) + v(¬A) = 1` holds
  exactly on the **complemented** elements (those with `A ∨ ¬A = ⊤`). *Correction the
  formalization forced:* this is **not** the "regular" (¬¬-stable) fragment — regular ⊋
  complemented, and an atomic valuation on a regular-but-uncomplemented element still has
  slack. On a connected locale the classical fragment can be just `{⊥, ⊤}`.
- `condVal` / `condVal_mul` / `condVal_symm` / `cond_add_compl_le` — **conditioning works.**
  The posterior `v(· | b) = v(· ⊓ b) / v b` is again a valuation, the product rule
  `v(a | b) · v b = v(a ⊓ b)` and Bayes symmetry hold — but **total probability fails over
  `{A, ¬A}`** (they don't tile `⊤`), so the conditional masses fall short of `v b` by the
  conditional slack `v b − v((A ∨ ¬A) ⊓ b)`. Bayesian updating survives; the assumption that
  `A` and `¬A` exhaust the world does not.
- `total_prob_of_partition` / `total_prob_predictive` — **prediction works over a genuine
  partition.** If `a, a'` really tile `⊤` (disjoint *and* exhaustive), then `v b = v(a⊓b) +
  v(a'⊓b) = v(b|a)·v a + v(b|a')·v a'`. The positive counterpart to the `{A,¬A}` failure:
  you may marginalise a prediction over families that actually join to `⊤`, just not over a
  proposition and its negation.
- `Measure.toValuationOpens` / `toValuationOpens_eq_interiorMeasure` — **the concrete model +
  the GMT identification (§8):** every classical probability measure `μ`, read on the open sets,
  *is* an intuitionistic-probability valuation `v U = μ U`, and this valuation *is* `P(□·)`
  restricted to the opens.
- `nonempty_coxModel` — **the Cox axioms are not vacuous:** an explicit model on the chain
  `ℝ≥0∞` (constructively, no excluded middle). This guards `constructive_cox` against the
  vacuity that an over-strong axiom would silently create.
- `eq_sum_mass` / `sum_mass` (in [`Representation.lean`](ConstructiveProb/Representation.lean))
  — **the finite representation theorem, the headline new result.** For a finite frame
  `LowerSet P`, every valuation is the point-measure of a mass function:
  `v U = ∑_{p ∈ U} v.mass p` and `∑ p, v.mass p = 1`. So every intuitionistic-probability
  valuation on a finite frame **is** a classical probability on its points — the converse of
  the GMT bridge, finite case (§8). *Scope, stated honestly:* we prove this for `LowerSet P`;
  by Birkhoff duality every finite frame is `LowerSet P` for `P` its join-irreducibles, so up
  to isomorphism this is *all* finite frames — but that isomorphism (and transport of the
  valuation across it) we cite rather than mechanize.
- `toPMF` — makes it literal: `v.mass` is a mathlib `PMF` (probability mass function), so a
  valuation on a finite frame **is** a classical discrete probability distribution on the
  points, with `v` its point-measure.
- `Valuation.mix` (in [`Basic.lean`](ConstructiveProb/Basic.lean)) / `deltaPoint` /
  `eq_mix_deltaPoint` (in [`Representation.lean`](ConstructiveProb/Representation.lean)) — **the
  mixture characterization.** Because every valuation axiom (above all modularity) is *linear* in
  the valuation, the valuations form a **convex set**: any weighted average of valuations (weights
  summing to `1`) is a valuation (`mix`). The sharp *point-valuations* `δ_p U = [p ∈ U]` are the
  pure states, and on a finite frame every valuation is their mixture,
  `v = ∑_p (v.mass p)·δ_p` (`eq_mix_deltaPoint`). So **{valuations on a finite frame} = {finite
  mixtures of points}**. *Why this matters:* it is the constructive successor to the "Cox
  uniqueness" question. Van Horn pins the sum rule down with the negation axiom R3, which
  `SumIrreducible.lean` shows is unavailable here; this identifies what replaces it — modularity is
  *exactly* the property closed under **mixing the points**, "an average of certainties", neither
  more nor less.
- `exists_valuation_not_point_representable` / `eq_tsum_mass_of_scott` (in
  [`RepresentationInfinite.lean`](ConstructiveProb/RepresentationInfinite.lean)) — **the
  boundary of the finite theorem.** On the infinite frame `LowerSet ℕ` the finite theorem
  *fails*: the indicator of `⊤` has every point-mass `0` yet `v ⊤ = 1` (the unit of mass
  escapes to a non-principal "point at infinity"), so finiteness is genuinely necessary.
  Conversely, adding **Scott-continuity** recovers it (`v ⊤ = ∑' n, v.mass n`). Together: *on
  `ℕ`, a valuation is point-representable iff it is Scott-continuous.*
- `tsum_mass_le` / `tsum_mass_le_one` (in
  [`RepresentationGeneral.lean`](ConstructiveProb/RepresentationGeneral.lean)) — **the general
  structural theorem.** For an *arbitrary* frame `LowerSet P` (no finiteness, no Scott-continuity)
  the point-masses always sum to *at most* the total: `∑' p, v.mass p ≤ v ⊤ ≤ 1`. So every
  localic valuation splits into an **atomic part** (the point-masses, always a sub-probability)
  and a **diffuse part** `v ⊤ − ∑' p, v.mass p ≥ 0` — a constructive Lebesgue-style
  decomposition. The equality cases (finite; `ℕ` + Scott) are "purely atomic" (`IsPurelyAtomic`,
  zero diffuse part); the `topIndicator` counterexample is the extreme purely-diffuse opposite.
  The proof peels a maximal point from each finite subset and uses modularity — it needs neither
  excluded middle nor `Classical`.
- `Valuation.eq_sum_mass_of_finite` / `Valuation.isPurelyAtomic_of_scott` (in
  [`RepresentationGeneral.lean`](ConstructiveProb/RepresentationGeneral.lean)) — **Scott-continuity
  ⟹ purely atomic, in general.** `eq_sum_mass_of_finite` upgrades the finite representation to hold
  on any *single* finite lower set (dropping `[Fintype P]`), so it applies to the finite pieces of
  an infinite frame. Building on it, `isPurelyAtomic_of_scott` shows that on **any locally-finite-
  below poset** `P` (every `↓p` finite), a **Scott-continuous** valuation has zero diffuse part:
  `∑' p, v.mass p = v ⊤`. This generalizes the "`ℕ` + Scott" equality case above from the chain
  `ℕ` to arbitrary posets — the diffuse mass can only escape "to infinity" when the whole is *not*
  approached by its finite pieces, which Scott-continuity forbids. (The *full* M3c — representing
  the diffuse part for non-spatial / non-Scott frames — stays open; see §6.5.)

**✅ Proved — the Cox derivation (this is §6.4, the former open goal):**

- `constructive_cox` — **the central theorem, corrected and proved** (§6.4). Every Cox model
  regraduates to a modular `Valuation`. Discharging it forced two corrections to the original
  bare statement, both mathematically informative: (1) it was literally *unsatisfiable* — it
  asked for a `StrictMono g : ℝ → ℝ≥0∞` with `g 0 = 0`, but strict monotonicity forces
  `g(−1) < g 0 = 0`, impossible in `ℝ≥0∞`; so `StrictMono g` becomes `StrictMonoOn g (Icc 0 1)`
  (the plausibility values live in `[0,1]`); (2) **modularity of the unconditional plausibility
  is an explicit hypothesis**, because the sum rule is irreducible (see `modularity_irreducible`
  and §6.5) — the product rule cannot supply it. With these it is proved, `g = ENNReal.ofReal`.
- `constructive_cox_nonvacuous` / `coxModelENNReal_modular` — the corrected theorem is **not
  vacuous**: its modularity hypothesis is met by the genuinely non-Boolean witness on `ℝ≥0∞`
  (automatic there, since a chain makes every monotone plausibility modular).
- `constructive_cox_of_modular` / `ModularCoxModel.classical_of_boolean` (`Cox.lean`) — the
  clean reduction: a `ModularCoxModel` (product rule + modular sum rule, **no** negation axiom)
  *is* a `Valuation`, and on a Boolean algebra it is automatically complement-additive
  (recovering Van Horn's classical Cox). The split is exact: the **product-rule half is
  logic-independent** (Aczél, below) and the **sum-rule half is where the logic lives**
  (modularity replaces R3).

**✅ Proved — the product-rule half (Aczél/Hölder generator, [`Aczel.lean`](ConstructiveProb/Aczel.lean)):**

This is the constructive content of Aczél's associativity theorem, built from scratch (mathlib
has no ordered-semigroup embedding for interval operations). A `Scale` bundles Aczél's
hypotheses on a combination functional `F` — divisible, associative, positive-cone
(`x < F x c`), jointly continuous, order-preserving, with an identity at `−∞`. The generator is
constructed directly as a dyadic limit `g b = ⨆ₙ (count of `n`-th roots under `b`)/2ⁿ`.

- `g_additive` — **the analytic heart:** the generator turns the combination into addition,
  `g (F x y) = g x + g y`, obtained as the limit of *approximate* additivity (a counting
  sandwich `dcount x n + dcount y n + 1 ≤ dcount (F x y) n ≤ ⋯ + 3`, with the `2⁻ⁿ` slack
  vanishing). `g_unit` (`g u = 1`) and `g_mono` normalize and order it.
- `g_strictMono_cone` — **the order embedding:** `u ≤ x < y ⟹ g x < g y`, proved *without*
  continuity, via the roots shrinking to the identity (`roots_shrink`) plus a count-amplification
  argument.
- `exists_ordered_generator` / `exists_mul_generator` — **Hölder's theorem on the cone:** every
  `Scale` carries a normalized, strictly monotone, additive generator, and (by `exp`) a strictly
  monotone *multiplicative* one `G (F x y) = G x · G y` — the exact shape of `AczelStatement`'s
  conclusion.
- `aczelStatement_cone` — **the bridge (M4):** `AczelStatement`'s conclusion delivered on the
  cone, `StrictMonoOn` and multiplicative. It is *minus continuity* — the constructed `g` is
  discontinuous at the unit — and *minus reorientation* to `[0,1]`; those are the analytic
  frontier (§6.5).
- `Scale.exists_bounded_mul_generator` — **the reorientation half of M4, closed.** The cone
  generator above runs *upward* (`G = exp∘g` increasing), matching the growing `t`-conorm picture;
  Cox's conjunction lives in the bounded `[0,1]` picture where combining makes things *less*
  plausible. The single order-reversing regraduation `Ḡ = exp(−g)` bridges them: it is a strictly
  **decreasing** multiplicative generator into `(0,1]`, `Ḡ(F x y) = Ḡ x · Ḡ y`, `Ḡ u = e⁻¹` — the
  bounded/Cox orientation of `AczelStatement`. No further analysis; it is pure regraduation. (The
  *other* half of the M4 gap — continuity of `g` and its extension below the unit — is genuine
  analysis and remains open, §6.5.)
- `nonempty_scale` / `logSumExpScale` — the whole `Scale` edifice is quantified over `∀ S`, so
  it needs a witness: `F x y = log(eˣ + eʸ)` (unit `0`, additive generator `exp`) satisfies every
  axiom. This guards the Aczél capstones against vacuity, as `nonempty_coxModel` does the Cox side.
- `hasOrderedGenerator_logSumExp` — **the open analytic core is witnessed, globally and
  continuously.** The one part left open in the forward direction is the *existence* of an
  order-embedding additive generator (Hölder), and the constructed `g` is discontinuous at the
  unit. For the archetype these both vanish: the generator `exp` works on **all** of `ℝ`, is
  continuous and strictly monotone, with `exp(F x y) = exp x + exp y`. So the open core is inhabited
  by a continuous global generator — guarding the *conclusion* the way `nonempty_scale` guards the
  hypotheses; only the general existence (for an arbitrary `Scale`) remains open.

**✅ Proved — the sum rule is irreducible (M5, [`SumIrreducible.lean`](ConstructiveProb/SumIrreducible.lean)):**

- `modularity_irreducible` — justifies *why* `constructive_cox` must posit modularity. On the
  five-element frame of lower sets of the "V" poset (a bottom below two incomparable points),
  there is a monotone, normalized plausibility that is **additive on disjoint joins yet not
  modular**. So modularity is not derivable from the disjunction/sum data and must be posited —
  the irreducible constructive replacement for the sum-rule half of R3.
- `no_disjunction_functional` — the **sharp** form: `q (x ⊔ y)` is not even a function of the
  marginals `q x, q y`. The pairs `(↓a, ↓a)` and `(↓a, ↓b)` have identical marginals `(½, ½)`
  but joins `↓a` and `⊤` valued `½` and `1`. Unlike the conjunction (which reduces to Aczél via
  conditioning), a disjunction on a Heyting frame — lacking complements to decompose a join — is
  genuinely not a functional of its marginals.

**✅ Proved — the computability guard ([`Halting.lean`](ConstructiveProb/Halting.lean)):**

- `exists_halting_slack` / `haltingValuation_not_classical` — the **non-collapse guard**. A
  semi-decidable ("machine halts") proposition is an *open* in the Sierpiński topology; on the
  Sierpiński frame it cannot be refuted (`hᶜ = ⊥`), so assigning it a halting probability
  `p ∈ (0,1)` (morally Chaitin's `Ω`) gives positive slack `1 − p` and violates
  `v a + v aᶜ = 1`. Any axiom set strong enough to collapse the theory to classical logic is
  refuted by this model — *because computability forbids `p ∈ {0,1}`*. This does for the sum
  rule what `nonempty_coxModel` does for the product rule: it certifies the theory stays
  genuinely non-classical. `chainValuation` (every monotone normalized map on a complete chain
  is a valuation) generalizes the earlier `chainVal`.

**⬜ Open (the analytic frontier — stated maths, not `sorry`s):**

- **Continuity + off-cone extension of the generator.** `aczelStatement_cone` proves the
  product rule on the cone `[u,∞)`; matching the *verbatim* `AczelStatement` on `[0,1]` needs two
  more things. *(i) Reorientation — **done.*** `Scale.exists_bounded_mul_generator` supplies the
  bounded `[0,1]` orientation via `Ḡ = exp(−g)` (decreasing, multiplicative, into `(0,1]`); this
  was pure regraduation, not analysis. *(ii) Continuity + off-cone extension — **still open.*** The
  constructed `g` is discontinuous at the unit (it is `0` below `u`), so a continuous generator
  requires extending it below the unit by group completion, then proving continuity. This is
  genuine analysis, multi-session. It *is* clean for the archetype
  (`hasOrderedGenerator_logSumExp`: `exp` is a continuous global generator for `logSumExpScale`),
  which witnesses the target; the general case remains.
- **Full representation in general (`M3c`).** `tsum_mass_le` gives the atomic part as a
  sub-probability for every frame; representing the *diffuse* remainder (equality) is the
  paper-defining open problem. *Progress:* `isPurelyAtomic_of_scott` now closes the
  **Scott-continuous case in general** (any locally-finite-below poset, not just the chain `ℕ`) —
  under Scott-continuity the diffuse part is `0`. What remains is precisely the genuinely diffuse
  regime: representing the remainder for **non-spatial / non-Scott** frames — and, strikingly, the
  non-spatiality obstruction is the *same phenomenon* as undecidability (a halting locale has too
  few points), tying this frontier to the computability guard above.

### Relation to prior formalizations — exactly what overlaps

To be scrupulous about novelty (a reviewer will be): the **base object is prior art, including in
formalized form**, but the development built on it is not. Precisely:

- **What coincides.** The modular valuation on a frame/locale is a known object — on paper
  (Coquand–Spitters, *Integrals and Valuations*, 2009; Vickers, *Topology via Logic*) and
  **formalized in Coq/HoTT** by Bidlingmaier–Faissole–Spitters (*Synthetic topology in HoTT for
  probabilistic programming*, MSCS 2021; the `FFaissole/Valuations` library, `Valuations.v`). Our
  `Valuation` is essentially that object, so the *definition* is not new.
- **How ours differs even at the object level.** (i) Their valuations are **Scott-continuous**
  (ω-cpo-valued, for domain-theoretic fixpoint semantics); we **deliberately omit** Scott-continuity
  — precisely what makes the non-representable valuations (`topIndicator`) and the atomic/diffuse gap
  visible. (ii) They treat a valuation as the constructive analogue of a **measure** (their goal is
  Riesz/Fubini, the Lebesgue valuation, and a Giry-style monad for probabilistic programming); we
  read the *same* object as **credence obtained by weakening the underlying logic**.
- **What is *not* formalized anywhere (the actual contribution).** The reading of the slack as the
  failure of excluded middle and its two-gap decomposition; the R3 hinge (additivity ⟺ EM); the
  constructive Cox theorem and the from-scratch Aczél/Hölder generator; the representation, mixture,
  and Scott-⟹-atomic theorems in the forms here; the halting/decidability guard; and the
  Dempster–Shafer belief-function bridge. None of this is in the Coq/HoTT valuations line of work.
- **Adjacent but a different object.** The **ALEA** Coq library (a Giry-style distribution monad for
  randomized programs) and **Sargsyan**'s cubical-Agda development (Markov categories, conditioning,
  d-separation) are constructive probability in a proof assistant, but formalize *additive*
  distributions, not localic non-additive valuations — no overlap with the specific object here.

So the accurate one-liner is: *the valuation object is prior-formalized (Coq/HoTT), for constructive
measure theory; the logic-driven non-additive theory on top of it is formalized here for the first
time.* **Not** "most of this is already done in Coq/Agda/HoTT." (Detailed map: [`RELATED_WORK.md`](RELATED_WORK.md).)

---

## 7. Why bother?

Five payoffs, roughly concrete to speculative — two of them (the computability ones, 3–4) are
outright theorems in this repository, not just motivations:

1. **It sharpens the link between two theories.** Ordinary (Kolmogorov) probability and
   Dempster–Shafer belief functions are usually built as separate constructions. That they are
   deeply related is *already known* — a theorem of Paris (1994), building on Shafer (1976),
   identifies non-classical probabilities of this kind with belief functions. The angle here
   is to locate the difference in the underlying **logic** (Boolean vs. Heyting), with the
   non-additivity ⟺ the failure of excluded middle, and to make that precise and machine-checked
   rather than to claim the connection as new. (See [`RELATED_WORK.md`](RELATED_WORK.md).)

2. **It reframes an old theorem.** Cox derived probability from classical logic. Swapping the
   boundary condition to constructive logic is a clean, under-explored variation, and there's
   a precedent that "the logic fixes the shape of probability" can be made into a real
   theorem — that's essentially what **Gleason's theorem** does for quantum logic.

3. **It turns decidability into something probability can measure.** The framework makes "the
   proposition `a` is decided" and "the probability of `a` behaves classically" the *same*
   condition: `v a + v aᶜ = 1` holds for every valuation exactly when `a ⊔ aᶜ = ⊤`, i.e. exactly
   when excluded middle holds at `a` (the R3-hinge equivalence, proved:
   `hasClassicalNegation_of_em` / `em_of_forall_hasClassicalNegation`). So the slack
   `1 − v a − v aᶜ` is a *quantitative measure of how undecided `a` is* — zero for decidable
   propositions, positive otherwise — and studying it is a way to study decidability itself
   through a probabilistic lens. The same phenomenon reappears one level up: whether a valuation
   is representable as a point-measure coincides with whether its locale is spatial (has "enough
   decided points"), the spatiality ⟺ decidability duality of §6.5.

4. **It proves classical probability is *not* appropriate for some real propositions.** This is
   a theorem, not a preference. Take a semi-decidable proposition — canonically "machine `n`
   halts" — which is an *open* in the observational (Sierpiński) topology and can be confirmed by
   a finite computation but never refuted by one. The natural valuation on it
   (`haltingValuation`) assigns it a genuine probability `p ∈ (0,1)` — morally Chaitin's `Ω`, an
   uncomputable, algorithmically random real — and `haltingValuation_not_classical` **proves**
   that this valuation *violates* the Kolmogorov complement rule `v a + v aᶜ = 1`. So for
   propositions grounded in computation, the classical assumption that a statement and its
   negation partition certainty is provably false; the constructive slack is *forced, not
   optional*. Any calculus insisting on the classical rule is refuted by this model — which is
   precisely why the halting valuation doubles as the theory's non-collapse guard (§6.5).

5. **It fits a philosophical picture.** If you think the world is fundamentally *structure*
   (and that "points"/"objects" are derived, not primitive), then the natural mathematics is
   locale theory — whose logic is constructive. So this isn't an arbitrary change; it's the
   probability theory that matches that worldview. (See `../probability_philosophy_handoff.md`.)

---

## 8. The concrete picture: probability measures on open sets

Everything above is abstract — valuations on an arbitrary frame. Here is a concrete source of
them that also explains, in one stroke, why the slack has nothing to do with belief.

**The setup.** There's a classical bridge, the **Gödel–McKinsey–Tarski translation**, between
intuitionistic logic and a modal logic (S4) with a "necessarily" operator `□`. Semantically,
`□` is the **interior** operator, and the intuitionistic propositions are exactly the **open
sets** of a space. (This is the same reason `Opens X` was our running example of a Heyting
algebra.)

**The bridge.** Take an ordinary space `X` — say the real line — and an ordinary, fully
classical probability measure `μ` on it (the kind you already know: `μ` of an interval, total
mass 1, additive). Now *look at `μ` only on the open sets.* The claim, now machine-checked as
`Measure.toValuationOpens`, is:

> A classical probability measure, restricted to the open sets, **is** an intuitionistic
> probability valuation: `v(U) = μ(U)`.

Reading `μ(U)` through the translation, it is `P(□U)` — "the probability of landing in the
region where `U` *verifiably* holds" (its interior). No new axioms: modularity is just the
inclusion–exclusion rule every measure already satisfies.

**Where the slack goes — and why it isn't belief.** The constructive negation of an open set
`U` is not the plain complement (that usually isn't open); it's the *interior* of the
complement, `int(Uᶜ)` — the largest open set disjoint from `U`. So

```
v(U) + v(not U) = μ(U) + μ(int(Uᶜ)),
```

and these two open pieces don't fill up `X`: what's missing is the **boundary** `∂U` (e.g. for
`U = (−∞, 0)`, the missing point is `0`). Hence

```
slack(U) = μ(∂U) — the measure of the topological boundary.
```

That is the whole point of the earlier "note on belief." The slack is not anyone's ignorance
or hesitation; it is the **μ-measure of a boundary** — a piece of geometry. If `μ` puts mass
on the boundary (e.g. an atom at `0`), there is slack; if not, there isn't. Either way it is a
fact about the space and the measure, with no reasoner in sight.

**What's proved, and what's still open.** Define `P(□·)` on *every* set by
`interiorMeasure S = μ(interior S)` (this is the object Dempster–Shafer names a "belief
function" and reads epistemically — Ruspini, Smets, Pearl; we keep only the structural content
and the name as a pointer). Then `toValuationOpens_eq_interiorMeasure` proves the **concrete
direction** of the identification: on the open (= intuitionistic) propositions, our valuation
*is* `P(□·)`. So the Heyting valuation from a measure is exactly `P(□·)` restricted to the opens
— machine-checked.

The **representation direction** — does *every* localic valuation arise this way, from some
classical measure via `□`? — is **proved in the finite case** (`eq_sum_mass`/`sum_mass`, §6); its
**boundary is pinned down** (`RepresentationInfinite.lean`): on the infinite chain `LowerSet ℕ`
it *fails* for a non-Scott-continuous valuation (the indicator of `⊤`, whose mass escapes to a
non-principal point at infinity) and *holds* once Scott-continuity is assumed, confirming
"representable ⟺ Scott-continuous" for the chain. This **Scott-continuous case is now proved in
general** (`isPurelyAtomic_of_scott`, `RepresentationGeneral.lean`): on *any* locally-finite-below
poset, a Scott-continuous valuation is purely atomic — so the point picture is exact wherever the
whole is genuinely approached by its finite pieces. And the **general upper bound is proved**
for *any* frame (`tsum_mass_le`): the atomic part is always a
sub-probability, `∑' p, v.mass p ≤ v ⊤`, so a valuation splits into atomic + diffuse parts with
the diffuse part `≥ 0` everywhere — the "≤" half of representation, holding unconditionally.

What **remains open** is the matching *equality* in the genuinely diffuse (non-Scott / non-spatial)
regime — i.e. representing the diffuse part. It is genuinely subtle: for a non-spatial locale (one
with too few points — e.g. a measure algebra) there is no point-mass to carry it, so any
representation must live on a
*measure space* into which the locale embeds, not on its points. Resolving it would mean
importing localic/constructive measure theory (the localic Riesz representation of
Coquand–Spitters and Vickers) with Scott-continuity plus a regularity/`τ`-smoothness condition —
a genuinely new (and paper-defining) theorem. See [`RELATED_WORK.md`](RELATED_WORK.md).

---

## 9. Open problems and future directions

Consolidated here for reference; each is discussed in context where it arises. Two tiers: the
**formal frontier** (what a next Lean push would target) and the **conceptual program** (what the
companion philosophy paper opens).

### The formal frontier (Lean / mathlib)

1. **Continuity + off-cone extension of the Aczél generator** → the verbatim `AczelStatement` on
   `[0,1]`. `aczelStatement_cone` and `exists_bounded_mul_generator` give the multiplicative
   generator, in the bounded Cox orientation, *on the positive cone*. What remains is a **continuous**
   generator on all of `[0,1]`, which requires the group completion below the unit — and that in turn
   requires commutativity of `F` for *off-cone* elements, which is **not** among the `Scale` axioms
   and is essentially equivalent to the theorem. Genuine analysis; clean for the archetype
   (`hasOrderedGenerator_logSumExp`), open in general. (§6.5.)
2. **Full representation in general — M3c.** `tsum_mass_le` gives the atomic part as a sub-probability
   for every frame, and `isPurelyAtomic_of_scott` closes the Scott-continuous case on any
   locally-finite-below poset. What remains is representing the **diffuse** remainder for
   **non-spatial / non-Scott** frames — the paper-defining problem. It needs localic/constructive
   measure theory (Coquand–Spitters, Vickers) ported to Lean, plus Scott-continuity and a
   regularity/`τ`-smoothness condition. Strikingly, the non-spatiality obstruction is the *same
   phenomenon* as undecidability (too few decided points), tying this to the halting guard. (§6.5, §8.)
3. **∞-monotonicity of the Dempster–Shafer bridge.** `two_monotone` proves `v` is a **2-monotone**
   capacity on the Booleanization (the convex-capacity hallmark). A *bona fide* belief function is
   **∞-monotone** (non-negative Möbius transform) — a whole tower of inequalities. Upgrading the
   2-monotone case to the full tower is future work. (§4; Thread G of [`RELATED_WORK.md`](RELATED_WORK.md).)
4. **A genuine uniqueness theorem.** `constructive_cox` is a *regraduation* theorem that **posits**
   modularity, and `modularity_irreducible` shows modularity cannot be derived from the disjunction
   data; the honest stand-in is the mixture characterization (`eq_mix_deltaPoint`). Open: derive
   modularity — and so pin down the calculus — from a more primitive desideratum, given
   `no_disjunction_functional` tells you where *not* to look. (§4, §6.4.)

### The conceptual / philosophical program

Beyond the formal development, the companion philosophy paper plan
([`../PAPER-PHIL-foundations.md`](../PAPER-PHIL-foundations.md)) opens a wider program, held there as
*horizon* rather than result: the **iterated-limit hierarchy** (classical logic ← classical
probability ← quantum probability), the **Principal Principle** interface between chance levels,
**prior uniqueness** (when the structure of an epistemic situation fixes the prior — the Bertrand /
Jeffreys worry), **emergent probability** (macro from micro), a structural reply to **Feyerabend**,
an **information-theoretic** (bits / Shannon) grounding of the limit behaviour, and the
**law-likeness fork** (brute regularity vs. a simplicity-weighted Solomonoff ensemble). These are
program-level, not next-commit-level.

**The unifying thread** across both tiers: *non-spatiality = undecidability = the failure of
point-representability* — one phenomenon seen three ways, as geometry (§8), as computability
(`Halting.lean`), and as representation theory (§6). Progress on any one sharpens the others.

---

## 10. Glossary

Terms as they are used in this project (not always in their fullest generality). Sections in
parentheses point to where the term earns its keep.

- **Atom / atomic part.** A *point mass*: `v.mass p = v(↓p) − v(↓p without p)`, the weight
  concentrated exactly at a point `p`. The **atomic part** of a valuation is the sum of all its
  point masses, `∑ₚ v.mass p`. (§6.) See **diffuse part**.
- **Birkhoff duality.** Every finite distributive lattice (in particular a finite frame) is the
  lattice of **lower sets** of its **join-irreducible** elements. This is what lets "valuation on
  a finite frame" be studied as "valuation on `LowerSet P`." (§6.)
- **Boolean algebra.** The algebra of classical logic: `and`, `or`, and a genuine complement
  `not`, with `A ∨ ¬A = ⊤` (excluded middle). The certain-limit target of *ordinary* Cox
  probability. (§3.)
- **Complemented element.** An `A` with a genuine complement inside the frame (`A ∨ ¬A = ⊤` and
  `A ∧ ¬A = ⊥`). Exactly the elements on which the classical rule `v(A) + v(¬A) = 1` holds —
  strictly fewer than the **regular** elements. (§6.)
- **Constructive / intuitionistic logic.** Logic in which asserting a statement requires
  constructing evidence; `A ∨ ¬A` is not assumed. Its algebra is a **Heyting algebra**. (§2.)
- **Cox's theorem.** The classical result that a consistent calculus of degrees of certainty
  agreeing with *classical* logic in the certain limit must be (a rescaling of) probability. The
  target re-derived over constructive logic by `constructive_cox` — **proved** in a corrected form
  that *posits* modularity (the sum rule) rather than deriving it (§6.4). (§1, §6.)
- **Dempster–Shafer belief function.** A known non-additive generalization of probability with
  `Bel(A) + Bel(¬A) ≤ 1`. Paris's theorem identifies the valuations here with these; we borrow
  the object but drop the epistemic "belief" reading. (§4.)
- **Diffuse part.** The remainder `v ⊤ − ∑ₚ v.mass p ≥ 0` left after the atomic part —
  probability mass carried by no point. Zero exactly when the valuation is **purely atomic**.
  (§6.)
- **Excluded middle (LEM).** The classical law `A ∨ ¬A = ⊤`. Its presence or absence is the
  single dial this whole project turns. (§2, §5.)
- **Frame / locale.** A complete Heyting algebra: `and`, arbitrary `or`, and the resulting
  `not` — concretely the algebra of **open sets** of a space. "Locale" is the same object viewed
  as "a space possibly without enough points." Lean: `Order.Frame`. (§3.)
- **GMT (Gödel–McKinsey–Tarski) translation.** The classical embedding of intuitionistic logic
  into the modal logic S4, sending intuitionistic truth to `□` ("necessarily"). Semantically `□`
  is the **interior** operator, which is why open sets model constructive logic. (§8.)
- **Heyting algebra.** The algebra of constructive logic: like a Boolean algebra but with a
  weaker negation and no excluded middle. (§3.)
- **Interior operator `□`.** Sends a set to its largest open subset; models "verifiably true."
  The intuitionistic negation of an open `U` is `int(Uᶜ)`. (§8.)
- **Join-irreducible.** An element that is not a join of strictly smaller ones — a "point" of a
  finite frame. The `P` in `LowerSet P`. (§6.)
- **Lower set (`LowerSet P`).** A downward-closed subset of a poset `P`, ordered by inclusion;
  with `⊔ = ∪`, `⊓ = ∩`, `⊤ = P` it is a frame. Our concrete arena for representation theorems.
  (§6.)
- **Mixture / convex combination.** A weighted average `∑ᵢ wᵢ · vᵢ` of valuations, weights
  `wᵢ ≥ 0` summing to `1` (`Valuation.mix`). Because every valuation axiom is *linear* in `v`, a
  mixture of valuations is a valuation. On a finite frame every valuation is a mixture of
  **point-valuations** (`eq_mix_deltaPoint`) — the characterization "modularity = the
  mixing-closure of point additivity." (§6.)
- **Modular law.** `v(A) + v(B) = v(A ∨ B) + v(A ∧ B)` — inclusion–exclusion. The one form of
  additivity needing no complement, and the defining axiom of a **valuation** here. (§4.)
- **Point of a locale; spatial vs. non-spatial.** A point is a completely-prime filter — "a way
  of being an outcome." A locale is **spatial** if it has enough points to be a genuine
  topological space, **non-spatial** if not (e.g. a measure algebra). Diffuse mass on a
  non-spatial locale has no point to sit on. (§8.)
- **Point-valuation (`δ_p`).** The sharp `{0,1}`-valued valuation `δ_p U = [p ∈ U]` concentrated
  at a join-irreducible point `p` (`deltaPoint`): certain of exactly the propositions containing
  `p`. The "pure states" of which every finite-frame valuation is a **mixture**
  (`eq_mix_deltaPoint`). The point-mass counterpart of a **point of a locale**. (§6.)
- **PMF.** mathlib's `PMF` — a genuine classical discrete probability distribution. `toPMF`
  turns a finite valuation into one. (§6.)
- **Prime ideal / prime filter.** The order-theoretic stand-ins for "points" that make sense
  even without excluded middle; the 0/1-valued valuations are their indicators. (§6.)
- **Regular element (¬¬-stable).** An `A` with `¬¬A = A`. Every complemented element is regular
  but not conversely — a distinction the formalization forced open (an atomic valuation can have
  slack on a regular-but-uncomplemented element). (§6.)
- **Representation theorem.** A theorem writing a valuation as `∑ₚ (point mass at p)` —
  recovering the classical distribution behind it. Proved for finite frames; holds under
  Scott-continuity on any locally-finite-below poset (`isPurelyAtomic_of_scott`); only an
  inequality (`tsum_mass_le`) in full generality. (§6.)
- **Scott-continuity.** Compatibility with directed suprema: `v(⨆ᵢ Aᵢ) = ⨆ᵢ v(Aᵢ)` for directed
  families. The extra hypothesis that pins down where the mass lives; our bare `Valuation` omits
  it deliberately. (§6.)
- **Slack.** `slack(A) = 1 − (v(A) + v(¬A)) ≥ 0`, the valuation of the undecided region. Zero
  iff `A` is complemented; in the measure model it is `μ(∂A)`, the mass of the boundary. (§4, §8.)
- **Valuation.** The central object: `v : Frame → [0,∞]` that is monotone, `v ⊥ = 0`, `v ⊤ = 1`,
  and **modular** — *not* assumed to satisfy the complement rule. (mathlib's `Valuation` is
  unrelated: it means valued-field valuations.) (§4.)

---

## 11. Building and reading it

**Prerequisites:** [`elan`](https://leanprover-community.github.io/get_started.html) (the Lean
version manager). The project pins Lean `v4.31.0` and mathlib `v4.31.0` automatically.

```bash
# from this directory:
lake exe cache get      # download prebuilt mathlib (once) — avoids an hours-long compile
lake build              # check every proof
```

A successful build is **clean — no `sorry`, no warnings.** Every declaration, including
`constructive_cox`, is fully checked; the landmark theorems depend only on the three standard
mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`), which `#print axioms` confirms.

**To read it interactively:** open this folder in **VS Code** with the `leanprover.lean4`
extension. Put your cursor inside any proof and open the Infoview (the ∀ icon) to watch the
goal state evolve step by step — the best way to *see* what a proof is doing.

**Suggested reading order in [`Basic.lean`](ConstructiveProb/Basic.lean):**
1. the top-of-file comment (the thesis + the honest caveats about Cox),
2. the `Valuation` structure (§4 here),
3. `add_compl_le_one` and `classical_additivity` (the proved core),
4. `exists_positive_slack` (the "it's not vacuous" example),
5. the open-problem section (where the research is),
6. then, for the representation story, [`Representation.lean`](ConstructiveProb/Representation.lean)
   (finite) → [`RepresentationInfinite.lean`](ConstructiveProb/RepresentationInfinite.lean)
   (its boundary) → [`RepresentationGeneral.lean`](ConstructiveProb/RepresentationGeneral.lean)
   (the general atomic/diffuse decomposition).

---

## 12. A few references

- Cox, R. T. (1946). *Probability, frequency and reasonable expectation.*
- Halpern, J. (1999). *A counterexample to theorems of Cox and Fine* — why "unique" needs care.
- Jaynes, E. T. (2003). *Probability Theory: The Logic of Science.*
- Shafer, G. (1976). *A Mathematical Theory of Evidence* (Dempster–Shafer belief functions).
- Vickers, S. (1989). *Topology via Logic* (locales / frames = the algebra of constructive logic).
- The companion philosophy notes: [`../probability_philosophy_handoff.md`](../probability_philosophy_handoff.md).
