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

The slogan is: ordinary (true/false) logic is what you use when you have *complete*
information; probability is what you use when you have *partial* information. And crucially,
if your uncertainty shrinks to zero, probability should turn back into ordinary logic — a
probability of `1` means "true," `0` means "false," and the rules of probability should
collapse into the rules of logic.

Cox's theorem (1946) made this precise: if you want a calculus of "degrees of certainty"
that (a) agrees with logic in the certain limit and (b) is internally consistent, you are
essentially forced into the usual rules of probability. (The word "forced" needs
qualification — see the note at the top of `Basic.lean` — but that's the spirit.)

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
development of it, and (ii) an attempt at a *uniqueness* theorem for it (see §5, §6, and
[`RELATED_WORK.md`](RELATED_WORK.md)).

### A note on the word "belief"

Dempster–Shafer calls its objects *belief functions* and calls the slack *ignorance*; the
modal reading in §7 even writes `Bel(A) = P(□A)`, "the probability of *believing* `A`". We
borrow the mathematics but **deliberately drop that vocabulary.** This project follows the
companion notes' principle of an *epistemic situation, not an epistemic agent* — there is no
believing subject anywhere in it. The slack is **not** what someone fails to believe; it is a
**structural** quantity: the valuation of the region excluded middle leaves undecided. In the
concrete model of §7 it is literally `μ(∂U)`, the measure of a topological **boundary** — a
fact about the space, true whether or not anyone is reasoning. So wherever the literature (or
an older comment) says "belief function" or "ignorance mass," read *non-additive valuation*
and *the measure of the undecided region.* We keep the DS name only to point at the same
mathematical object, never at a state of mind.

---

## 5. What the Lean file actually proves

Everything in [`Basic.lean`](ConstructiveProb/Basic.lean) is checked by the Lean proof
assistant, so the ✅ items are theorems with zero gaps (a computer verified every step). The
⬜ items are stated but not yet proved (`sorry`) — they're the open research targets.

**✅ Proved:**

- `add_compl_eq_sup` — the identity `v(A) + v(not A) = v(A or not A)` from §4.
- `add_compl_le_one` — the Dempster–Shafer inequality `v(A) + v(not A) ≤ 1`, *derived* from
  constructive logic rather than assumed.
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
  the GMT identification (§7):** every classical probability measure `μ`, read on the open sets,
  *is* an intuitionistic-probability valuation `v U = μ U`, and this valuation *is* `P(□·)`
  restricted to the opens.
- `nonempty_coxModel` — **the Cox axioms are not vacuous:** an explicit model on the chain
  `ℝ≥0∞` (constructively, no excluded middle). This guards `constructive_cox` against the
  vacuity that an over-strong axiom would silently create.

**⬜ Open (the research program):**

- `constructive_cox` — **the central goal.** A constructive analogue of Cox's theorem: that
  the valuations above are the *unique* reasonable calculus (up to rescaling) with a
  constructive-logic limit — obtained by *dropping R3*. Genuinely open even on paper: existing
  Cox proofs use double-negation elimination, so this needs a new argument, not a port. This
  is now the **only** remaining `sorry` in the file.

---

## 6. Why bother?

Three payoffs, from concrete to speculative:

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

3. **It fits a philosophical picture.** If you think the world is fundamentally *structure*
   (and that "points"/"objects" are derived, not primitive), then the natural mathematics is
   locale theory — whose logic is constructive. So this isn't an arbitrary change; it's the
   probability theory that matches that worldview. (See `../probability_philosophy_handoff.md`.)

---

## 7. The concrete picture: probability measures on open sets

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
— machine-checked. What remains open is the **representation direction**: does *every* localic
valuation arise this way, from some classical measure via `□`? No source pins that down; that
half would be genuinely new. See [`RELATED_WORK.md`](RELATED_WORK.md).

---

## 8. Building and reading it

**Prerequisites:** [`elan`](https://leanprover-community.github.io/get_started.html) (the Lean
version manager). The project pins Lean `v4.31.0` and mathlib `v4.31.0` automatically.

```bash
# from this directory:
lake exe cache get      # download prebuilt mathlib (once) — avoids an hours-long compile
lake build              # check every proof
```

A successful build prints exactly one warning of the form `declaration uses 'sorry'` — the
single open target `constructive_cox` in §5, and it is expected.

**To read it interactively:** open this folder in **VS Code** with the `leanprover.lean4`
extension. Put your cursor inside any proof and open the Infoview (the ∀ icon) to watch the
goal state evolve step by step — the best way to *see* what a proof is doing.

**Suggested reading order in [`Basic.lean`](ConstructiveProb/Basic.lean):**
1. the top-of-file comment (the thesis + the honest caveats about Cox),
2. the `Valuation` structure (§4 here),
3. `add_compl_le_one` and `classical_additivity` (the proved core),
4. `exists_positive_slack` (the "it's not vacuous" example),
5. the open-problem section (where the research is).

---

## 9. A few references

- Cox, R. T. (1946). *Probability, frequency and reasonable expectation.*
- Halpern, J. (1999). *A counterexample to theorems of Cox and Fine* — why "unique" needs care.
- Jaynes, E. T. (2003). *Probability Theory: The Logic of Science.*
- Shafer, G. (1976). *A Mathematical Theory of Evidence* (Dempster–Shafer belief functions).
- Vickers, S. (1989). *Topology via Logic* (locales / frames = the algebra of constructive logic).
- The companion philosophy notes: [`../probability_philosophy_handoff.md`](../probability_philosophy_handoff.md).
