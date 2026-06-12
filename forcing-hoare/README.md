# A Forcing-Style Semantics for Step-Indexed Hoare Logic

## What is this, in plain terms?

Suppose you write a computer program and want to be sure it behaves
correctly — that whenever the input satisfies some condition `P`, the
output satisfies some condition `Q`. The standard way to write down such
a guarantee is a **Hoare triple** `{P} c {Q}`, which says: "if `c` is
run from any state satisfying `P` and it terminates, the final state
satisfies `Q`." There is a small handful of inference rules that let
you build up correctness proofs for big programs from proofs about
their parts, and the whole apparatus is called *Hoare logic*.

Hoare logic in its original form works beautifully for simple
imperative programs. It runs into trouble as soon as programs become
**self-referential** in any serious way — for instance when a function
can take itself as an argument, when data structures can contain
pointers to themselves, or when the program manipulates other programs.
The trouble is that the meaning of a program in such a language is
defined in terms of itself, and the most obvious way of writing down
"what `{P} c {Q}` means" turns into a circular definition.

The standard fix is called **step indexing**. Instead of asking
"does `c` satisfy its specification?", you ask "does `c` satisfy its
specification *if we only look at the first `n` execution steps*?",
for every natural number `n`. Each individual question is well-defined
without circularity, because the answer at depth `n` only refers to
the answers at depths smaller than `n`. The "real" answer is then
recovered as "yes at every `n`." This trick (Appel–McAllester 2001,
later refined by Ahmed, by Birkedal and collaborators, and by the Iris
project) is now the standard technical backbone for verifying
sophisticated programming languages.

This project takes the position that step indexing is, at its heart,
a logical technique that set theorists already discovered in the
1960s, under the name **forcing**. Forcing was invented by Paul Cohen
to build mathematical structures whose properties can be described by
specifying, level by level, what is true in some growing approximation.
The approximations are called *conditions*; smaller approximations
extend to bigger ones; a property is "forced" by a condition if every
extension of that condition makes the property true. The exact
technique Cohen first used was called **ramified forcing**: it built
the approximations as an explicit stratified hierarchy, where each
level only refers to levels below it.

What we are doing in this project is making the analogy precise:

- Step-indexed propositions *are* propositions in a forcing semantics.
- The forcing conditions are the natural numbers (the step indices).
- The "later" modality `▷`, which is the central technical device of
  step-indexed logics, is the operator that says "to talk about a
  property here, you must drop one level."
- This corresponds exactly to the *ramification* in Cohen's original
  forcing construction.

If we can make this precise enough, then results about ramified
forcing (a topic with decades of mathematical study) become available
as tools for reasoning about programs, and conversely the program-
verification community gets a cleaner conceptual account of why
step-indexed logic has the shape it does.

We mechanize everything in **Rocq** (the proof assistant formerly known
as Coq), so every claim in the development is a machine-checked
theorem rather than a hand-waved argument.

## What is in this directory

### What we have done

**Phase 1 — propositional layer.**
[coq/Phase1_Forcing.v](coq/Phase1_Forcing.v) defines forcing conditions
(natural numbers, with smaller naturals reading as stronger conditions
— this is the topos-of-trees / Iris orientation; the dictionary with
the standard Cohen-style ordering is given in the file header). It
defines step-indexed propositions as downward-closed predicates on
conditions, the Heyting-algebra connectives (`⊤`, `⊥`, `∧`, `∨`, `→`)
in their Kripke form, and the later modality `▷`. It proves the
standard intuitionistic introduction and elimination rules, the basic
laws of `▷`, and **Löb's rule** `(▷ φ → φ) ⊢ φ`, which is the engine
of all step-indexed recursive reasoning. A sanity check shows that
`▷ ⊥` and `⊥` are not interderivable, witnessing that step-indexing
genuinely changes the propositional theory rather than collapsing to
ordinary intuitionistic logic.

No external Coq libraries are used in Phase 1 beyond `Arith` and `Lia`.

**Phase 2 — IMP and its Hoare logic.**

- [coq/Phase2a_IMP.v](coq/Phase2a_IMP.v) defines the IMP language
  (a small imperative language with mutable state and standard
  control-flow constructs) and gives it a call-by-value small-step
  operational semantics. Each small step corresponds to one decrement
  of the step-index clock.

- [coq/Phase2b_Hoare.v](coq/Phase2b_Hoare.v) defines a step-indexed
  weakest precondition for IMP commands and lifts both the wp and the
  Hoare triple itself to step-indexed propositions over the forcing
  semantics from Phase 1. It proves soundness of the structural rules:
  `skip`, assignment, sequencing, the conditional, and the rule of
  consequence.

- [coq/Phase2c_While.v](coq/Phase2c_While.v) proves soundness of the
  `while` rule by induction on the step index, which is precisely
  the meta-level form of Löb's rule. It then packages all six
  soundness rules into a single theorem `imp_hoare_rules`. (At this
  point the *propositional* Löb's rule from Phase 1 is not yet
  invoked directly; an internal-Löb derivation is on the list for
  later — see notes below.)

For IMP, step-indexing is genuinely overkill: every non-terminal
command can step, so the wp is a partial-correctness predicate that
could equivalently be defined without any indexing at all. Phase 2 is
the calibration phase, where the forcing reading is at its crispest
and most explanatory, but does not yet do technical work the
non-step-indexed version could not.

**Phase 3a — an untyped λ-calculus with general recursion.**
[coq/Phase3a_Lambda.v](coq/Phase3a_Lambda.v) defines a small
higher-order language (variables in de Bruijn style, integer
constants, addition, a zero-test conditional, λ-abstraction,
application, and a fix-point operator), all the standard de Bruijn
machinery for shift and substitution, and a call-by-value small-step
semantics. `EFix` is treated as a value and self-unfolds when applied,
so the language has general recursion without recursive types as a
separate construct.

This is the substrate for the rest of Phase 3. With `fix` in the
language, the wp predicate becomes essentially recursive in the
program being analysed, and step-indexing stops being optional.

### What the plan is

- **Phase 3b** — step-indexed wp for the λ-calculus, lifted to an
  `iProp` as in Phase 2b. Soundness for the *non-`fix`* constructs:
  values, application, arithmetic, conditional. Unlike Phase 2, the
  wp here will need an explicit safety conjunct, because λ-calculus
  has stuck terms (e.g. applying an integer as if it were a function).

- **Phase 3c** — the payoff. Soundness for `fix`, using the
  propositional Löb rule from Phase 1 directly at the `iProp` level,
  not by meta-level induction on `n`. This is where the forcing
  framework is supposed to do real technical work, and where the
  ramification story becomes load-bearing rather than just
  decorative.

- **Phase 3d** — a worked example (likely factorial via `fix`) that
  exhibits the full system end-to-end, partly as a sanity check and
  partly to make the reasoning concrete for the paper.

- **Phase 4** — writeup, in `paper/`. The concrete shape of the
  contribution will be decided by what comes out of Phase 3, but the
  central thesis is: step-indexed Hoare logic is *ramified* forcing
  over `(ω, ≤)`, with `▷` as the explicit level-descent operator.
  The reason step-indexing resists "unramification" (unlike modern
  set-theoretic forcing, where Shoenfield showed the explicit level
  hierarchy can be eliminated) is that the propositions over which
  we recurse are themselves built impredicatively in higher-order
  languages, so the level filtration is doing real work.

### Known gaps and refinements to come

- The wp predicate in Phase 2b does not literally enforce safety
  (non-stuckness): a stuck non-`CSkip` configuration would satisfy
  it vacuously. For IMP this is invisible because IMP has no stuck
  terms, but it means the doc comment on `wp_at` slightly overclaims.
  Phase 3b will introduce a wp that does enforce safety explicitly,
  because the λ-calculus needs it.

- The `while` rule in Phase 2c is currently proved by induction on
  the step index. Conceptually this is the same as Löb, but the
  *internal* (`iProp`-level) Löb rule from Phase 1 is not yet
  threaded through. We will produce an alternative `hoare_while`
  proof that goes through `iLob` once the higher-order setting
  makes the framework reasoning natural.

- The Phase 4 thesis as stated above is, at present, an aspiration.
  It is what Phase 3 should *test*: if the soundness proof for `fix`
  goes through cleanly *only* via Löb-at-`iProp`, the thesis is
  vindicated; if it can be done equally cleanly by direct meta-level
  induction, the thesis weakens to "ramified forcing is a nice way
  to talk about step-indexing" rather than "ramification is doing
  real work that cannot be eliminated."

## How to build

From the project root (`~/Documents/math/forcing-hoare/`):

```
coq_makefile -f _CoqProject -o Makefile
make
```

Requires Coq 8.18 or compatible. Tested against Coq 8.18.0.

## References (for the reader who wants to go further)

- Paul Cohen, *Set Theory and the Continuum Hypothesis* (1966) — the
  original ramified forcing construction.
- Joseph Shoenfield, *Unramified Forcing* (1971) — the cleanup that
  collapsed Cohen's ramification, giving the modern presentation.
- Andrew Appel and David McAllester, *An indexed model of recursive
  types for foundational proof-carrying code* (TOPLAS 2001) — the
  original step-indexed model.
- Lars Birkedal et al., *First steps in synthetic guarded domain
  theory* (LMCS 2012) — the topos-of-trees presentation, which is
  the implicit forcing semantics behind modern step-indexing.
- Ralf Jung et al., *Iris from the ground up* (JFP 2018) — the
  state-of-the-art step-indexed separation logic, mechanized in Coq.
