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

- [coq/Phase1_Forcing.v](coq/Phase1_Forcing.v) — the propositional
  layer. We define forcing conditions (natural numbers), step-indexed
  propositions (downward-closed predicates on conditions), the
  Heyting-algebra connectives (`⊤`, `⊥`, `∧`, `∨`, `→`), and the
  later modality `▷`. We prove the standard intuitionistic
  introduction and elimination rules, the basic laws of `▷`, and
  **Löb's rule** `(▷ φ → φ) ⊢ φ`, which is the engine of all
  step-indexed recursive reasoning. We also include a sanity check
  showing that `▷ ⊥` and `⊥` are not equivalent, witnessing that
  step-indexing genuinely changes the propositional theory rather
  than collapsing to ordinary intuitionistic logic.

The Phase 1 file uses no external Coq libraries (only `Arith` and
`Lia` from the standard library), so the conceptual content is
visible without machinery getting in the way.

### What the plan is

- **Phase 2** — A simple imperative language (IMP: assignment,
  sequencing, branching, loops, mutable state) with operational
  semantics, and Hoare triples `{P} c {Q}` interpreted as a
  step-indexed proposition over the forcing semantics from Phase 1.
  Soundness of the standard Hoare rules — including the `while` rule,
  which is where Löb earns its keep — should follow with little fuss.
  This phase is mainly a calibration exercise: at this level of
  expressiveness, step-indexing is overkill, but the forcing reading
  is at its crispest and most explanatory.

- **Phase 3** — A higher-order language with recursive types. This is
  where step-indexing is actually necessary, and where the forcing
  reading should pay technical rather than just pedagogical dividends.
  The goal is a clean soundness proof for a Hoare-style logic over
  this language, mechanized end-to-end. We will likely need Iris or
  at least `stdpp` at this stage; we will reach for them only when
  the bare-Coq development becomes unwieldy.

- **Phase 4** — The writeup, in `paper/`. The contribution will be
  decided by what comes out of Phases 2 and 3, but at minimum the
  paper should argue that step-indexed Hoare logic is *ramified*
  forcing over `(ω, ≤)`, with the `▷` modality as the explicit
  level-descent operator; and that the reason step-indexing resists
  "unramification" (unlike modern set-theoretic forcing, where
  Shoenfield showed the explicit level hierarchy can be eliminated)
  is that the propositions over which we recurse are themselves
  built impredicatively in higher-order languages, so the level
  filtration is doing real work.

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
