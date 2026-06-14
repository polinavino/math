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
- The forcing conditions are the natural numbers (the step indices) —
  or, in the abstract version, any well-founded preorder.
- The "later" modality `▷`, which is the central technical device of
  step-indexed logics, is the operator that says "to talk about a
  property here, you must drop one level."
- This corresponds exactly to the *ramification* in Cohen's original
  forcing construction.
- The internal Löb rule is what makes the framework work in
  higher-order settings, and at the meta level it is *exactly*
  well-founded induction on the forcing order.

We mechanize everything in **Rocq** (the proof assistant formerly known
as Coq), so every claim in the development is a machine-checked
theorem rather than a hand-waved argument.

## What is in this directory

### What we have done

#### Phase 1 — propositional layer

The forcing semantics for step-indexed intuitionistic logic, with
the later modality and Löb's rule. No external dependencies beyond
`Arith` and `Lia`.

[coq/Phase1_Forcing.v](coq/Phase1_Forcing.v)
- **Defines:** `cond` (= `nat`); `iProp` as a record of downward-closed
  predicates with monotonicity; entailment `ientails` / `⊢`;
  connectives `iTrue`/`iFalse`/`iAnd`/`iOr`/`iImpl` (with notations
  `⊤ ⊥ ∧ ∨ →`); the later modality `iLater` / `▷`.
- **Proves:** preorder of `⊢` (`ientails_refl`, `ientails_trans`);
  Heyting algebra introduction and elimination rules
  (`iAnd_intro`/`iOr_elim`/`iImpl_intro`/`iImpl_elim`/etc.); laws of
  `▷` (`iLater_mono`, `iLater_intro`: φ ⊢ ▷ φ, distribution over `∧`);
  **`iLob`** — the propositional Löb rule `(▷ φ → φ) ⊢ φ`; sanity
  check `iLater_False_distinct` that `▷ ⊥` and `⊥` are not
  interderivable.

#### Phase 2 — IMP and its Hoare logic

[coq/Phase2a_IMP.v](coq/Phase2a_IMP.v)
- **Defines:** `var` (= `nat`), `state` (= `var → Z`), `update`;
  arithmetic and boolean expressions `aexp`/`bexp` with `aeval`/`beval`;
  commands `cmd` (skip / assign / seq / if / while); small-step `step`
  and its iteration `steps`; configuration `safe`.
- **Proves:** rewrite helpers `update_eq`/`update_neq`; the smoke
  test `tiny_runs`.

[coq/Phase2b_Hoare.v](coq/Phase2b_Hoare.v)
- **Defines:** `wp_at` (step-indexed weakest precondition as a
  Fixpoint on `nat`); `wp` (lifted to `iProp`); `hoare` (the Hoare
  triple as an `iProp`); validity `hoare_valid`; `asgn_pre`
  (substitution-at-postcondition).
- **Proves:** monotonicities `wp_at_mono`, `wp_at_post_mono`;
  unfolding lemma `wp_at_S`; `hoare_valid_alt` (equivalence with
  meta-level `∀ n s, …`); soundness of `hoare_skip`, `hoare_assign`,
  `hoare_seq` (with the helper `wp_seq`), `hoare_if`,
  `hoare_consequence`; smoke test `demo_assign`.

[coq/Phase2c_While.v](coq/Phase2c_While.v)
- **Proves:** `hoare_while` (soundness of `while`, via meta-level
  induction on the step index); `hoare_while_iLob` (the same theorem,
  via the internal `iLob` rule — `apply ientails_trans` to factor
  through `▷ φ → φ`, then `apply iLob`); smoke test
  `demo_while_false`; the packaged `imp_hoare_rules` theorem
  combining all six structural rules.

For IMP, step-indexing is genuinely overkill: every non-terminal
command can step, so the wp is a partial-correctness predicate that
could equivalently be defined without any indexing at all. Phase 2
is the calibration phase. The conceptual interest is that the same
`while` rule admits both an induction-on-`n` proof and an internal-`iLob`
proof, which the file presents side-by-side to make the equivalence
explicit.

#### Phase 3 — an untyped λ-calculus with general recursion

[coq/Phase3a_Lambda.v](coq/Phase3a_Lambda.v)
- **Defines:** `expr` (de-Bruijn-indexed variables, integers, plus,
  zero-test conditional, λ-abstraction, application, fix); `value`
  (integers and the two value-form binders, `EFix` is a value);
  de-Bruijn machinery `shift` and `subst_at` / `subst`; small-step
  CBV semantics `step` (β-reduction and `fix`-unfolding) and its
  iteration `steps`.
- **Proves:** smoke tests `id_app_5`, `two_plus_three`, `fix_id_5`.

[coq/Phase3b_Wp.v](coq/Phase3b_Wp.v)
- **Defines:** `wp_at` for `expr` — with three conjuncts (termination,
  **safety** = value-or-can-step, and step-closure); `wp` (lifted to
  `iProp`); `wp_valid`.
- **Proves:** `wp_at_mono`, `wp_at_post_mono`, `wp_at_S`,
  `wp_valid_alt`; helper `value_no_step`; **`wp_value`** (a value
  satisfies any postcondition it semantically satisfies);
  **`wp_pure_step_at`** / **`wp_pure_step`** (deterministic
  head-reduction transfers wp).

[coq/Phase3c_Fix.v](coq/Phase3c_Fix.v)
- **Defines:** `recursive_spec` — for a value `e` and predicate `S`,
  the `iProp` saying "for every `v` satisfying `S`, applying `e` to
  `v` is safe and yields a value satisfying `S`."
- **Proves:** determinism helpers `step_fix_det`, `step_fix_progress`,
  `not_value_app_fix`; **`wp_fix`** — given a body whose substituted
  form preserves `recursive_spec` whenever the self-reference does
  (a Lipschitz-like assumption), `EFix body` satisfies
  `recursive_spec`. The proof is `apply ientails_trans` to reduce
  to `⊤ ⊢ ▷ φ → φ`, then `apply iLob`. No meta-level induction on
  `nat` appears.

[coq/Phase3d_Example.v](coq/Phase3d_Example.v)
- **Defines:** `recursive_id` (= `EFix (ELam (EVar 0))`), a fix-point
  that ignores its self-reference and returns its argument;
  `bottom` (= `EFix (EVar 0)`), the canonical divergent fix-point.
- **Proves:** helper `wp_at_value`; determinism helper
  `step_app_lam_var0_det`; operational sanity checks
  `recursive_id_runs` (= `EInt 5` in two steps) and `bottom_loops`
  (= itself in one step); **`recursive_id_spec`** (verified using
  `wp_fix`: for every `S`, `recursive_id` preserves `S`);
  **`bottom_spec`** (every recursive spec is satisfied vacuously —
  a one-liner proof exhibiting that `wp_fix`'s premise reduces to
  reflexivity for `bottom`).

The structural difference between Phases 2c and 3c is the load-bearing
piece of the thesis. In Phase 2c the `while` rule *can* be proved by
meta-level induction (the IMP setting is first-order enough that the
iProp machinery is optional). In Phase 3c the natural proof of
`wp_fix` goes through `iLob` directly: for higher-order recursion,
the internal Löb rule is the natural tool.

#### Phase 4 — abstract forcing framework

[coq/Phase4_Abstract.v](coq/Phase4_Abstract.v)
- **Defines:** `ForcingStructure` — a record packaging an abstract
  carrier `cond`, a preorder `le`, a strict relation `lt`, the
  reflexivity / transitivity / `lt ⊂ le` / `lt`-`le` transitivity
  axioms, and well-foundedness of `lt`. Inside `Section
  AbstractForcing` (parameterised by an arbitrary
  `FS : ForcingStructure`): `iProp` (downward-closed predicates),
  `ientails` / `⊢`, `iTrue`/`iFalse`/`iAnd`/`iImpl`, `iLater` as
  *universal-over-strict-predecessors* (`▷ φ at p := ∀ p' ≺ p,
  p' ⊩ φ`). At the top level: `nat_FS` (the instantiation at the
  natural numbers); `prod_FS` (a second, non-trivially-different
  instance: `nat × nat` with the pointwise product order, motivated
  by independent step-indices for parallel components).
- **Proves:** `ientails_refl`, `ientails_trans`, monotonicity
  helpers, and **`iLob`** (proved by `apply (well_founded_ind
  (fs_lt_wf FS))`). Well-foundedness of `lt_pair` (via the
  measure `fst p + snd p`). `Check iLob nat_FS` and `Check iLob
  prod_FS` confirm the framework instantiates at both structures
  without any change to the abstract development.

The conceptual point: the "ramification" in "ramified forcing" is
*not* specifically the `nat`-indexed stratification. Any well-founded
forcing notion supports the same internal logic with the same modal
structure. The choice of `nat` in Phase 1 is for computational
convenience (one program step = one decrement of the step index), not
for foundational necessity. This also makes precise the equivalence
between Löb's rule and well-founded induction: `iLob` is literally
`well_founded_ind` on the strict order, viewed internally rather than
externally.

#### Phase 5 — metatheoretic result: Löb's rule is essential

[coq/Phase5_Metatheory.v](coq/Phase5_Metatheory.v)
- **Defines:** a "would-be" iProp framework over `Z` (the integers,
  which are not well-founded under `<`), including `iPropZ`,
  `ientailsZ`, `iFalseZ`, `iImplZ`, `iLaterZ` — all the same
  constructions as in Phase 4, but without invoking well-foundedness.
- **Proves:** `lob_premise_at` — the premise `(▷ ⊥) → ⊥` is forced
  at every condition (vacuously, because `Z` has no minimum so
  `▷ ⊥` is never forced); `lob_conclusion_fails` — `⊥` is forced
  at no condition; **`lob_fails_over_Z`** — the entailment
  `(▷ ⊥ → ⊥) ⊢ ⊥` does not hold.

The upshot: the `fs_lt_wf` axiom in `ForcingStructure` cannot be
dropped. This is the step-indexed analog of the well-known
characterisation in modal logic (Gödel–Löb axiom is sound on the
class of transitive converse-well-founded Kripke frames). The
"ramification" in ramified forcing is not a presentation convenience —
it is *constitutive* of the modal logic.

#### Phase 6 — bridge to forcing translations

[coq/Phase6_Bridge.v](coq/Phase6_Bridge.v)
- **Defines:** the constant embedding `embed : Prop → iProp`,
  notation `⌜·⌝`, mapping a meta-level proposition to the iProp
  constantly forced (or constantly unforced) at every condition.
- **Proves:** that `⌜·⌝` is a Heyting algebra homomorphism — it
  commutes with `True`/`False`/`∧`/`∨`/`→` in both directions
  (`embed_True_l`/`r`, `embed_False_l`/`r`, `embed_and_intro`/`elim`,
  `embed_or_intro`/`elim`, `embed_impl_intro`/`elim`); the genuine
  new content of `iProp` over the embedded image is `▷`
  (`embed_later_distinct` — `▷ ⌜False⌝ ⊬ ⌜False⌝`).

The conceptual claim: `iProp FS` of Phase 4 is *literally* the
propositional fragment of the Jaber–Tabareau–Sozeau forcing
translation of CIC, instantiated at the forcing structure `FS`. The
`▷` modality is the step-indexed-specific addition — produced by the
well-founded strict refinement, and giving rise to Löb's rule via the
construction in Phase 4. A full mechanization of the JTS translation
is future work.

#### The paper

[paper/main.tex](paper/main.tex) — draft of the writeup, in CPP
(`acmart` `sigplan`) format, currently 18 pages. The paper's central
thesis is supported by the mechanization on four fronts:

1. *In higher-order settings, Löb's rule is the load-bearing
   reasoning principle for recursion* (Phase 3c): the meta-level
   induction shortcut available for IMP-style recursion (Phase 2c)
   is not the natural tool when the soundness predicate is itself
   recursive in the program.

2. *The framework is genuinely abstract over the forcing notion*
   (Phase 4): step-indexing is not tied to ω; it is well-founded
   induction over an arbitrary forcing structure, and Löb's rule
   is *equivalent to* this well-founded induction at the meta
   level.

3. *Well-foundedness is essential* (Phase 5): without it, Löb's
   rule fails. The "ramification" in ramified forcing is
   constitutive of the modal logic, not a presentation choice.

4. *The framework is the propositional fragment of the
   Jaber–Tabareau–Sozeau forcing translation* (Phase 6),
   with `▷` as the step-indexed-specific addition that
   well-founded forcing makes available.

The paper is split into per-section fragment files, with
[main.tex](paper/main.tex) doing only the preamble, frontmatter,
and `\input` of each section, plus the bibliography:

| File | Contents |
|---|---|
| [paper/intro.tex](paper/intro.tex) | Introduction |
| [paper/sec-prop.tex](paper/sec-prop.tex) | The propositional layer (Phase 1) |
| [paper/sec-imp.tex](paper/sec-imp.tex) | Hoare logic for IMP (Phase 2) |
| [paper/sec-lam.tex](paper/sec-lam.tex) | Hoare logic for the λ-calculus + fix (Phase 3) |
| [paper/sec-comparison.tex](paper/sec-comparison.tex) | The Phase 2c vs 3c diagnostic |
| [paper/sec-abstract.tex](paper/sec-abstract.tex) | Abstract forcing framework (Phase 4) |
| [paper/sec-lob-essential.tex](paper/sec-lob-essential.tex) | Löb's rule is essential (Phase 5) |
| [paper/sec-bridge.tex](paper/sec-bridge.tex) | Bridge to JTS forcing translations (Phase 6) |
| [paper/sec-related-work.tex](paper/sec-related-work.tex) | Related work |
| [paper/sec-conclusion.tex](paper/sec-conclusion.tex) | Conclusion |
| [paper/refs.bib](paper/refs.bib) | Bibliography (~38 entries) |
| [paper/Makefile](paper/Makefile) | `make` to build, `make clean` to clean intermediates |

Venue plan: primary target is CPP (deadline October, conference
January); fallback ITP (deadline February–March, conference July).
No overlap, so we can submit to CPP first and to ITP if not
accepted.

### Known gaps

- **Generality of `wp_fix`** (Phase 3c): the soundness rule for `fix`
  is currently stated for a specific shape of spec (where the
  precondition and postcondition coincide as a single predicate `S`).
  A more general rule with distinct pre/postconditions, and a rule
  for `fix` applied at higher types, would strengthen the case for
  the framework's usability.

- **Abstract framework as a foundation** (Phase 4): we showed the
  abstract framework recovers Phase 1, but did not re-derive Phases
  2 and 3 on top of it. This is mostly cosmetic — Phase 1's results
  are immediate corollaries — but a full refactor would make the
  parametric framing the canonical one.

## How to build

### Rocq development

From the project root:

```
coq_makefile -f _CoqProject -o Makefile
make
```

Requires Coq 8.18 or compatible. Tested against Coq 8.18.0. No
external libraries beyond `Arith`, `Lia`, `ZArith`, `Wellfounded`,
`Wf_nat`.

### Paper

From `paper/`:

```
make
```

Requires `pdflatex` and `bibtex`. The `acmart` document class is
distributed with TeX Live. Output is `paper/main.pdf`.

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
