# When does the calculus equal the PCS? (numerical exploration)

Setup: `pip install pycddlib-standalone networkx scipy numpy`.

- `pcs.py`, `pcs2.py`: formulas (`base`, `neg`, `tens`, `wth`, derived `par`, `plus`, `lolli`),
  webs, coherence graphs, generators of P(A); vertex enumeration only at negations (cdd).
- `lpgap.py`, `general.py`: one-sided gap certificates (LP optimum > 0/1 optimum).
  `general.pred` is the conjectured gap predicate.
- `exact2.py`: exact vertex enumeration for every case the conjecture predicts has no gap.
- `additive.py`, `recheck.py`: additive types (built with & and ⊕), where coherence graphs are
  exactly the cographs.

Conjecture (2026-10-08): a formula over nonempty data types has calculus ≠ PCS iff some
`X ⊗ Y` occurs negatively with an induced 4-cycle in the coherence graphs of both `X` and `Y`
(equivalently, `((2⊸2)⊗(2⊸2))^⊥` is a coordinate retract of it).
The "if" direction is proved in Lean (`Retract.lean`: `gap_of_C4`, `gap_of_C4_occ`).

**Refuted (2026-10-08).** `(2 & 1) ⊸ ((2⊸2) ⊗ (2⊸2))` has a gap without a double 4-cycle:
the coherence graph of `((2⊸2)⊗(2⊸2))^⊥` contains an induced house, and P3 ⊠ house is imperfect.
The restriction to 3 × 5 web points is the clique-constrained polytope of P3 ⊠ house, which has
fractional vertices. On the full 48-point web, LP max 2.5 > 2 = max over 0/1 points. The statement
for second-order additive types (cographs) is still open: there, gap ⟺ both contain C4 matched all
tests.
