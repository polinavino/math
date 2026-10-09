# Second-order classification for cograph types

**Notation.** For a formula A: web |A|, coherence graph G_A (strict coherence), PCS P(A).
For a graph F:
- CL(F) is Mix of the indicators of the cliques of F;
- STAB(F) is Mix of the indicators of the stable sets of F;
- QSTAB(F) = {z ≥ 0 : z(K) ≤ 1 for every clique K of F}.

A formula X has the *clique property* if P(X) = CL(G_X). Examples:
- data types n and n^⊥;
- n ⊸ m (Lean: `P_lolli_base`, `mem_lin_iff_mix`);
- every formula built from data types with & and ⊕.

The coherence graphs of formulas built with & and ⊕ are exactly the cographs, since & is join and ⊕ is disjoint union.

## Theorem

Let X, Y be formulas over nonempty data types with the clique property.

1. The calculus of (X ⊗ Y)^⊥ equals its PCS iff G_X ⊠ G_Y is perfect.
2. If G_X and G_Y are cographs, this holds iff G_X or G_Y has no induced C4.

Direction "both contain C4 ⇒ gap" holds for *all* formulas and is proved in Lean (`gap_of_C4`, `gap_of_C4_occ` in `Retract.lean`).

## Proof of 1

- P(X ⊗ Y) = orth(orth{x ⊗ y}) is the closed, convex, downward-closed hull of the products. Since P(X), P(Y) are mixtures of clique indicators, the products are mixtures of indicators of K × L. So P(X ⊗ Y) is Mix of subsets of such rectangles. These are exactly the cliques of G_X ⊠ G_Y, because a clique of a strong product projects to cliques. Hence P(X ⊗ Y) = CL(F) with F := G_X ⊠ G_Y.
- P((X ⊗ Y)^⊥) = CL(F)^⊥ = QSTAB(F). Its {0,1}-points are the stable sets of F, so the calculus is STAB(F).
- STAB(F) = QSTAB(F) iff F is perfect (Lovász 1972, Chvátal 1975).

## Proof of 2 (the cograph lemma)

**(⇒)** If both contain C4, then C4 ⊠ C4 is an induced subgraph, and it contains C5 (the pentagon). So the product is imperfect.

**(⇐)** Let G be a C4-free cograph, i.e. trivially perfect, i.e. the comparability graph of a rooted forest (Wolk 1962, Golumbic 1978). Let H be a cograph. We show that G ⊠ H has no hole of length ≥ 5 (Lemma A) and no antihole of length ≥ 6 (Lemma B). Then G ⊠ H is weakly chordal, hence perfect (Hayward 1985). This does not use the strong perfect graph theorem.

**Preliminaries.** In the forest, x ≈ y means comparable or equal, and x ⊥ y means incomparable.

- (P1) If y ≈ a, y ≈ b and a ⊥ b, then y is a proper common ancestor of a and b.
- (P2) Path lemma. In a walk x_0, …, x_m with consecutive terms ≈, an element q of minimum depth satisfies q ≈ x_i for all i.
  - Proof: suppose some x_i ⊥ q. Leaving the subtree of lca(x_i, q) that contains x_i requires a step to an ancestor of the lca. That node is shallower than q.
- (P3) In G ⊠ H, distinct (x,h), (y,h') are adjacent iff x ≈ y and h ≈ h'.
- (P4) Reduction. Restrict G and H to the projections of Z. They stay a forest comparability graph and a cograph. π_H(Z) is connected because Z is. If |π_H(Z)| = 1, then Z lies in a copy of G, which is perfect. So WLOG π_H(Z) = V(H), H is connected with ≥ 2 vertices, and H = A + B (join of nonempty cographs).
- (P5) Dominant vertices. If x_s ≈ x_j for all j, then z_s ~ z_j iff h_s ≈ h_j. If h_t ≈ h_j for all j, then z_t ~ z_j iff x_t ≈ x_j.

### Lemma A (no holes of length k ≥ 5)

Let z_0 … z_{k-1} be an induced cycle with z_i = (x_i, h_i), indices mod k. By (P2), applied to the closed walk of x's, a minimum-depth element r satisfies r ≈ x_i for all i. Pick s with x_s = r, so z_s is dominant.

WLOG h_s ∈ A. Since z_s is adjacent to every z_j with h_j ∈ B, the B-indices lie in {s−1, s+1}. They are nonempty because π_H(Z) ⊇ B. WLOG h_{s+1} ∈ B.

**Case 1: h_{s−1} ∈ B.**
- All other indices are A-indices.
- For j ∈ [s+3, s−2]: z_{s+1} ≁ z_j while h_{s+1} ~ h_j, so x_{s+1} ⊥ x_j.
- Likewise x_{s−1} ⊥ x_j for j ∈ [s+2, s−3].
- Let q be of minimum depth among x_{s+2}, …, x_{s−2}.
  - If q = x_j with j ∈ [s+3, s−2]: x_{s+2} ≈ x_{s+1} and x_{s+2} ≈ q while x_{s+1} ⊥ q. By (P1), x_{s+2} is a proper ancestor of q, contradicting minimality.
  - Symmetrically, using x_{s−2} and x_{s−1}, q is not attained in [s+2, s−3].
- For k ≥ 5 the two ranges cover [s+2, s−2]. Contradiction.

**Case 2: h_{s−1} ∈ A.**
- s+1 is the only B-index, so B = {b} with b universal in H. By (P5), z_{s+1} ~ z_j iff x_{s+1} ≈ x_j, hence x_{s+1} ⊥ x_j for j ∈ [s+3, s−1].
- As in Case 1, the minimum depth of x_{s+2}, …, x_{s−1} is attained only at x_{s+2}.
- So x_{s+2} ≈ every x_j (including x_{s+1}, and r = x_s), and z_{s+2} is dominant.
- Put u_i = h_{s+2+i} for i = 0, …, k−2, so u_{k−2} = h_s. Then:
  - consecutive u's are ≈;
  - u_0 ≉ u_i for i ≥ 2 (z_{s+2} has neighbours z_{s+1}, z_{s+3} only);
  - u_{k−2} ≉ u_i for i ≤ k−4 (z_s is non-adjacent to z_{s+2}, …, z_{s−2}).
- The values u_i induce a connected subgraph of the cograph H. A shortest path from u_0 to u_{k−2} is induced, so it has length 2. Its middle vertex is adjacent to u_0, so it is the value u_1. But u_1 ≈ u_{k−2} contradicts u_{k−2} ≉ u_1, since 1 ≤ k−4.

### Lemma B (no antiholes of length k ≥ 6)

Let z_0 … z_{k−1} be an induced antihole: z_i ≁ z_{i±1}, and z_i ~ z_j otherwise.

**(B1) A dominant root.** Let r be of minimum depth with x_s = r. Then x_j ≈ r for j ∉ {s±1}.
- If x_{s+1} ⊥ r, the x_j with j ∈ [s+3, s−2] (nonempty for k ≥ 6) are ≈ to both. By (P1) they are proper ancestors of r: contradiction.
- So z_s is dominant. WLOG h_s ∈ A. Then h_{s±1} ∈ A, since h_s ≉ h_{s±1}.

**(B2) Boundaries.** A position p is a *boundary* if exactly one of h_p, h_{p+1} is in B.
- At a boundary, h_p ~ h_{p+1} but z_p ≁ z_{p+1}, so x_p ⊥ x_{p+1}.
- Every x_j with j ∉ {p−1, …, p+2} is then a proper common ancestor of x_p and x_{p+1}.
- Two boundaries p, p' with {p', p'+1} disjoint from {p−1, …, p+2} would make x_{p'}, x_{p'+1} both ancestors of x_p, hence comparable. That is a contradiction.
- So there are exactly two boundaries, at distance 1 or 2, and one letter fills a block of length 1 or 2. A contains s−1, s, s+1, so B is a block {t} or {t, t+1}.

**(B3) B-block {t, t+1}.**
- The boundaries give x_{t−1} ⊥ x_t and x_{t+1} ⊥ x_{t+2}.
- x_{t+2} is non-consecutive with z_t and z_{t−1}. So it is ≈ to both, hence a proper common ancestor of x_{t−1} and x_t.
- x_{t−1} is ≈ to x_{t+1} and x_{t+2}, hence a proper common ancestor of x_{t+1} and x_{t+2}.
- So x_{t+2} and x_{t−1} are proper ancestors of each other. Contradiction.

**(B4) B-block {t}.**
- B = {b}, b universal, so z_t ~ z_j iff x_t ≈ x_j. Hence x_t ⊥ x_{t±1} and x_t ≈ x_j otherwise.
- By (P1), every x_j with j ∉ {t−1, t, t+1} is a proper ancestor of x_t:
  - j = t+2 as a common ancestor with x_{t−1};
  - the others as common ancestors with x_{t+1}.
- So for J = [t+2, t−2] the x's are pairwise comparable. Then h_j ≉ h_{j+1} and h_i ≈ h_j for non-consecutive i, j ∈ J.

**If k ≥ 7:** |J| ≥ 4. Four consecutive indices of J give four distinct values inducing a P4 in H. Contradiction.

**If k = 6:** J = {t+2, t+3, t+4}, and z_{t+1}, z_{t+5} are adjacent to z_{t+3}, z_{t+4} and z_{t+2}, z_{t+3} respectively.
- This gives h_{t+1} ≈ h_{t+3}, h_{t+4}, h_{t+5}, and h_{t+5} ≈ h_{t+2}, h_{t+3}.
- If h_{t+5} ≉ h_{t+4}, then h_{t+3} − h_{t+5} − h_{t+2} − h_{t+4} is an induced P4. So h_{t+5} ≈ h_{t+4}, hence x_{t+5} ⊥ x_{t+4}.
- If h_{t+1} ≉ h_{t+2}, then h_{t+3} − h_{t+1} − h_{t+4} − h_{t+2} is an induced P4. So h_{t+1} ≈ h_{t+2}, hence x_{t+1} ⊥ x_{t+2}.
- x_{t+4} is an ancestor of x_{t+1} and x_{t+2} is not. x_{t+2} is an ancestor of x_{t+5} and x_{t+4} is not. Both lie on the ancestor chain of x_t.
- So depth(x_{t+2}) > depth(lca(x_t, x_{t+1})) ≥ depth(x_{t+4}) > depth(lca(x_t, x_{t+5})) ≥ depth(x_{t+2}). Contradiction.

∎

## Remarks

- **Numerical checks.** The lemma was checked on all 3,567 cograph pairs up to 30 vertices. Weak chordality was checked on 920 small pairs and a random sample of larger ones (`wchordal.py`).
- **Exact condition for n ⊸ m.** For X = n ⊸ m and Y = n' ⊸ m', G_X is complete multipartite with n parts of size m. It contains C4 iff n, m ≥ 2, which recovers the previously numerical exact condition.
- **The statement does not extend beyond second order.** (2 & 1) ⊸ ((2⊸2) ⊗ (2⊸2)) has a gap without a double C4. The coherence graph of T contains an induced house, and P3 ⊠ house is imperfect. See `README.md`.

## Not formalized

Formalizing the following would need new Lean infrastructure:
- the bipolar step in part 1;
- the perfect-graph polytope theorem (Lovász / Chvátal);
- Hayward's theorem;
- Lemmas A and B.

The "gap" direction is in Lean.
