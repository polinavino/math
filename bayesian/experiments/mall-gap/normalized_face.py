"""Checks cited in Section 11 (not formalized).

1. Two arguments, T = ((2 -o 2) (x) (2 -o 2))^perp over Bool: the elements of P(T) that halt with
   probability 1 on every pair of total functions form a polytope whose vertices are all {0,1}
   (12 of them, the deterministic two-party classical processes of Baumeler and Wolf 2016).
   The full P(T) has fractional vertices.
2. Three arguments: on the same normalized face there is a gap (LP optimum > 0/1 optimum).

Needs pycddlib-standalone, scipy, numpy.
"""
import itertools
import numpy as np
import cdd
from scipy.optimize import linprog, milp, LinearConstraint, Bounds


def constraints(k):
    pts = list(itertools.product(itertools.product(range(2), range(2)), repeat=k))
    idx = {p: i for i, p in enumerate(pts)}
    funs = list(itertools.product(range(2), repeat=2))
    rows = []
    for fs in itertools.product(funs, repeat=k):
        r = [0] * len(pts)
        for xs in itertools.product(range(2), repeat=k):
            r[idx[tuple((xs[i], fs[i][xs[i]]) for i in range(k))]] += 1
        rows.append(r)
    return pts, rows


def vertices(rows, n, normalized):
    M = [[1] + [-x for x in r] for r in rows] + [[0] + [int(j == i) for j in range(n)] for i in range(n)]
    mat = cdd.matrix_from_array(M, rep_type=cdd.RepType.INEQUALITY)
    if normalized:
        mat.lin_set = set(range(len(rows)))
    gen = cdd.copy_generators(cdd.polyhedron_from_matrix(mat))
    return [row[1:] for row in gen.array if row[0] == 1]


if __name__ == '__main__':
    pts, rows = constraints(2)
    for normalized in (True, False):
        V = vertices(rows, len(pts), normalized)
        frac = [v for v in V if any(abs(x - round(x)) > 1e-9 for x in v)]
        print('two arguments,', 'normalized' if normalized else 'full PCS', ': vertices', len(V), 'fractional', len(frac))
    pts, rows = constraints(3)
    A = np.array(rows, dtype=float); b = np.ones(len(rows)); n = len(pts)
    rng = np.random.default_rng(0); best = 0.0
    for _ in range(300):
        c = rng.standard_normal(n)
        lp = linprog(-c, A_eq=A, b_eq=b, bounds=[(0, None)] * n, method='highs')
        ip = milp(-c, constraints=LinearConstraint(A, b, b), integrality=np.ones(n), bounds=Bounds(0, 1))
        best = max(best, ip.fun - lp.fun)
    print('three arguments, normalized: largest LP minus 0/1 optimum over 300 objectives', round(best, 4))
