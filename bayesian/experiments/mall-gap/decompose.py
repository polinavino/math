"""Constructive proof prototype: QSTAB(G ⊠ H) = STAB(G ⊠ H) for G a forest comparability graph and H a
cograph, by an explicit decomposition (Main / Core / ABS0 / ABS_L / exact_absorb).

Cograph: ('leaf', v) | ('union', A, B) | ('join', A, B).
Forest: list of trees, tree = (node, [subtrees]).
Vectors: dict vertex -> float.
"""
import random, itertools
from fractions import Fraction

EPS = 1e-9


# ---------- cographs ----------
def verts(H):
    if H[0] == 'leaf': return [H[1]]
    return verts(H[1]) + verts(H[2])

def omega(H, v):
    if H[0] == 'leaf': return v.get(H[1], 0.0)
    a, b = omega(H[1], v), omega(H[2], v)
    return max(a, b) if H[0] == 'union' else a + b

def adj(H, x, y):
    """strict adjacency in the cograph"""
    if H[0] == 'leaf': return False
    A, B = set(verts(H[1])), set(verts(H[2]))
    if x in A and y in A: return adj(H[1], x, y)
    if x in B and y in B: return adj(H[2], x, y)
    return H[0] == 'join'

def restrict(H, S):
    if H[0] == 'leaf': return H if H[1] in S else None
    a, b = restrict(H[1], S), restrict(H[2], S)
    if a is None: return b
    if b is None: return a
    return (H[0], a, b)

def closed_nbhd(H, I):
    V = verts(H)
    return {y for y in V if any(y == x or adj(H, x, y) for x in I)}

def is_stable(H, I):
    return all(not adj(H, x, y) for x, y in itertools.combinations(I, 2))

def add(u, v, c=1.0):
    w = dict(u)
    for k, x in v.items(): w[k] = w.get(k, 0.0) + c * x
    return w

def scale(v, c): return {k: c * x for k, x in v.items()}

def comp(v, H):
    S = set(verts(H)); return {k: x for k, x in v.items() if k in S}


# ---------- forests ----------
def nodes(F):
    out = []
    for (r, ch) in F: out.append(r); out += nodes(ch)
    return out

def max_chains(F, prefix=()):
    if not F: return [list(prefix)]
    out = []
    for (r, ch) in F:
        out += max_chains(ch, prefix + (r,)) if ch else [list(prefix + (r,))]
    return out

def chain_sum(y, C):
    s = {}
    for x in C: s = add(s, y.get(x, {}))
    return s


# ---------- exact absorption ----------
def exact_absorb(K, b, v, L):
    """a <= v with omega(b + a) = L, assuming omega(b) <= L <= omega(b + v)"""
    if K[0] == 'leaf':
        x = K[1]; return {x: L - b.get(x, 0.0)} if v.get(x, 0.0) > 0 or L - b.get(x, 0.0) > EPS else {x: 0.0}
    K1, K2 = K[1], K[2]
    b1, b2, v1, v2 = comp(b, K1), comp(b, K2), comp(v, K1), comp(v, K2)
    if K[0] == 'union':
        a1 = exact_absorb(K1, b1, v1, min(L, omega(K1, add(b1, v1))))
        a2 = exact_absorb(K2, b2, v2, min(L, omega(K2, add(b2, v2))))
    else:
        L1 = max(omega(K1, b1), L - omega(K2, add(b2, v2)))
        a1 = exact_absorb(K1, b1, v1, L1)
        a2 = exact_absorb(K2, b2, v2, L - L1)
    return add(a1, a2)


# ---------- ABS ----------
def ABS0(K, m, F, y):
    """split y = y1 + y2 nodewise with omega(m + Y1(C)) <= omega(m), omega(Y2(C)) <= omega(m + Y(C)) - omega(m)"""
    if K[0] == 'leaf':
        return {x: {} for x in nodes(F)}, {x: comp(y.get(x, {}), K) for x in nodes(F)}
    K1, K2 = K[1], K[2]
    if K[0] == 'join':
        p1, q1 = ABS0(K1, comp(m, K1), F, {x: comp(y.get(x, {}), K1) for x in nodes(F)})
        p2, q2 = ABS0(K2, comp(m, K2), F, {x: comp(y.get(x, {}), K2) for x in nodes(F)})
    else:
        M = omega(K, m)
        p1, q1 = ABSL(K1, comp(m, K1), F, {x: comp(y.get(x, {}), K1) for x in nodes(F)}, M)
        p2, q2 = ABSL(K2, comp(m, K2), F, {x: comp(y.get(x, {}), K2) for x in nodes(F)}, M)
    return ({x: add(p1[x], p2[x]) for x in nodes(F)}, {x: add(q1[x], q2[x]) for x in nodes(F)})


def ABSL(K, m, F, y, L):
    """split with omega(m + Y1(C)) <= L and omega(Y2(C)) <= max(0, omega(m + Y(C)) - L)"""
    p, q = {}, {}
    def go(trees, base):
        for (x, ch) in trees:
            yx = y.get(x, {})
            if omega(K, add(base, yx)) <= L + EPS:
                p[x] = yx; q[x] = {}
                go(ch, add(base, yx))
            else:
                a = exact_absorb(K, base, yx, L)
                sub = [(x, ch)]
                ysub = {z: y.get(z, {}) for z in nodes(sub)}
                ysub[x] = add(yx, a, -1.0)
                pp, qq = ABS0(K, add(base, a), sub, ysub)
                for z in nodes(sub):
                    p[z] = pp[z]; q[z] = qq[z]
                p[x] = add(pp[x], a)
    go(F, m)
    return p, q


# ---------- Core and Main ----------
def Core(H, m, F, y):
    """(m, y) as a mixture of (1_I, y_I): list of (lam, I, yI)"""
    if H[0] == 'leaf':
        x = H[1]; mx = m.get(x, 0.0); out = []
        if mx > EPS: out.append((mx, frozenset([x]), {z: {} for z in nodes(F)}))
        if 1 - mx > EPS: out.append((1 - mx, frozenset(), {z: scale(y.get(z, {}), 1 / (1 - mx)) for z in nodes(F)}))
        return out
    H1, H2 = H[1], H[2]
    m1, m2 = comp(m, H1), comp(m, H2)
    y1 = {z: comp(y.get(z, {}), H1) for z in nodes(F)}
    y2 = {z: comp(y.get(z, {}), H2) for z in nodes(F)}
    if H[0] == 'union':
        out = []
        for (l1, I1, w1) in Core(H1, m1, F, y1):
            for (l2, I2, w2) in Core(H2, m2, F, y2):
                out.append((l1 * l2, I1 | I2, {z: add(w1[z], w2[z]) for z in nodes(F)}))
        return out
    t1, t2 = omega(H1, m1), omega(H2, m2)
    p1, q1 = ABS0(H1, m1, F, y1)
    p2, q2 = ABS0(H2, m2, F, y2)
    out = []
    for (t, Hj, mj, pj) in ((t1, H1, m1, p1), (t2, H2, m2, p2)):
        if t > EPS:
            for (l, I, w) in Core(Hj, scale(mj, 1 / t), F, {z: scale(pj[z], 1 / t) for z in nodes(F)}):
                out.append((t * l, I, w))
    t0 = 1 - t1 - t2
    if t0 > EPS:
        out.append((t0, frozenset(), {z: scale(add(q1[z], q2[z]), 1 / t0) for z in nodes(F)}))
    return out


def Main(H, F, z):
    """z on forest x H as a mixture of valid assignments: list of (lam, sigma)"""
    if not F: return [(1.0, {})]
    if len(F) > 1:
        out = [(1.0, {})]
        for T in F:
            part = Main(H, [T], z)
            out = [(l1 * l2, {**s1, **s2}) for (l1, s1) in out for (l2, s2) in part]
        return out
    (r, ch) = F[0]
    res = []
    for (lam, I, yI) in Core(H, z.get(r, {}), ch, {x: z.get(x, {}) for x in nodes(ch)}):
        if lam < EPS: continue
        Hsub = restrict(H, set(verts(H)) - closed_nbhd(H, I)) if I else H
        if Hsub is None:
            sub = [(1.0, {x: frozenset() for x in nodes(ch)})]
        else:
            sub = Main(Hsub, ch, yI)
        for (l2, s2) in sub:
            res.append((lam * l2, {r: I, **s2}))
    return res


# ---------- tests ----------
def rand_cograph(vs, rng):
    if len(vs) == 1: return ('leaf', vs[0])
    k = rng.randint(1, len(vs) - 1)
    return (rng.choice(['union', 'join']), rand_cograph(vs[:k], rng), rand_cograph(vs[k:], rng))

def rand_forest(ns, rng):
    if not ns: return []
    trees = []; rest = list(ns)
    while rest:
        r = rest.pop(0); k = rng.randint(0, len(rest))
        trees.append((r, rand_forest(rest[:k], rng))); rest = rest[k:]
    return trees

def qstab_vertex(F, H, rng):
    """a random vertex of {z >= 0 : omega(sum_C z) <= 1} via LP with clique constraints"""
    import numpy as np
    from scipy.optimize import linprog
    N = nodes(F); V = verts(H)
    idx = {(x, h): i for i, (x, h) in enumerate(itertools.product(N, V))}
    # cliques of H: enumerate maximal cliques by brute force
    cl = [K for r in range(1, len(V) + 1) for K in itertools.combinations(V, r)
          if all(adj(H, a, b) for a, b in itertools.combinations(K, 2))]
    rows = []
    for C in max_chains(F):
        for K in cl:
            row = np.zeros(len(idx))
            for x in C:
                for h in K: row[idx[(x, h)]] = 1
            rows.append(row)
    c = -np.array([rng.random() for _ in idx])
    res = linprog(c, A_ub=np.array(rows), b_ub=np.ones(len(rows)), bounds=[(0, None)] * len(idx), method='highs-ds')
    z = {x: {} for x in N}
    for (x, h), i in idx.items():
        if res.x[i] > 1e-12: z[x][h] = float(res.x[i])
    return z

def check(H, F, z, mix):
    N = nodes(F); V = verts(H)
    tot = sum(l for l, _ in mix)
    assert abs(tot - 1) < 1e-6, tot
    for x in N:
        for h in V:
            val = sum(l for l, s in mix if h in s.get(x, frozenset()))
            assert abs(val - z[x].get(h, 0.0)) < 1e-6, (x, h, val, z[x].get(h, 0.0))
    for l, s in mix:
        for C in max_chains(F):
            sets = [s.get(x, frozenset()) for x in C]
            U = set()
            for S in sets:
                assert not (U & S), 'not disjoint'
                U |= S
            assert is_stable(H, U), 'not stable'
    return True

if __name__ == '__main__':
    rng = random.Random(3); n = 0
    for trial in range(400):
        nv = rng.randint(1, 6); nn = rng.randint(1, 6)
        H = rand_cograph([f'h{i}' for i in range(nv)], rng)
        F = rand_forest([f'x{i}' for i in range(nn)], rng)
        z = qstab_vertex(F, H, rng)
        mix = Main(H, F, z)
        check(H, F, z, mix); n += 1
    print('ok', n, 'random instances decomposed and verified')
