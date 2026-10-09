"""Faster exploration. Gen(A): vectors whose down-closed convex hull is P(A).
Only negation needs vertex enumeration (cdd). For tens/wth, integrality and the
clique property reduce to the components (proved by hand; checked on small cases).
"""
import itertools, functools, sys
import numpy as np
import cdd
import networkx as nx
from pcs import base, neg, tens, wth, par, plus, lolli, show, web, coh, clean, maximal, vertices_from_H, downclose_vertices

ZO = lambda v: bool(np.all((np.abs(v) < 1e-6) | (np.abs(v - 1) < 1e-6)))


@functools.lru_cache(maxsize=None)
def Gen(A):
    t = A[0]; n = len(web(A))
    if t == 'base':
        return tuple(tuple(np.eye(n)[i]) for i in range(n))
    if t == 'neg':
        V = [np.array(v) for v in Gen(A[1])]
        vs = vertices_from_H(V, n)
        return tuple(tuple(v) for v in maximal(vs))
    if t == 'tens':
        g = [np.outer(a, b).ravel() for a in Gen(A[1]) for b in Gen(A[2])]
        return tuple(tuple(v) for v in maximal(clean(g)))
    if t == 'wth':
        return tuple(tuple(list(a) + list(b)) for a in Gen(A[1]) for b in Gen(A[2]))


@functools.lru_cache(maxsize=None)
def integral(A):
    t = A[0]
    if t == 'base': return True
    if t == 'neg': return all(ZO(np.array(v)) for v in Gen(A))
    return integral(A[1]) and integral(A[2])


def anticliques_ok(A):
    """every maximal anticlique I of A satisfies g(I) <= 1 for all generators g of P(A)"""
    G = nx.complement(coh(A))
    gens = np.array(Gen(A))
    for I in nx.find_cliques(G):
        if gens[:, list(I)].sum(axis=1).max() > 1 + 1e-6: return False
    return True


@functools.lru_cache(maxsize=None)
def S(A):
    """P(A) = Mix of clique indicators"""
    t = A[0]
    if t == 'base': return True
    if t == 'neg': return integral(A) and anticliques_ok(A[1])
    return S(A[1]) and S(A[2])


def Q(A): return S(neg(A))


def perfect(G): return nx.is_perfect_graph(G)


def check_tensor_theory(A):
    """for small A = tens/wth, compare the reduced integrality with an actual down-closure computation"""
    n = len(web(A))
    vs = downclose_vertices([np.array(v) for v in Gen(A)], n)
    return all(ZO(v) for v in vs)


def report(name, A):
    import time
    t0 = time.time()
    n = len(web(A)); g = len(Gen(A))
    out = dict(name=name, web=n, gens=g, integral=integral(A), S=S(A), perfect=perfect(coh(A)))
    out['time'] = round(time.time() - t0, 1)
    print(out, flush=True)
    return out


if __name__ == '__main__':
    b1, b2, b3 = base(1), base(2), base(3)
    core = tens(lolli(b2, b2), lolli(b2, b2)); T = neg(core)
    for name, A in [('core', core), ('T', T), ('core par 2', par(core, b2)), ('T x 2', tens(T, b2)),
                    ('core par 2^', par(core, neg(b2))), ('core x 2', tens(core, b2)),
                    ('(2 par 2) x (2 par 2)', tens(par(b2, b2), par(b2, b2)))]:
        report(name, A)
