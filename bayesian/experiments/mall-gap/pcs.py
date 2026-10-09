"""Numerical exploration: when does the calculus (Mix of {0,1} points) equal the PCS?

Formulas: ('base', n), ('neg', A), ('tens', A, B), ('wth', A, B).
P(A) is a down-closed polytope in R^web, stored by its vertex list.
"""
import itertools, functools
import numpy as np
import cdd
import networkx as nx

TOL = 1e-7


def neg(A): return ('neg', A)
def tens(A, B): return ('tens', A, B)
def wth(A, B): return ('wth', A, B)
def base(n): return ('base', n)
def par(A, B): return neg(tens(neg(A), neg(B)))
def plus(A, B): return neg(wth(neg(A), neg(B)))
def lolli(A, B): return neg(tens(A, neg(B)))


def show(A):
    t = A[0]
    if t == 'base': return str(A[1])
    if t == 'neg':
        B = A[1]
        return show(B) + '^'
    if t == 'tens': return '(' + show(A[1]) + ' x ' + show(A[2]) + ')'
    if t == 'wth': return '(' + show(A[1]) + ' & ' + show(A[2]) + ')'


@functools.lru_cache(maxsize=None)
def web(A):
    t = A[0]
    if t == 'base': return tuple(range(A[1]))
    if t == 'neg': return web(A[1])
    if t == 'tens': return tuple(itertools.product(web(A[1]), web(A[2])))
    if t == 'wth': return tuple([('L', a) for a in web(A[1])] + [('R', b) for b in web(A[2])])


@functools.lru_cache(maxsize=None)
def coh(A):
    """strict coherence graph on indices 0..|web|-1"""
    W = web(A); n = len(W)
    G = nx.Graph(); G.add_nodes_from(range(n))
    t = A[0]
    if t == 'base':
        return G
    if t == 'neg':
        H = coh(A[1])
        return nx.complement(H)
    if t == 'tens':
        GA, GB = coh(A[1]), coh(A[2]); nA, nB = len(web(A[1])), len(web(A[2]))
        def c(G, i, j): return i == j or G.has_edge(i, j)
        for i in range(n):
            a, b = divmod(i, nB)
            for j in range(i + 1, n):
                a2, b2 = divmod(j, nB)
                if c(GA, a, a2) and c(GB, b, b2): G.add_edge(i, j)
        return G
    if t == 'wth':
        GA, GB = coh(A[1]), coh(A[2]); nA = len(web(A[1]))
        for (i, j) in GA.edges(): G.add_edge(i, j)
        for (i, j) in GB.edges(): G.add_edge(nA + i, nA + j)
        for i in range(nA):
            for j in range(nA, n): G.add_edge(i, j)
        return G


def clean(vs):
    out = []
    seen = set()
    for v in vs:
        v = np.where(np.abs(v) < TOL, 0.0, v)
        key = tuple(np.round(v, 6))
        if key not in seen:
            seen.add(key); out.append(v)
    return out


def vertices_from_H(Arows, n):
    """{y >= 0 : <a,y> <= 1 for a in Arows} -> vertices"""
    rows = [[1.0] + list(-np.asarray(a, float)) for a in Arows]
    for i in range(n):
        e = [0.0] * (n + 1); e[i + 1] = 1.0; rows.append(e)
    mat = cdd.matrix_from_array(rows, rep_type=cdd.RepType.INEQUALITY)
    poly = cdd.polyhedron_from_matrix(mat)
    g = cdd.copy_generators(poly)
    vs = [np.array(r[1:]) for r in g.array if abs(r[0] - 1) < 1e-9]
    assert all(abs(r[0]) > 1e-9 for r in g.array), "unbounded"
    return clean(vs)


def downclose_vertices(gens, n):
    """vertices of the down-closed hull of conv(gens) within R^n_+"""
    rows = [[1.0] + list(map(float, v)) for v in gens]
    for i in range(n):
        r = [0.0] * (n + 1); r[i + 1] = -1.0; rows.append(r)
    mat = cdd.matrix_from_array(rows, rep_type=cdd.RepType.GENERATOR)
    poly = cdd.polyhedron_from_matrix(mat)
    h = cdd.copy_inequalities(poly)
    ineq = [list(r) for r in h.array]
    for i in range(n):
        e = [0.0] * (n + 1); e[i + 1] = 1.0; ineq.append(e)
    mat2 = cdd.matrix_from_array(ineq, rep_type=cdd.RepType.INEQUALITY)
    poly2 = cdd.polyhedron_from_matrix(mat2)
    g = cdd.copy_generators(poly2)
    vs = [np.array(r[1:]) for r in g.array if abs(r[0] - 1) < 1e-9]
    return clean(vs)


def maximal(vs):
    """drop vectors dominated coordinatewise by another"""
    out = []
    for i, v in enumerate(vs):
        dom = False
        for j, w in enumerate(vs):
            if i != j and np.all(w >= v - TOL) and np.any(w > v + TOL):
                dom = True; break
        if not dom: out.append(v)
    return out


@functools.lru_cache(maxsize=None)
def P(A):
    """vertex list (maximal ones) of the PCS of A"""
    t = A[0]; n = len(web(A))
    if t == 'base':
        return tuple(tuple(np.eye(n)[i]) for i in range(n)) if n else (tuple(),)
    if t == 'neg':
        V = [np.array(v) for v in P(A[1])]
        vs = vertices_from_H(V, n)
        return tuple(tuple(v) for v in maximal(vs))
    if t == 'tens':
        VA, VB = P(A[1]), P(A[2])
        gens = [np.outer(a, b).ravel() for a in VA for b in VB]
        gens = maximal(clean(gens))
        vs = downclose_vertices(gens, n)
        return tuple(tuple(v) for v in maximal(vs))
    if t == 'wth':
        VA, VB = P(A[1]), P(A[2])
        return tuple(tuple(list(a) + list(b)) for a in VA for b in VB)


def integral(A):
    return all(np.all((np.abs(np.array(v)) < 1e-6) | (np.abs(np.array(v) - 1) < 1e-6)) for v in P(A))


def frac_vertices(A):
    return [v for v in P(A) if not np.all((np.abs(np.array(v)) < 1e-6) | (np.abs(np.array(v) - 1) < 1e-6))]


def inP(A, x):
    """membership of x in down-closed hull of P(A) vertices via the dual: <x,y> <= 1 for vertices y of P(A^perp)"""
    for y in P(neg(A)):
        if np.dot(x, y) > 1 + 1e-6: return False
    return True


def cliques_sharp(A):
    """every maximal clique of the coherence graph is an element of P(A)"""
    G = coh(A); n = len(web(A))
    for K in nx.find_cliques(G):
        x = np.zeros(n); x[list(K)] = 1
        if not inP(A, x): return False
    return True


def S(A):  # P(A) = Mix(cliques)
    return integral(A) and cliques_sharp(A)


def Q(A):
    return S(neg(A))


def perfect(G):
    # perfect iff no odd hole / antihole; small graphs: use networkx is_perfect if available
    try:
        return nx.is_perfect_graph(G)
    except AttributeError:
        raise


if __name__ == '__main__':
    b2 = base(2)
    core = tens(lolli(b2, b2), lolli(b2, b2))
    T = neg(core)
    for name, A in [('2', b2), ('2^', neg(b2)), ('2-o2', lolli(b2, b2)), ('core', core), ('T', T)]:
        print(name, len(web(A)), 'verts', len(P(A)), 'integral', integral(A), 'S', S(A), 'Q', Q(A), 'perfect', perfect(coh(A)))
