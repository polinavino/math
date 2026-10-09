"""Gap test for {y >= 0 : <g,y> <= 1 for g in gens}: LP optimum vs 0/1 optimum over random objectives."""
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

def gap_certificate(gens, trials=60, seed=0):
    G = np.array(gens, float); n = G.shape[1]
    rng = np.random.default_rng(seed)
    objs = [np.ones(n)] + [rng.random(n) for _ in range(trials)] + [rng.integers(0, 3, n).astype(float) for _ in range(trials)]
    for c in objs:
        lp = linprog(-c, A_ub=G, b_ub=np.ones(len(G)), bounds=[(0, None)] * n, method='highs')
        if lp.status != 0: continue
        ip = milp(-c, constraints=LinearConstraint(G, -np.inf, np.ones(len(G))), integrality=np.ones(n), bounds=Bounds(0, 1))
        if -lp.fun > -ip.fun + 1e-6:
            return dict(c=c, lp=-lp.fun, ip=-ip.fun, y=lp.x)
    return None
