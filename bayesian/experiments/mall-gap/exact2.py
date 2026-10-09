import numpy as np, itertools, time
import multiprocessing as mp
from exactw import worker
def run_with_timeout(gens, secs):
    q = mp.Queue(); p = mp.Process(target=worker, args=(gens, q)); p.start(); p.join(secs)
    if p.is_alive():
        p.terminate(); p.join(); return None
    return [np.array(v) for v in q.get()] if not q.empty() else None
def main():
    from pcs import base, neg, tens, wth, plus, lolli, par, show, web, coh
    import pcs2
    from general import pred
    ZO = lambda v: bool(np.all((np.abs(v) < 1e-6) | (np.abs(v - 1) < 1e-6)))
    b1, b2, b3 = base(1), base(2), base(3)
    L1 = [b1, b2, b3, neg(b2), neg(b3), lolli(b2, b2), tens(b2, neg(b2)), wth(b2, b1), plus(neg(b2), b1), wth(b2, b2),
          plus(neg(b2), neg(b2)), lolli(b2, b3), lolli(b3, b2), par(b2, b2), tens(neg(b2), neg(b2))]
    L2 = []
    for X, Y in itertools.combinations_with_replacement(L1, 2):
        if len(web(X)) * len(web(Y)) <= 12: L2 += [tens(X, Y), neg(tens(X, Y)), wth(X, Y), plus(X, Y)]
    cands = L1 + L2
    pairs = [(X, Y) for X, Y in itertools.combinations_with_replacement(cands, 2) if 4 <= len(web(X)) * len(web(Y)) <= 20]
    print('pairs', len(pairs), flush=True)
    t = time.time(); n = 0; checked = 0; bad = []; skipped = 0; gapcount = 0
    for X, Y in pairs:
        F = neg(tens(X, Y))
        if pred(F): gapcount += 1; continue
        n += 1
        gens = [np.outer(a, b).ravel() for a in pcs2.Gen(X) for b in pcs2.Gen(Y)]
        vs = run_with_timeout(gens, 8)
        if vs is None: skipped += 1; continue
        checked += 1
        if not all(ZO(v) for v in vs):
            bad.append((show(X), show(Y))); print('COUNTEREXAMPLE', show(X), '|', show(Y), flush=True)
        if checked % 200 == 0: print(checked, 'checked', skipped, 'skipped', len(bad), 'bad', '%.0fs' % (time.time() - t), flush=True)
    print('gap predicted (proved by gap_of_C4 + transfer):', gapcount, '| no-gap predictions', n, 'exactly checked', checked,
          'skipped', skipped, 'counterexamples', len(bad), '%.0fs' % (time.time() - t), flush=True)
if __name__ == '__main__':
    mp.set_start_method('fork')
    main()
