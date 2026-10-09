import numpy as np, itertools, time, random
import networkx as nx
from networkx.algorithms import isomorphism
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
from pcs import base, neg, tens, wth, plus, lolli, par, show, web, coh
import pcs2
C4=nx.cycle_graph(4)
def hasC4(G): return isomorphism.GraphMatcher(G,C4).subgraph_is_isomorphic()
def lp_ip(G,c):
    n=G.shape[1]
    lp=linprog(-c,A_ub=G,b_ub=np.ones(len(G)),bounds=[(0,None)]*n,method='highs')
    ip=milp(-c,constraints=LinearConstraint(G,-np.inf,np.ones(len(G))),integrality=np.ones(n),bounds=Bounds(0,1))
    return -lp.fun,-ip.fun
def holes(H, maxlen=7, limit=40):
    out=[]
    for k in (5,7):
        if k>maxlen: break
        for comp,G2 in ((False,H),(True,nx.complement(H))):
            GM=isomorphism.GraphMatcher(G2,nx.cycle_graph(k))
            for m in itertools.islice(GM.subgraph_isomorphisms_iter(),limit):
                out.append(sorted(m.keys()))
    return out
def gap_test(Gm, Hgraph, seed=0):
    n=Gm.shape[1]; rng=np.random.default_rng(seed)
    objs=[np.ones(n)]+[rng.random(n) for _ in range(30)]
    for S_ in holes(Hgraph):
        c=np.zeros(n); c[S_]=1; objs.append(c)
    for _ in range(60):
        c=np.zeros(n); c[rng.choice(n,size=min(n,rng.integers(4,9)),replace=False)]=1; objs.append(c)
    for c in objs:
        l,ip=lp_ip(Gm,c)
        if l>ip+1e-6: return True
    return False
@__import__('functools').lru_cache(maxsize=None)
def pred(A):
    """conjectured gap"""
    t=A[0]
    if t=='base': return False
    if t in ('tens','wth'): return pred(A[1]) or pred(A[2])
    B=A[1]  # A = neg B
    if B[0]=='base': return False
    if B[0]=='neg': return pred(B[1])
    if B[0]=='wth': return pred(neg(B[1])) or pred(neg(B[2]))
    if B[0]=='tens': return pred(neg(B[1])) or pred(neg(B[2])) or (hasC4(coh(B[1])) and hasC4(coh(B[2])))
if __name__=="__main__":
    b1,b2=base(1),base(2)
    L1=[b1,b2,neg(b2),lolli(b2,b2),tens(b2,neg(b2)),wth(b2,b1),plus(neg(b2),b1),wth(b2,b2),plus(neg(b2),neg(b2))]
    L2=[]
    for X,Y in itertools.combinations_with_replacement(L1,2):
        if len(web(X))*len(web(Y))<=16:
            L2+= [tens(X,Y), neg(tens(X,Y))]
    cands=L1+L2
    print('candidates',len(cands),flush=True)
    t=time.time(); n=0; bad=[]; stats={'gap':0,'nogap':0}
    random.seed(1)
    pairs=[(X,Y) for X,Y in itertools.combinations_with_replacement(cands,2) if 4<=len(web(X))*len(web(Y))<=64]
    random.shuffle(pairs)
    for X,Y in pairs[:400]:
        try:
            Gm=np.array([np.outer(a,b).ravel() for a in pcs2.Gen(X) for b in pcs2.Gen(Y)])
        except Exception as e:
            continue
        F=neg(tens(X,Y)); n+=1
        truth=gap_test(Gm, nx.strong_product(coh(X),coh(Y)))
        p=pred(F)
        stats['gap' if truth else 'nogap']+=1
        if truth!=p:
            bad.append((show(X),show(Y),truth,p)); print('MISMATCH',show(X),'|',show(Y),'truth',truth,'pred',p,flush=True)
        if n%50==0: print(n,'done',stats,len(bad),'mismatches','%.0fs'%(time.time()-t),flush=True)
    print('tested',n,stats,'mismatches',len(bad),'%.0fs'%(time.time()-t))
    