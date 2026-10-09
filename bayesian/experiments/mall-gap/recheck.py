import numpy as np, itertools, time
import networkx as nx
from networkx.algorithms import isomorphism
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
from pcs import base, neg, tens, wth, plus, show, web, coh
import pcs2
C4=nx.cycle_graph(4); C5=nx.cycle_graph(5)
def hasC4(G): return isomorphism.GraphMatcher(G,C4).subgraph_is_isomorphic()
def lp_ip(G, c):
    n=G.shape[1]
    lp=linprog(-c,A_ub=G,b_ub=np.ones(len(G)),bounds=[(0,None)]*n,method='highs')
    ip=milp(-c,constraints=LinearConstraint(G,-np.inf,np.ones(len(G))),integrality=np.ones(n),bounds=Bounds(0,1))
    return -lp.fun, -ip.fun
forms={1:[base(1)]}
for n in range(2,6):
    forms[n]=[]
    for k in range(1,n//2+1):
        for A in forms[k]:
            for B in forms[n-k]: forms[n]+=[wth(A,B),plus(A,B)]
reps=[]
for n in range(1,6):
    for A in forms[n]:
        if not any(len(web(B))==n and nx.is_isomorphic(coh(A),coh(B)) for B in reps): reps.append(A)
n=0; agree=0; dis=[]
for i,X in enumerate(reps):
    for Y in reps[i:]:
        if len(web(X))*len(web(Y))>25: continue
        if not (hasC4(coh(X)) and hasC4(coh(Y))): continue
        n+=1
        Gm=np.array([np.outer(a,b).ravel() for a in pcs2.Gen(X) for b in pcs2.Gen(Y)])
        H=nx.strong_product(coh(X),coh(Y)); H=nx.convert_node_labels_to_integers(H, ordering='sorted')
        # index of (a,b) in strong_product with sorted ordering matches a*|Y|+b
        GM=isomorphism.GraphMatcher(H,C5)
        m=next(GM.subgraph_isomorphisms_iter())
        c=np.zeros(Gm.shape[1]); c[list(m.keys())]=1
        l,ip=lp_ip(Gm,c)
        if l>ip+1e-6: agree+=1
        else: dis.append((show(X),show(Y),l,ip))
print('predicted-gap pairs',n,'certified by C5 objective',agree)
for d in dis[:5]: print('NOT certified',d)
