import itertools, time, sys
import networkx as nx
from networkx.algorithms import isomorphism
from pcs import base, neg, tens, wth, plus, show, web, coh
import pcs2
C4=nx.cycle_graph(4)
def hasC4(G): return isomorphism.GraphMatcher(G,C4).subgraph_is_isomorphic()
# additive formulas from base 1 with & and (+), up to web size 4, one per coherence-graph iso class
forms={1:[base(1)]}
for n in range(2,5):
    forms[n]=[]
    for k in range(1,n//2+1):
        for A in forms[k]:
            for B in forms[n-k]:
                forms[n]+= [wth(A,B), plus(A,B)]
reps=[]
for n in range(1,5):
    for A in forms[n]:
        G=coh(A)
        if not any(len(web(B))==n and nx.is_isomorphic(G,coh(B)) for B in reps): reps.append(A)
print('additive types (iso classes):',len(reps))
for A in reps: assert pcs2.S(A) and pcs2.Q(A)
t=time.time(); n=0; bad=0
for i,X in enumerate(reps):
    for Y in reps[i:]:
        if len(web(X))*len(web(Y))>16: continue
        F=neg(tens(X,Y)); n+=1
        gap = not pcs2.integral(F)
        pred = hasC4(coh(X)) and hasC4(coh(Y))
        if gap!=pred: bad+=1; print('MISMATCH',show(X),show(Y),gap,pred)
print('pairs',n,'mismatches',bad,'%.0fs'%(time.time()-t))
