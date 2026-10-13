"""Exact51edge graph permutation; reflected Schur follows permutation identity.
No numeric field approximation or root-symmetry assumption.
"""
from simplex_tree_pilot import *

def reflected(ff):
 p=lambda i:(4-i)%9 if i<9 else i
 fp={j:next(k for k,g in enumerate(faces) if set(g)=={p(i) for i in f}) for j,f in enumerate(faces)}
 def node(i):
  if i<9:return (3-i)%9
  if i<20:return 9+p(i-9)
  return 20+fp[i-20]
 edgeidx={tuple(sorted(e)):k for k,e in enumerate(edges)};ep=[edgeidx[tuple(sorted((node(v),node(w))))] for v,w in edges]
 assert sorted(ep)==list(range(51)) and all(ep[ep[k]]==k for k in range(51))
 al=[None]*51
 for k,a in enumerate(ff['alpha']):al[ep[k]]=a
 assert len(ff['alpha'])==51 and sum(F(a) for a in al)==1 and min(F(a) for a in al)>0
 ww={tuple(sorted(((3-i)%9,(3-j)%9))):w for i,j,w in ff['weights']};assert len(ww)==36
 return {'name':ff['name']+'-reflected','alpha':al,'weights':[(i,j,ww[(i,j)]) for i in range(9) for j in range(i+1,9)],'permuted_from':ff['name']}
