"""Bounded numeric diagnostic: q1 outside-six width budget + repaired area dual.
16 symmetry representatives (combinatorial relabeling only, not metric symmetry).
Decision whether added cluster capacity enables an area proof for q1 classes.
"""
import numpy as np, math,json
from pathlib import Path
from scipy.optimize import minimize
P=Path(__file__).parent;R=.38;a=np.linspace(0,math.pi,1801)
w=2*np.arcsin(R*np.maximum(.5,np.sin(a/2)));F=.5*R*R*np.sin(a)+.5*(w-np.sin(w))
core=[0,2,3,4,5,6,7,8];B=math.asin(2*R);seen=set();out=[]
for start in range(8):
 cc=core[start:]+core[:start]
 for span in range(2,5):
  S=frozenset(cc[:span+1]);T=frozenset([*cc[span:],cc[0]])
  key=lambda s,t:tuple(sorted([tuple(sorted(s)),tuple(sorted(t))]))
  kk=min(key(S,T),key({(2-i)%9 for i in S},{(2-i)%9 for i in T}))
  if kk in seen:continue
  seen.add(kk)
  edges=[(i,(i+1)%9) for i in range(9)]+[(0,2)]+[(9,x) for x in S]+[(10,x) for x in T]+[(9,10)]
  ei=np.array([e[0] for e in edges]);ej=np.array([e[1] for e in edges])
  def dual(z):
   mu=z[:11];lam,eta=z[11:];b=mu[ei]+mu[ej];t=np.arccos(np.clip(b/(R*R),-1,1))
   val=2*math.pi*(sum(mu)-lam)-eta*(2*math.pi-2*B)+np.sum(R*R*np.sin(t)-b*t)
   for i in range(9):val+=np.max(F+(lam+(eta if i>=3 else 0))*w-mu[i]*a)
   return val
  z=np.r_[np.ones(9)*.03,[-.04,-.04],.2,.2]
  o=minimize(dual,z,method='Powell',bounds=[(-1,1)]*11+[(0,2)]*2,options={'maxiter':80,'ftol':1e-8,'xtol':1e-7})
  row={'start':start,'span':span,'hub9_rings':sorted(S),'hub10_rings':sorted(T),'dual':float(o.fun),'z':o.x.tolist(),'success':bool(o.success)};out.append(row)
  print('q1',start,span,'degrees',len(S)+1,len(T)+1,'dual',round(o.fun,8),'eta',round(o.x[-1],8),flush=True)
  (P/'area_triple_dual.json').write_text(json.dumps(out,indent=2))
