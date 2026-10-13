"""Numeric-only bounded test of Fejes-Toth area relaxation on q=0,1 fans.
Decision: whether topology plus per-cell angle conservation alone might exclude q1.
No site realizability or lower-bound certification claimed. 9x9 small SLSQP runs.
"""
import numpy as np, math, json
from scipy.optimize import minimize
from pathlib import Path
r=.38

def F(a):
 t=np.arcsin(r*np.sin(a/2))
 return t-.5*np.sin(2*t)+.5*r*r*np.sin(a)
results=[]
for q in (0,1):
 # q1 ear (0,1,2); q0 no ear. Hub 9,10.
 core=[i for i in range(9) if not(q and i==1)]
 for span in range(1,len(core)):
  u,v=core[0],core[span]
  edges=[(i,(i+1)%9) for i in range(9)]
  if q: edges +=[(0,2)]
  edges +=[(9,x) for x in core[:span+1]]
  edges +=[(10,x) for x in [*core[span:],core[0]]]
  edges +=[(9,10)]
  E=len(edges)
  mat=np.zeros((11,E+9))
  for k,(i,j) in enumerate(edges): mat[i,k]=mat[j,k]=1
  for i in range(9): mat[i,E+i]=1
  def area(x):return r*r*np.sin(x[:E]).sum()+F(x[E:]).sum()
  def coverage(x):return 2*np.arcsin(r*np.sin(x[E:]/2)).sum()-2*math.pi
  x0=np.ones(E+9)*1.1;x0[E:]=2.3
  sol=minimize(lambda x:-area(x),x0,method='SLSQP',bounds=[(1e-6,math.pi-1e-6)]*(E+9),constraints=[{'type':'eq','fun':lambda x:mat@x-2*math.pi},{'type':'ineq','fun':coverage}],options={'ftol':1e-11,'maxiter':300})
  rec={'q':q,'span':span,'area_relax':float(area(sol.x)),'success':bool(sol.success),'linear_resid':float(np.max(abs(mat@sol.x-2*math.pi))),'coverage_slack':float(coverage(sol.x)),'angles':sol.x.tolist(),'edges':edges}
  results.append(rec)
  print(q,span,sol.success,round(area(sol.x),9),round(rec['linear_resid'],9),flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(results,indent=2))
