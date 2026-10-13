"""Degenerate sector implies SAME t on both adjacent switches; bounded diagnostic jointfactor."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,math,json
from scipy.optimize import differential_evolution
P=Path(__file__).parent;R=.38;pi=math.pi
results=[]
for source,inds in [('endpoint_frozen_dual_0_4.json',range(9)),('middle_sector_dual_proposal.json',[2])]:
 j=json.loads((P/source).read_text());z=np.array(j['z']);edges=[tuple(e) for e in j['edges']]
 def sw(bi,b,t):
  i,jj=bi,(bi+1)%9;e=edges.index(tuple(sorted((i,jj))));return (z[i]+z[jj]-z[50+e]+2*z[112+bi])*b+(R*R*math.sin(2*b)/2-z[11+e]*math.sin(b)**2+z[33+2*i]+z[32+2*jj])*t*t+(-z[73+e]*math.sin(b)+z[95+2*i]+z[94+2*jj])*t
 def ring(i,t):
  w=2*math.asin(R*t);return (w-math.sin(w))/2-z[i]*pi-(z[32+2*i]+z[33+2*i])*t*t-(z[94+2*i]+z[95+2*i])*t+(z[71]+(z[112+(i-1)%9]+z[112+i])/2)*w
 rows=[]
 for i in inds:
  def fun(x):
   t,b,c=x;return -(ring(i,t)+sw((i-1)%9,b,t)+sw(i,c,t))
  s=differential_evolution(fun,[(75/76,1),(0,pi/2),(0,pi/2)],seed=848+i,maxiter=180,popsize=15,tol=1e-10)
  row={'sector':i,'joint_max_numeric':float(-s.fun),'arg':s.x.tolist()}
  if source.startswith('endpoint'):
   base=json.loads((P/'sector_degenerate_probe.json').read_text());excluded=[20+i,11+(i-1)%9,11+i];row['conditional_total_numeric']=base['full_dual_numeric']-sum(base['factors'][k] for k in excluded)-s.fun
  rows.append(row)
 results.append({'source':source,'rows':rows})
 print(source,rows,flush=True)
(P/'degenerate_triplet_probe.json').write_text(json.dumps({'scope':'finite numerical jointfactor diagnostic only; exact structuralcoupling valid all inward degenerate sectors','results':results},indent=2))
