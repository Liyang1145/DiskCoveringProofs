"""Bounded legal-domain descent against proposed augmented stress (12 starts, <=100 iterations).
Safe finite differences/backtracking enforce domain; no infeasible NaN result is a witness.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,json,warnings
from scipy.special import logsumexp
warnings.filterwarnings('ignore',category=RuntimeWarning)
P=Path(__file__).parent;z={'__file__':str(P/'angle_stress_probe.py')};exec((P/'angle_stress_probe.py').read_text().split('y0=np.zeros(29)')[0],z)
N,a0,branches,lam,mu,act,domain=[z[k] for k in ['N','a0','branches','lam','mu','act','domain']];n=N.shape[1];temp=.1;rho=1.;margin=1e-5

def fun(y):
 try:
  d=domain(y)
  if not np.all(np.isfinite(d)) or min(d)<=margin:return None
  g,c=branches(a0+N@y);v=temp*logsumexp(g[act]/temp,b=lam)+mu@c+rho*sum(c[13:]**2)
  return float(v) if np.isfinite(v) else None
 except (ValueError,OverflowError,FloatingPointError):return None

def grad(y):
 h=2e-6;v0=fun(y);g=np.zeros(n)
 for k in range(n):
  e=np.eye(n)[k]*h;vp=fun(y+e);vm=fun(y-e)
  if vp is not None and vm is not None:g[k]=(vp-vm)/(2*h)
  elif vp is not None:g[k]=(vp-v0)/h
  elif vm is not None:g[k]=(v0-vm)/h
  else:return None
 return g

rng=np.random.default_rng(841);base=fun(np.zeros(n));out={'scope':'legal-domain numerical attack on one artificial stress, not covering counterexample or continuum certificate','temp':temp,'rho':rho,'runs':[]}
for k in range(12):
 rad=[.01,.1,.3,.6][k%4]
 for attempt in range(10000):
  y=rng.normal(size=n);y*=rad/np.linalg.norm(y)
  if fun(y) is not None:break
 else:raise RuntimeError('no legal seed')
 B=np.eye(n);g=grad(y);reason='iteration_budget'
 for it in range(100):
  v=fun(y);p=-B@g
  if p@g>=0:p=-g;B=np.eye(n)
  p*=min(1,.1/max(np.linalg.norm(p),1e-30));step=1.
  while step>1e-9:
   vnew=fun(y+step*p)
   if vnew is not None and vnew<=v+1e-4*step*(g@p):break
   step*=.5
  if step<=1e-9:reason='line_search_stop';break
  yy=y+step*p;gg=grad(yy)
  if gg is None:reason='boundary_gradient';break
  s=yy-y;t=gg-g;st=s@t
  if st>1e-12:
   I=np.eye(n);B=(I-np.outer(s,t)/st)@B@(I-np.outer(t,s)/st)+np.outer(s,s)/st
  y,g=yy,gg
  if np.linalg.norm(g)<1e-6:reason='small_gradient';break
 row={'start':k,'start_radius':rad,'iterations':it+1,'reason':reason,'stress_change':fun(y)-base,'min_domain':float(min(domain(y))),'gradient_norm':float(np.linalg.norm(g)),'distance':float(np.linalg.norm(y)),'nonlinear_constraint_error':float(max(abs(branches(a0+N@y)[1][13:]))),'angles':(a0+N@y).tolist()};out['runs'].append(row);print({key:v for key,v in row.items() if key!='angles'},flush=True);(P/'nonlinear_stress_attack.json').write_text(json.dumps(out,indent=2))
