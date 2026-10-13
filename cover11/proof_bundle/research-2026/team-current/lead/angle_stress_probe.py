"""Bounded test of ONE candidate supporting-stress inequality, not global optimality proof.
Candidate KKT weights combine20radius branches; global-valid if stress>=logR* over
positive angular domain. Find violations to decide whether this simple certificate works.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,math,json
from scipy.optimize import minimize
from scipy.optimize._numdiff import approx_derivative
from scipy.linalg import null_space
P=Path(__file__).parent
zz={'__file__':str(P/'check_angle_only.py')};exec((P/'check_angle_only.py').read_text().split("a=ns['x0'][:42]")[0],zz)
ns,shape=zz['ns'],zz['shape'];a0=ns['x0'][:42];eq=ns['eq'][:,:42];rhs=ns['rhs'];act=np.where(ns['x0'][42:62]>-1e-7)[0];r0,co,detail=shape(a0)
def branches(a):
 r,c,d=shape(a);return d['logg']+np.log(max(d['rat'][0],1e-100)),c
Jc=approx_derivative(lambda a:branches(a)[1],a0,method='3-point');Jg=approx_derivative(lambda a:branches(a)[0][act],a0,method='3-point');K=np.vstack([np.c_[Jc.T,Jg.T],np.r_[np.zeros(21),np.ones(len(act))]])
mm=np.linalg.lstsq(K,np.r_[np.zeros(42),1.],rcond=1e-10)[0];mu=mm[:21];lam=mm[21:];station=float(max(abs(K@mm-np.r_[np.zeros(42),1.])))
assert station<1e-7 and min(lam)>0
# Keep13linear equalities exactly via nullspace; nonlinear cycle/circle8 are Lagrange terms.
N=null_space(eq);assert N.shape==(42,29)
def lag(y):
 a=a0+N@y;g,c=branches(a);return float(lam@g[act]+mu@c)
def domain(y):
 a=a0+N@y;r,c,d=shape(a);return np.r_[a[:33]-1e-5,math.pi-1e-5-a[:33],a[33:]-1e-5,math.pi/2-1e-5-a[33:],d['alpha']-1e-5,math.pi-1e-5-d['alpha'],d['w']-1e-5,math.pi-1e-5-d['w']]
y0=np.zeros(29);v0=lag(y0);rng=np.random.default_rng(8381);out={'scope':'bounded diagnostic of single supporting stress, not theorem','candidate_radius':r0,'stationarity_error':station,'active':act.tolist(),'weights':lam.tolist(),'multipliers':mu.tolist(),'candidate_logstress':v0,'runs':[]}
for k in range(8):
 y=np.zeros(29) if k==0 else rng.normal(0,[.01,.03,.08,.15][(k-1)%4],29)
 while min(domain(y))<0:y*=.5
 sol=minimize(lag,y,method='SLSQP',constraints=[{'type':'ineq','fun':domain}],options={'maxiter':160,'ftol':1e-11})
 row={'trial':k,'success':bool(sol.success),'message':sol.message,'stress_minus_candidate':float(lag(sol.x)-v0),'min_domain':float(min(domain(sol.x))),'nonlinear_residual':float(max(abs(branches(a0+N@sol.x)[1][13:]))),'angles':(a0+N@sol.x).tolist()};out['runs'].append(row);print({key:v for key,v in row.items() if key!='angles'},flush=True);(P/'angle_stress_probe.json').write_text(json.dumps(out,indent=2))
