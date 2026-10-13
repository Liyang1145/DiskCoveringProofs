"""Reduced positive shape model; six circle equations. Candidate/control/local diagnostic only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,math,json
from scipy.optimize import minimize
P=Path(__file__).parent;ns={'__file__':str(P/'q0_exact_closure_radius.py')};exec((P/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0],ns)
for name in ['x0','A','B','U','V','eq','rhs','alpha','ac']:globals()[name]=ns[name]
Alt=np.array([[(-1)**((j-i)%9) for j in range(9)] for i in range(9)])
def shape(y):
 x=np.r_[y,0.];a=ac+alpha@x;rad=np.exp(y[53:62]);u=np.roll(rad,1);v=rad;ell=np.sqrt(np.maximum(1e-30,(u-v)**2+4*u*v*np.sin(a/2)**2));L=np.arctan2(v*np.sin(a),u-v*np.cos(a));T=math.pi-a-L;tau=math.pi-T-np.roll(L,-1)-2*y[33:42];w=Alt@tau
 q=2*np.sin(w/2);rr=q/ell
 return a,w,ell,rr,tau

def ce(y):
 x=np.r_[y,0.];a,w,ell,rr,tau=shape(y)
 return np.r_[eq@x-rhs,(U-V)@x+np.log(np.sin(A@x))-np.log(np.sin(B@x)),rr[1:7]-rr[0]]
def ci(y):
 a,w,ell,rr,tau=shape(y);return np.r_[a,math.pi-a,w,math.pi-w,rr[0]-.37,.38-rr[0]]
y0=x0[:-1].copy();r0=math.exp(x0[-1]);s0=shape(y0);assert max(abs(ce(y0)))<1e-12 and max(abs(s0[3]-r0))<1e-12
h=1e-6;jac=np.column_stack([(ce(y0+np.eye(62)[k]*h)-ce(y0-np.eye(62)[k]*h))/(2*h) for k in range(62)]);sv=np.linalg.svd(jac,compute_uv=False);rank=int(sum(sv>1e-7));assert rank==40
out={'caliber':'positive branch local diagnostics, no global proof','candidate_residual':float(max(abs(ce(y0)))),'candidate_recovered_radius':float(s0[3][0]),'equations':len(ce(y0)),'variables':62,'numeric_rank':rank,'singular_values':sv.tolist(),'runs':[]}
bounds=[(1e-7,math.pi-1e-7)]*33+[(1e-7,math.pi/2-1e-7)]*9+[(-5,0)]*20
rng=np.random.default_rng(838)
for k in range(3):
 seed=y0.copy()
 if k:seed[:42]+=rng.normal(0,.001,42);seed[42:]=np.minimum(0,seed[42:]+rng.normal(0,.0001,20))
 sol=minimize(lambda y:shape(y)[3][0],seed,method='SLSQP',bounds=bounds,constraints=[{'type':'eq','fun':ce},{'type':'ineq','fun':ci}],options={'maxiter':200,'ftol':2e-13})
 a,w,ell,rr,tau=shape(sol.x);row={'trial':k,'success':bool(sol.success),'message':sol.message,'radius':float(rr[0]),'equality_error':float(max(abs(ce(sol.x)))),'all9radius_spread':float(max(abs(rr-rr[0]))),'min_inequality':float(min(ci(sol.x))),'active_radii_numeric':int(sum(sol.x[42:]>-1e-7)),'x':sol.x.tolist()};out['runs'].append(row);print({key:v for key,v in row.items() if key!='x'},flush=True)
(P/'q0_scale_free_shape.json').write_text(json.dumps(out,indent=2))
