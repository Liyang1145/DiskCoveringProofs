"""Numeric tangent/KKT diagnostic ONLY, no proof of local/global optimality."""
from pathlib import Path
import numpy as np,json
P=Path(__file__).parent
src=(P/'q0_exact_closure_radius.py').read_text();exec(src[:src.index('out={')])
from scipy.optimize._numdiff import approx_derivative
from scipy.linalg import null_space
active=np.where(x0[42:62]>-1e-8)[0]+42
G=np.r_[jac[keep],np.eye(63)[active]];svG=np.linalg.svd(G,compute_uv=False);N=null_space(G,rcond=1e-7)
grad=np.eye(63)[62];mult=np.linalg.lstsq(G.T,-grad,rcond=1e-9)[0];station=np.max(np.abs(G.T@mult+grad))
# Central finite-difference Hessian of scalar Lagrangian, independently assembled stencil.
def lag(x):return x[-1]+mult[:rank]@ceq(x)[keep]+mult[rank:]@x[active]
h=2e-4;k=N.shape[1];H=np.zeros((k,k));v0=lag(x0)
for i in range(k):
 for j in range(k):
  if i==j:H[i,i]=(lag(x0+h*N[:,i])+lag(x0-h*N[:,i])-2*v0)/h**2
  else:H[i,j]=(lag(x0+h*(N[:,i]+N[:,j]))-lag(x0+h*(N[:,i]-N[:,j]))-lag(x0+h*(-N[:,i]+N[:,j]))+lag(x0-h*(N[:,i]+N[:,j])))/(4*h*h)
res={'active_indices':active.tolist(),'inactive_radii':[(int(i),float(np.exp(x0[i]))) for i in range(42,62) if i not in active],'constraint_rank_numeric':int(sum(svG>1e-7)),'tangent_dimension_numeric':k,'stationarity_residual':float(station),'active_multipliers':mult[rank:].tolist(),'tangent_hessian_eigenvalues_numeric':np.linalg.eigvalsh(H).tolist(),'tangent_R_components':N[-1].tolist(),'N':N.tolist()}
(P/'q0_closure_tangent.json').write_text(json.dumps(res,indent=2));print({k:v for k,v in res.items() if k!='N'})
