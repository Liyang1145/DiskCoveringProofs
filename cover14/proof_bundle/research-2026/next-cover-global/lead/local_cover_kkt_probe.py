"""Bounded numeric mechanism test: true circumradius branch KKT critical Hessian.
Not a proof of localminimum, exactrank orglobalbound.
"""
import json,numpy as np
from scipy.optimize import linprog
from pathlib import Path
from local_cover_attack import x0,jac,grad
P=Path(__file__).resolve().parent
J=jac(x0);rot=np.eye(29)[19];A=np.vstack((J.T,np.zeros((0,24))))
# gradobjective=sum lambda gradconstraint +eta gradgauge
AA=np.column_stack((J.T,rot));w=linprog(np.zeros(25),A_eq=AA,b_eq=grad,bounds=[(0,None)]*24+[(None,None)],method='highs');assert w.success
# Firstordercriticaldirections obeydr²=0,gauge=0, all positive-support tightgradient=0.
poss=[];pool=[w.x]
for i in range(24):
 obj=np.zeros(25);obj[i]=-1;rr=linprog(obj,A_eq=AA,b_eq=grad,bounds=[(0,None)]*24+[(None,None)],method='highs');assert rr.success
 if rr.x[i]>1e-8:poss.append(i);pool.append(rr.x)
w=np.mean(pool,axis=0);M=np.vstack((J[poss],rot,grad));u,sv,v=np.linalg.svd(M,full_matrices=True);rank=sum(sv>1e-9);N=v[rank:].T
results=[]
for h in(1e-4,3e-5,1e-5):
 H=np.zeros((29,29))
 for k in range(29):
  delta=np.eye(29)[k]*h
  H[:,k]=-((jac(x0+delta)-jac(x0-delta)).T@w[:24])/(2*h)
 H=(H+H.T)/2;crit=N.T@H@N;ev=np.linalg.eigvalsh(crit)
 results.append({'fd_step':h,'critical_eigenvalues':ev.tolist()})
out={'status':'numeric_only','scope':'truecircumradiusboundary-switchbranch, arbitrary28sitecoordinates gaugefixed; nonstrictmultipliers needcriticalcone inequalities','gradient_rank':int(np.linalg.matrix_rank(J,tol=1e-9)),'positive_possible_constraints':poss,'zero_multiplier_constraints':[i for i in range(24)if i not in poss],'weights':w.tolist(),'stationarity_residual':float(max(abs(AA@w-grad))),'critical_linear_space_dimension':N.shape[1],'curvature_fd_controls':results}
(P/'local-cover-kkt-probe.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in('weights','curvature_fd_controls')});print(results)
