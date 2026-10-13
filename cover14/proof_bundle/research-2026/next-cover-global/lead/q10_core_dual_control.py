"""Positive core stress and active-set compatibility; numeric only."""
import numpy as np,json
from scipy.optimize import linprog
from q10_core_kkt_probe import J,D,v,edges,ids,row,P
B=J.T; obj=np.r_[np.zeros(40),-1.];eq=np.c_[B,np.zeros(41)];beq=np.r_[np.zeros(40),-1.]
sol=linprog(obj,A_ub=np.c_[-np.eye(40),np.ones(40)],b_ub=np.zeros(40),A_eq=eq,b_eq=beq,bounds=[(None,None)]*40+[(0,None)],method='highs');assert sol.success
lam=sol.x[:40];H=np.zeros((41,41));H[:40,:40]=2*np.kron(D.T@(lam[:,None]*D),np.eye(2));K=np.block([[H,J.T],[J,np.zeros((40,40))]])
u,sv,vh=np.linalg.svd(J);left=u[:,-1];JT=np.zeros((40,10));A=np.array(row['anchors'])
for k,e in enumerate(edges):
 if e>=24:
  j=(e-24)//2;JA=np.array([-A[j,1],A[j,0]]);JT[k,j]=-2*v[k]@JA
compat=left@JT
# Linearized all-active equation J dx + JT dtheta=0 demands compat*dtheta=0.
out=dict(status='numeric_only',strictstress_min=float(min(lam)),stationarity_residual=float(max(abs(B@lam-beq))),stress=lam.tolist(),leftnull=left.tolist(),leftnull_residual=float(max(abs(left@J))),compatibility_angle_row=compat.tolist(),rotation_row_sum=float(sum(compat)),Hmin=float(np.linalg.eigvalsh(H[:40,:40])[0]),K_smallest=np.linalg.svd(K,compute_uv=False)[-5:].tolist())
(P/'q10-core-dual-control.json').write_text(json.dumps(out,indent=2));print(out)
