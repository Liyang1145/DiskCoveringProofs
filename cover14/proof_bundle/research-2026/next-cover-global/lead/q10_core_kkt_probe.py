"""Numeric reduced-core KKT regularity diagnostic, not exact rank proof."""
import json,numpy as np
from fixed_anchor_convex_probe import P
row=json.loads((P/'q10-relaxed-anchor-probe.json').read_text())['rows'][0]
D=np.array(row['incidence_matrix'],float); X=np.vstack([row['centers'],row['witnesses']]); off=np.array(row['offset']);z=np.array(row['flow_vectors'])
ids=[i for i in range(22)if i not in[8,9]]; edges=[k for k in range(44)if D[k,8]==0 and D[k,9]==0]
D=D[np.ix_(edges,ids)];v=(np.array(row['incidence_matrix'])@X+off)[edges]; norms=np.linalg.norm(v,axis=1)
lam=np.linalg.norm(z[edges],axis=1);lam/=sum(lam);r=row['radius']; # squaredlength multipliers approximately normalized
J=np.column_stack([(2*D[:,:,None]*v[:,None,:]).reshape(40,40),-np.ones(40)])
H=np.zeros((41,41));H[:40,:40]=2*np.kron(D.T@(lam[:,None]*D),np.eye(2))
K=np.block([[H,J.T],[J,np.zeros((40,40))]])
# full KKT has 41primalvars and40dualvars, unlike primalJ40x41
out=dict(status='numeric_only',edges=len(edges),freepoints=len(ids),Jshape=list(J.shape),Kshape=list(K.shape),min_multiplier=float(min(lam)),max_active_squared_residual=float(max(abs(norms**2-r*r))),J_singular_values=np.linalg.svd(J,compute_uv=False).tolist(),K_singular_values=np.linalg.svd(K,compute_uv=False).tolist(),H_free_eigenvalues=np.linalg.eigvalsh(H[:40,:40]).tolist(),stationarity_residual=float(max(abs(J.T@lam+np.r_[np.zeros(40),1.]))))
(P/'q10-core-kkt-probe.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if not isinstance(v,list)});print('Jmin',out['J_singular_values'][-1],'Kmin',out['K_singular_values'][-1],'Hmin',out['H_free_eigenvalues'][0])
