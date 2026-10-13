"""Numeric optimized affine dual-flow jet. Feasibility is linear balance only; not a certificate."""
import json,numpy as np
from scipy.linalg import null_space
from q10_core_kkt_probe import D,v,edges,row,P
ctl=json.loads((P/'q10-core-dual-control.json').read_text()); lam=np.array(ctl['stress']);r=row['radius']; A=np.array(row['anchors']);unit=v/np.linalg.norm(v,axis=1)[:,None];z=lam[:,None]*unit
# F(theta,z)=sum off(theta).z-r sum|z|. z restricted exactly to balance in futurecert.
N=null_space(np.kron(D.T,np.eye(2))); W=np.zeros((80,80));G=np.zeros((80,10));H=np.zeros((10,10))
for k,e in enumerate(edges):
 W[2*k:2*k+2,2*k:2*k+2]=r*(np.eye(2)-np.outer(unit[k],unit[k]))/lam[k]
 if e>=24:
  j=(e-24)//2;G[2*k:2*k+2,j]=np.array([A[j,1],-A[j,0]]);H[j,j]+=A[j]@z[k]
Q=N.T@W@N;mix=N.T@G; vals,vecs=np.linalg.eigh(Q);keep=vals>1e-8;pinv=(vecs[:,keep]/vals[keep])@vecs[:,keep].T
T=N@pinv@mix;gain=mix.T@pinv@mix;Hjet=H+gain
# Singular flowradialstressmodes produce compatibility/kink, so no differentiabilityconclusion.
nullmix=vecs[:,~keep].T@mix; constraints=np.vstack([np.ones(10),np.eye(10)[5]-np.eye(10)[4],np.eye(10)[0]-np.eye(10)[9],nullmix]);B=null_space(constraints,rcond=1e-9)
out=dict(status='numeric_only_affine_dual_jet',flow_balance=float(np.max(abs(D.T@z))),Q_eigenvalues=vals.tolist(),nullmix_singular_values=np.linalg.svd(nullmix,compute_uv=False).tolist(),critical_dimension=B.shape[1],critical_H_eigenvalues=np.linalg.eigvalsh(B.T@Hjet@B).tolist(),full_H_eigenvalues=np.linalg.eigvalsh(Hjet).tolist(),Hjet=Hjet.tolist(),jet=T.tolist(),baseflow=z.tolist(),edges=edges,critical_basis=B.tolist(),jet_balance=float(np.max(abs(np.kron(D.T,np.eye(2))@T))))
(P/'q10-adaptive-flow-jet.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in ['Q_eigenvalues','Hjet','jet','baseflow','edges','critical_basis']})
