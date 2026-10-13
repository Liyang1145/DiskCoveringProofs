"""Bounded tau-design diagnostic; no constants promoted from numpy eigenvalues."""
import interval_network_envelope as k
import numpy as np,json
H=k.arr(k.H)[:8,:8];G=k.arr(k.G8);N=k.arr(k.N);alpha=k.arr(k.alpha).ravel();Lam=k.arr(k.Lam);X=np.array([[float(k.mid(v)) for v in x] for x in k.X]);U=X[:9];d=float(np.linalg.eigvalsh(Lam)[-1]);rows=[]
for tau in [.01,.03,.05,.1,.2,.5,1,2,5,10]:
 Q=tau*N@G.T;b=max(np.linalg.norm(Q,axis=1)/alpha);M=np.zeros((18,8))
 for e,(v,w) in enumerate(k.edges):
  for node,sgn in [(v,1),(w,-1)]:
   if node<9:M[2*node:2*node+2]+=sgn*np.outer(X[v]-X[w],Q[e])
 m=np.linalg.norm(M,2);mu=np.linalg.eigvalsh(H+2*tau*G@G.T)[0];C=d*(1+b)+m
 rows.append({'tau':tau,'mu_numeric':mu,'b_numeric':b,'m_op_numeric':m,'d_op_numeric':d,'rho_quarter_numeric':mu/(4*C)})
(k.P/'local_tau_diagnostic.json').write_text(json.dumps(rows,indent=2));print(rows)
