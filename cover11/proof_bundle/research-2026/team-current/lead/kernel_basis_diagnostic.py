"""Four basis designs, actual full Hessian and directional loss; numeric only."""
import interval_network_envelope as k
import numpy as np,json
N=k.arr(k.N);G=k.arr(k.G8);H=k.arr(k.H)[:8,:8];al=k.arr(k.alpha).ravel();X=np.array([[float(k.mid(v)) for v in x] for x in k.X]);flux=np.zeros((18,4))
for e,(v,w) in enumerate(k.edges):
 for node,sgn in [(v,1),(w,-1)]:
  if node<9:flux[2*node:2*node+2]+=sgn*np.outer(X[v]-X[w],N[e])
def power(A,p):
 val,V=np.linalg.eigh(A);return (V*val**p)@V.T
Rlist=[('identity',np.eye(4)),('Gwhite',power(G.T@G,-.5)),('Nwhite',power(N.T@N,-.5)),('relative',power(N.T@np.diag(1/al**2)@N,-.5))];rows=[];d=.08;cross=.0358
for name,R in Rlist:
 NN=N@R;GG=G@R;AA=flux@R;B=max(np.linalg.norm(NN,axis=1)/al);A=np.linalg.norm(AA,'fro');scale=np.linalg.norm(GG,2)**2
 for t in [.04,.1,.2,.4,1.]:
  tau0=t/scale;mu=np.linalg.eigvalsh(H+2*tau0*GG@GG.T)[0]
  if mu<=0:continue
  tau=2*tau0;quart=d/3+tau0*(B*d+A)**2;rho=(-cross+np.sqrt(cross**2+2*quart*mu))/(2*quart)
  rows.append({'name':name,'tau0':tau0,'mu':mu,'B':B,'A':A,'rho_numeric':rho,'positivity':tau*B*np.linalg.norm(GG,2)*rho,'R':R.tolist()})
rows.sort(key=lambda x:-x['rho_numeric']);(k.P/'kernel_basis_diagnostic.json').write_text(json.dumps(rows,indent=2));print([{k:v for k,v in r.items() if k!='R'} for r in rows[:6]])
