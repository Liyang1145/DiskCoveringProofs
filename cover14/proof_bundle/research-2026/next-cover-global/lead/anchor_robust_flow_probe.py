"""Convex robustdual design: maximize minimum globalTaylor vertexbound; two controls."""
from fixed_anchor_convex_probe import *
from scipy.linalg import null_space
import sys

def solve(row,q,mode='taylor',simplex=None,angle_vertices=None):
 D=np.array(row['incidence_matrix']);Z0=np.array(row['flow_vectors']);N=null_space(D.T);k=N.shape[1];nf=len(row['faces']);B=np.zeros((q,len(D)))
 for j in range(q):B[j,3*nf+2*j:3*nf+2*j+2]=-1
 BN=B@N;theta=2*math.pi*np.arange(q)/q;A=np.c_[np.cos(theta),np.sin(theta)];Tangent=np.c_[-np.sin(theta),np.cos(theta)];L=2*math.asin(.33173203427623414);delta=q*L-2*math.pi;VV=[]
 for i in range(q):
  for j in (range(q)if q==11 else [-1]):
   if j==i:continue
   d=np.zeros(q)
   if q==10:d[i]=delta
   else:d[i]=L;d[j]=delta-L
   VV.append(np.arange(q)*L-np.r_[0,np.cumsum(d[:-1])])
 if simplex is not None:
  assert q==10;VV=[np.arange(q)*L-delta*np.r_[0,np.cumsum(v[:-1])]for v in np.array(simplex)]
  theta=np.mean(VV,axis=0);A=np.c_[np.cos(theta),np.sin(theta)];Tangent=np.c_[-np.sin(theta),np.cos(theta)]
 if angle_vertices is not None:
  VV=angle_vertices;theta=np.mean(VV,axis=0);A=np.c_[np.cos(theta),np.sin(theta)];Tangent=np.c_[-np.sin(theta),np.cos(theta)]
 dt=np.array(VV)-theta;H=A[None,:,:]+dt[:,:,None]*Tangent[None,:,:];pen=.5*dt**2
 if mode=='concave':
  TT=np.array(VV);H=np.stack([np.cos(TT),np.sin(TT)],axis=2);pen=np.zeros_like(dt);lo=TT.min(axis=0);hi=TT.max(axis=0);assert max(hi-lo)<math.pi;EH=np.stack([np.c_[np.cos(lo),np.sin(lo)],np.c_[np.cos(hi),np.sin(hi)]])
 X=N.T@Z0;X/=np.linalg.norm(N@X,axis=1).sum();x0=np.r_[X.ravel(),.2]
 def calc(x,jac=False):
  X=x[:-1].reshape(k,2);Z=N@X;G=BN@X;zn=np.linalg.norm(Z,axis=1);gn=np.linalg.norm(G,axis=1);vals=np.einsum('vji,ji->v',H,G)-pen@gn-x[-1];c=np.r_[1-zn.sum(),vals]
  if mode=='concave':c=np.r_[c,np.einsum('hji,ji->hj',EH,G).ravel()]
  if not jac:return c
  Ju=-(N.T@(Z/np.maximum(zn[:,None],1e-30))).ravel();GG=H-pen[:,:,None]*G[None,:,:]/np.maximum(gn[None,:,None],1e-30);Jv=np.einsum('jk,vji->vki',BN,GG).reshape(len(VV),-1);JJ=np.block([[Ju[None,:],np.zeros((1,1))],[Jv,-np.ones((len(VV),1))]])
  if mode=='concave':
   EP=np.einsum('jk,hji->hjki',BN,EH).reshape(2*q,2*k);JJ=np.vstack([JJ,np.c_[EP,np.zeros(2*q)]])
  return JJ
 grad=np.r_[np.zeros(2*k),-1.];rr=minimize(lambda x:-x[-1],x0,jac=lambda x:grad,method='SLSQP',constraints=[{'type':'ineq','fun':calc,'jac':lambda x:calc(x,True)}],options={'maxiter':200,'ftol':2e-12});Z=N@rr.x[:-1].reshape(k,2);out=dict(row);out['flow_vectors']=Z.tolist();out['anchors']=A.tolist();out.update(robust_value=float(rr.x[-1]),robust_success=bool(rr.success),robust_min_constraint=float(min(calc(rr.x))),robust_iterations=int(rr.nit));print({a:out[a]for a in ['case','robust_value','robust_success','robust_min_constraint','robust_iterations']},flush=True);return out
if __name__=='__main__':
 data=json.loads((P/'anchor-simplex-q10-catalogue-probe.json').read_text())['runs'];out=[]
 for idx in map(int,sys.argv[1:]or['541','878']):out.append(solve(next(r for r in data if r['index']==idx),10));(P/'anchor-robust-flow-probe.json').write_text(json.dumps({'status':'numeric_robust_flow_proposals','runs':out},indent=2))
