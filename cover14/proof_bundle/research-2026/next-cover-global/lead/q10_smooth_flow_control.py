"""Bounded convexsmoothnorm control; only exact repaired-flow certificates are bearing."""
from anchor_robust_flow_probe import *
from q11_chord_flow_certificate import bound
from q11_chord_flow_fraction_replay import replay
from q10_polytope_partition_probe import Q,iv,S,L
from scipy.optimize import LinearConstraint

def smooth(row,TT,eps=1e-8):
 D=np.array(row['incidence_matrix']);N=null_space(D.T);k=N.shape[1];nf=len(row['faces']);B=np.zeros((10,len(D)))
 for j in range(10):B[j,3*nf+2*j:3*nf+2*j+2]=-1
 BN=B@N;lo=TT.min(axis=0);hi=TT.max(axis=0);H=np.stack([np.cos(TT),np.sin(TT)],axis=2);EH=np.stack([np.c_[np.cos(lo),np.sin(lo)],np.c_[np.cos(hi),np.sin(hi)]]);Jv=np.einsum('jk,vji->vki',BN,H).reshape(len(TT),-1);EP=np.einsum('jk,hji->hjki',BN,EH).reshape(20,2*k);M=np.vstack([np.c_[Jv,-np.ones(len(TT))],np.c_[EP,np.zeros(20)]]);X=N.T@np.array(row['flow_vectors']);X/=np.sqrt(np.sum((N@X)**2,axis=1)+eps**2).sum();x0=np.r_[X.ravel(),min(Jv@X.ravel())];grad=np.r_[np.zeros(2*k),-1.]
 def budget(x):return 1-np.sqrt(np.sum((N@x[:-1].reshape(k,2))**2,axis=1)+eps**2).sum()
 def jac(x):
  Z=N@x[:-1].reshape(k,2);zn=np.sqrt(np.sum(Z**2,axis=1)+eps**2);return np.r_[-(N.T@(Z/zn[:,None])).ravel(),0.]
 rr=minimize(lambda x:-x[-1],x0,jac=lambda x:grad,method='SLSQP',constraints=[LinearConstraint(M,0,np.inf),{'type':'ineq','fun':budget,'jac':jac}],options={'maxiter':400,'ftol':1e-12});Z=N@rr.x[:-1].reshape(k,2);out=dict(row);out['flow_vectors']=Z.tolist();tt=TT.mean(axis=0);out['anchors']=np.c_[np.cos(tt),np.sin(tt)].tolist();out.update(smooth_value=float(rr.x[-1]),smooth_success=bool(rr.success),smooth_iterations=int(rr.nit),smooth_min_constraint=float(min(budget(rr.x),min(M@rr.x))));return out
if __name__=='__main__':
 a=json.loads((P/'q10-polytope-partition-879.json').read_text());ss=[n for n in a['nodes']if n.get('status')=='split'];out=[]
 for n in [ss[0],a['nodes'][51],ss[-1]]:
  V=np.array([[float(iv(tuple(map(Q,t))).lo/S)for t in v]for v in n['polytope']['vertex_set']]);TT=np.arange(10)*float(L.lo/S)-np.c_[np.zeros(len(V)),np.cumsum(V[:,:-1],axis=1)];r=smooth(n['flow_proposal'],TT);c=bound(r,{'vertices':n['polytope']['vertex_set']});rr=replay(c);out.append({'node':n['id'],'old':n['flow_proposal']['robust_value'],'proposal':r,'certificate':c,'replay':rr});print('SMOOTH',n['id'],n['flow_proposal']['robust_value'],r['smooth_value'],c['lower_radius_display'],r['smooth_success'],r['smooth_iterations'],flush=True)
 (P/'q10-smooth-flow-control.json').write_text(json.dumps({'status':'three_fixedcell_controls_coverage_pending','runs':out},indent=2))
