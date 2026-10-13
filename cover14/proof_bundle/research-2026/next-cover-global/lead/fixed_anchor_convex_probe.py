"""Numerical fixedanchor SOCP calibration through analytic norm Jacobians; no bound certification."""
import json,math,time,numpy as np
from pathlib import Path
from fractions import Fraction
from scipy.optimize import minimize
P=Path(__file__).resolve().parent

def solve_case(name,C,A,faces,owners,W0=None):
 n=len(C);nf=len(faces);nv=n+nf;N=2*nv+1;W=[]
 if W0 is None:
  for f in faces:
   a,b,c=C[f];W.append(np.linalg.solve(2*np.array([b-a,c-a]),np.array([b@b-a@a,c@c-a@a])))
 else:W=list(W0)
 X=np.vstack([C,W]);tail=[];head=[];anchor=[]
 for f,vs in enumerate(faces):
  for v in vs:tail.append(v);head.append(n+f);anchor.append(-1)
 for j,vs in enumerate(owners):
  for v in vs:tail.append(v);head.append(-1);anchor.append(j)
 tail=np.array(tail);head=np.array(head);anchor=np.array(anchor);m=len(tail);D=np.zeros((m,nv));D[np.arange(m),tail]=1;mask=head>=0;D[np.where(mask)[0],head[mask]]=-1;offset=np.zeros((m,2));offset[~mask]=-A[anchor[~mask]]
 def vectors(x):return D@x[:-1].reshape(nv,2)+offset
 def cons(x):return x[-1]-np.linalg.norm(vectors(x),axis=1)
 def jac(x):
  v=vectors(x);norm=np.linalg.norm(v,axis=1);u=v/np.maximum(norm[:,None],1e-100);J=-(D[:,:,None]*u[:,None,:]).reshape(m,2*nv);return np.column_stack([J,np.ones(m)])
 r0=np.max(np.linalg.norm(D@X+offset,axis=1));x0=np.r_[X.ravel(),r0+1e-9];obj=lambda x:x[-1];g=np.zeros(N);g[-1]=1;start=time.time();opt=minimize(obj,x0,jac=lambda x:g,method='SLSQP',constraints=[{'type':'ineq','fun':cons,'jac':jac}],options={'maxiter':150,'ftol':1e-12});x=opt.x;J=jac(x);mult=np.maximum(0,np.array(opt.multipliers));v=vectors(x);z=mult[:,None]*v/np.maximum(np.linalg.norm(v,axis=1)[:,None],1e-100);balance=D.T@z;num=float(np.sum(offset*z));den=float(np.linalg.norm(z,axis=1).sum());dual=num/den
 out={'status':'numeric_only_fixedanchor_convex_calibration','case':name,'success':bool(opt.success),'message':str(opt.message),'iterations':int(opt.nit),'initial_radius':r0,'radius':float(x[-1]),'min_constraint':float(min(cons(x))),'dual_proposal_value':dual,'dual_force_residual':float(np.max(abs(balance))),'seconds':time.time()-start,'centers':x[:2*n].reshape(n,2).tolist(),'witnesses':x[2*n:-1].reshape(nf,2).tolist(),'anchors':A.tolist(),'faces':faces,'owners':owners,'flow_vectors':z.tolist(),'incidence_matrix':D.astype(int).tolist(),'offset':offset.tolist()};print({k:v for k,v in out.items()if k not in ['centers','witnesses','anchors','faces','owners','flow_vectors','incidence_matrix','offset']},flush=True);return out
if __name__=='__main__':
 out=[];G=json.loads((P/'stress-barycentric-result.json').read_text());D=json.loads((P/'improved-upper-test.json').read_text());C=np.array([[float(Fraction(x))for x in p]for p in D['centers']]);A=np.array([[math.cos(float(a['theta'])),math.sin(float(a['theta']))]for a in G['anchors']]);faces=[f['ids']for f in G['faces']]+[[4,6,12],[5,7,13]];owners=[a['owners']for a in G['anchors']];out.append(solve_case('candidate',C,A,faces,owners));(P/'fixed-anchor-convex-probe.json').write_text(json.dumps({'runs':out},indent=2))
 Q=json.loads((P/'q11-cartesian-replay.json').read_text());faces=json.loads((P/'q11-pocket-catalogue.json').read_text())['entries'][58]['faces'];owners=[[i,(i+1)%11]for i in range(11)];out.append(solve_case('q11-58',np.array(Q['centers']),np.array(Q['anchors']),faces,owners));(P/'fixed-anchor-convex-probe.json').write_text(json.dumps({'runs':out},indent=2))
