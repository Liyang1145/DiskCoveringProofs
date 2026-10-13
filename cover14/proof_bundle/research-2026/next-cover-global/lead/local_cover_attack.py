"""Bounded attack: try falsifying arbitrary-center local optimality of C1167.
Fixed physical Voronoi branch only. 8 deterministic perturbations, maxiter400.
No convergence/localminimum inference from failure; if lowercandidate checkfullD separately.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,time,itertools
import numpy as np
from pathlib import Path
from fractions import Fraction
from scipy.optimize import minimize
P=Path(__file__).resolve().parent
D=json.loads((P/'improved-upper-test.json').read_text());G=json.loads((P/'stress-barycentric-result.json').read_text())
C0=np.array([[float(Fraction(x))for x in p]for p in D['centers']]);r0=float(D['threshold_decimal'])
faces=np.array([f['ids']for f in G['faces']]);pairs=np.array([a['owners']for a in G['anchors']]);theta=np.array([float(a['theta'])for a in G['anchors']]);ref=np.c_[np.cos(theta),np.sin(theta)]

def quantities(C):
 p=C[pairs[:,0]];q=C[pairs[:,1]];dv=q-p;nn=np.sum(dv*dv,axis=1);k=(np.sum(q*q,axis=1)-np.sum(p*p,axis=1))/2
 base=dv*(k/nn)[:,None];orth=np.c_[-dv[:,1],dv[:,0]];rad=(1-np.sum(base*base,axis=1))/nn
 # complex step derivative-compatible; choose branch using reference orientation not perturbedcomparison.
 signs=np.sign(np.sum(orth0*(ref-base0),axis=1))
 anchors=base+orth*(signs*np.sqrt(rad))[:,None]
 boundary=np.sum((anchors-p)**2,axis=1)
 p=C[faces[:,0]];q=C[faces[:,1]];v=C[faces[:,2]];u=q-p;w=v-p
 rhs1=(np.sum(q*q,axis=1)-np.sum(p*p,axis=1))/2;rhs2=(np.sum(v*v,axis=1)-np.sum(p*p,axis=1))/2
 det=u[:,0]*w[:,1]-u[:,1]*w[:,0]
 centers=np.c_[(rhs1*w[:,1]-u[:,1]*rhs2)/det,(u[:,0]*rhs2-rhs1*w[:,0])/det]
 radii=np.sum((centers-p)**2,axis=1)
 return np.r_[boundary,radii]
p=C0[pairs[:,0]];q=C0[pairs[:,1]];dv=q-p;nn=np.sum(dv*dv,axis=1);k=(np.sum(q*q,axis=1)-np.sum(p*p,axis=1))/2;base0=dv*(k/nn)[:,None];orth0=np.c_[-dv[:,1],dv[:,0]]
def con(x):return x[-1]-quantities(x[:-1].reshape(14,2))
def jac(x):
 J=np.zeros((24,29));J[:,-1]=1
 for j in range(28):
  xx=x.astype(complex);xx[j]+=1e-25j;J[:,j]=np.imag(con(xx))/1e-25
 return J
x0=np.r_[C0.ravel(),r0*r0];grad=np.r_[np.zeros(28),1.]
# Rotationgauge: keep X+ y=0 (index9), exactconstraint.
eq={'type':'eq','fun':lambda x:x[19],'jac':lambda x:np.eye(29)[19]}
assert max(abs(con(x0)))<1e-14
JJ=jac(x0);hh=1e-6;fd=(con(x0+hh*np.eye(29)[2])-con(x0-hh*np.eye(29)[2]))/(2*hh)
assert max(abs(fd-JJ[:,2]))<1e-8
if __name__=='__main__':
 out={'status':'numeric_only','scope':'local24-contactbranch perturbation attack; no certifiedminimum','initial_radius':r0,'calibration_residual':float(max(abs(con(x0)))),'runs':[]}
 rng=np.random.default_rng(142026);start=time.time()
 for run in range(8):
  xx=x0.copy();scale=[.001,.01][run//4];xx[:28]+=rng.normal(size=28)*scale;xx[19]=0;xx[-1]+=scale
  res=minimize(lambda x:x[-1],xx,jac=lambda x:grad,method='SLSQP',constraints=[{'type':'ineq','fun':con,'jac':jac},eq],bounds=[(v-.06,v+.06)for v in x0[:28]]+[(.10,.13)],options={'maxiter':400,'ftol':2e-14,'disp':False})
  rec={'run':run,'perturbation':scale,'success':bool(res.success),'message':str(res.message),'iterations':res.nit,'radius':float(np.sqrt(res.x[-1])),'min_constraint':float(min(con(res.x))),'max_center_change':float(max(abs(res.x[:28]-x0[:28]))),'centers':res.x[:28].reshape(14,2).tolist()}
  out['runs'].append(rec);print({k:v for k,v in rec.items()if k!='centers'},flush=True)
  (P/'local-cover-attack.json').write_text(json.dumps(out,indent=2))
  if rec['radius']<r0-1e-9 and rec['min_constraint']>-1e-10:print('LOWER CANDIDATE NEED FULL COVER CHECK',flush=True);break
 print('DONE seconds',time.time()-start,flush=True)
