"""Positive Dirichlet face radii: numeric solve and implicit derivatives.
Existence/uniqueness theorem in DIRICHLET-RADIUS-EXISTENCE.md; no interval certification here.
"""
import numpy as np
from scipy.optimize import least_squares

def evaluate(logr,beta,loga,edge_faces,anchor_ids):
 n=len(logr);m=len(beta);G=np.full(n,np.pi);H=np.zeros((n,n));B=np.zeros((n,m+len(loga)))
 for e,fs in enumerate(edge_faces):
  f=fs[0];g=fs[1] if len(fs)==2 else None
  lf=logr[f];lg=logr[g] if g is not None else loga[anchor_ids[e]]
  t=np.exp(lg-lf);sn=np.sin(beta[e]);cs=np.cos(beta[e]);den=1+t*t-2*t*cs
  hf=np.arctan2(t*sn,1-t*cs);w=t*sn/den
  G[f]-=hf;H[f,f]+=w;B[f,e]-=(t*cs-t*t)/den
  if g is not None:
   hg=np.pi-beta[e]-hf;G[g]-=hg;H[g,g]+=w;H[f,g]-=w;H[g,f]-=w
   B[g,e]+=(1-t*cs)/den
  else:B[f,m+anchor_ids[e]]-=w
 return G,H,B

def solve(beta,loga,edge_faces,anchor_ids,start=None):
 n=max(max(fs) for fs in edge_faces)+1
 if start is None:start=np.full(n,float(np.mean(loga)))
 f=lambda l:evaluate(l,beta,loga,edge_faces,anchor_ids)
 l=np.array(start,dtype=float)
 for iteration in range(60):
  G,H,B=f(l)
  if max(abs(G))<1e-12:break
  step=np.linalg.solve(H,-G); alpha=1.; score=float(G@G)
  for backtrack in range(30):
   trial=l+alpha*step;Gt=f(trial)[0]
   if float(Gt@Gt)<score:break
   alpha*=.5
  else:raise ValueError('inconclusive line search')
  l=trial
 G,H,B=f(l)
 if max(abs(G))>1e-10:raise ValueError(('inconclusive_numeric_solve',max(abs(G))))
 return l,-np.linalg.solve(H,B),float(max(abs(G)))

if __name__=='__main__':
 from coupled_primal_probe import *
 ef=[E[e]for e in edges];ai={k:bedges.index(e) for k,e in enumerate(edges) if len(E[e])==1}
 be=x0[:ne];la=np.log(x0[ne+nf:]);lr,J,res=solve(be,la,ef,ai)
 err=float(max(abs(np.exp(lr)-x0[ne:ne+nf])))
 rng=np.random.default_rng(1261);checks=[]
 for it in range(5):
  direction=rng.normal(size=ne+nb);direction/=np.linalg.norm(direction);eps=1e-6
  plus=solve(be+eps*direction[:ne],la+eps*direction[ne:],ef,ai,lr)[0]
  minus=solve(be-eps*direction[:ne],la-eps*direction[ne:],ef,ai,lr)[0]
  checks.append(float(max(abs((plus-minus)/(2*eps)-J@direction))))
 out={'status':'numeric_fixed_candidate_elimination_calibration','eliminated_positive_face_radii':nf,'remaining_parameters':ne+nb,'candidate_radius_error':err,'equation_residual':res,'implicit_derivative_directional_errors':checks,'min_anchor_log_derivative':float(J[:,ne:].min()),'anchor_scale_derivative_sum_error':float(max(abs(J[:,ne:].sum(axis=1)-1)))}
 assert err<1e-11 and max(checks)<1e-7 and out['min_anchor_log_derivative']>-1e-12
 (P/'dirichlet-radius-solver-control.json').write_text(json.dumps(out,indent=2));print(out)
