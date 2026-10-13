"""Bounded remote intrinsic geometry test for augmented stress;10k perturbations max."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,json,math,warnings
from scipy.special import logsumexp
warnings.filterwarnings('ignore')
P=Path(__file__).parent;z={'__file__':str(P/'angle_stress_probe.py')};exec((P/'angle_stress_probe.py').read_text().split('y0=np.zeros(29)')[0],z)
ns,shape,branches,lam,mu,act=[z[k] for k in ['ns','shape','branches','lam','mu','act']];base=ns['c'];faces=ns['faces'];a0=z['a0'];rng=np.random.default_rng(842)
def calc(a):
 r,c,d=shape(a)
 if min(d['alpha'])<=0 or max(d['alpha'])>=math.pi or min(d['w'])<=0 or max(d['w'])>=math.pi:return None
 g,c=branches(a);F=.1*logsumexp(g[act]*10,b=lam)+mu@c+sum(c[13:]**2)
 return F,c,r
b0=calc(a0)[0];sgn=[np.sign(np.linalg.det(np.array([base[f[1]]-base[f[0]],base[f[2]]-base[f[0]]]))) for f in faces];out={'scope':'finite physical-coordinate perturbations only, not global positivity certificate','trials':[]};count=0;best=None
for sigma in [.003,.01,.03,.06,.1]:
 vals=[];valid=0
 for k in range(2000):
  c=base+rng.normal(0,sigma,base.shape);a=[];bs=[];good=True
  for ff,f in enumerate(faces):
   p=c[f]
   if np.linalg.det(np.array([p[1]-p[0],p[2]-p[0]]))*sgn[ff]<=1e-8:good=False;break
   for i in range(3):
    u=p[(i+1)%3]-p[i];v=p[(i+2)%3]-p[i];a.append(math.acos(np.clip(u@v/np.linalg.norm(u)/np.linalg.norm(v),-1,1)))
  if not good:continue
  for i in range(9):
   j=(i+1)%9;d=np.linalg.norm(c[j]-c[i]);mid=(c[j]+c[i])/2;n=np.array([(c[j]-c[i])[1],-(c[j]-c[i])[0]])/d;disc=(mid@n)**2+1-mid@mid
   if disc<=0:good=False;break
   ll=-mid@n+math.sqrt(disc)+rng.normal(0,sigma)
   if ll<=0:good=False;break
   bs.append(math.atan2(d/2,ll))
  if not good:continue
  a=np.r_[a,bs];res=calc(a)
  if res is None:continue
  F,cons,R=res
  if max(abs(cons[:15]))>1e-10:continue
  valid+=1;v=float(F-b0);vals.append(v)
  if best is None or v<best['change']:best={'change':v,'sigma':sigma,'angles':a.tolist(),'nonlinear_residual':float(max(abs(cons[13:]))),'shape_radius':R}
 row={'sigma':sigma,'attempts':2000,'valid':valid,'min_change':min(vals) if vals else None};out['trials'].append(row);out['best']=best;(P/'nonlinear_stress_geometric.json').write_text(json.dumps(out,indent=2));print(row,flush=True)
