"""Numeric calibration of exact split-residual vertex lemma; not covering certificate."""
from pathlib import Path
import numpy as np,json
P=Path(__file__).parent
raw=json.loads(Path('n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
C=np.array([[int(v)/1e17 for v in a] for a in raw['centers_scaled_1e17']]); rings=C[[i for i in range(11) if i not in [0,2]]];a,b=C[[0,2]]
r=.38;n=(b-a)/np.linalg.norm(b-a);t=(b@b-a@a)/(2*np.linalg.norm(b-a))
pts=[]
for i,c in enumerate(rings):
 for d in rings[:i]:
  q=d-c;L=np.linalg.norm(q)
  if 0<L<2*r:
   m=(c+d)/2;u=np.array([-q[1],q[0]])/L;h=np.sqrt(r*r-L*L/4)
   pts.extend([(m+h*u,'pair'),(m-h*u,'pair')])
 z=t-n@c
 if abs(z)<r:
  m=c+z*n;u=np.array([-n[1],n[0]]);h=np.sqrt(r*r-z*z)
  pts.extend([(m+h*u,'line'),(m-h*u,'line')])
V=[]
for x,kind in pts:
 ds=np.linalg.norm(x-rings,axis=1)
 if np.linalg.norm(x)>1 or min(ds)<r-1e-12:continue
 # Strict local feasible direction calibration: avoids isolated equality trap.
 active=rings[abs(ds-r)<1e-10]; normals=(x-active)/r;direction=normals.sum(axis=0)
 if len(active) and min(normals@direction)<=1e-8:raise AssertionError('singular K membership needs analytic treatment')
 V.append((x,kind))
rng=np.random.default_rng(211);X=rng.uniform(-1,1,(120000,2));X=X[(X*X).sum(1)<=1];X=X[np.min(np.sum((X[:,None,:]-rings[None,:,:])**2,axis=2),axis=1)>r*r]
rows=[]
for sign in [-1,1]:
 W=np.array([x for x,k in V if sign*(n@x-t)>=-1e-12]);Y=X[sign*(X@n-t)>=0]
 assert len(W)>0 and len(Y)>0
 hs=np.vstack([a,b,rng.uniform(-.7,.7,(48,2))]);errs=[]
 for h in hs:errs.append(float(np.max(np.sum((Y-h)**2,axis=1))-np.max(np.sum((W-h)**2,axis=1))))
 assert max(errs)<=1e-10
 rows.append({'side':sign,'vertices':len(W),'residual_samples':len(Y),'max_sample_minus_vertex':max(errs),'points':W.tolist()})
# Equilateral equality trap: origin all distances=r, yet punctured |x|<r ring-covered.
# Independent exact formula: max_i u_i.x >= |x|/2 => min distance² <= r²+|x|²-r|x|.
(P/'r21_residual_vertices_control.json').write_text(json.dumps({'scope':'numeric calibration at rational saved centers, r=.38, actual-hub bisector, 50 query centers; no all-ring-domain certification','ring_max_norm':float(max(np.linalg.norm(rings,axis=1))),'line_normal':n.tolist(),'line_offset':float(t),'filtered_vertices':len(V),'sides':rows},indent=2))
print('split residual finite vertices:',[(q['vertices'],q['residual_samples'],q['max_sample_minus_vertex']) for q in rows])
