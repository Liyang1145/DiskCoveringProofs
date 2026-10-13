"""Primal finite-disk intersection calibration, independently from convex optimization."""
import numpy as np,json
from pathlib import Path
P=Path(__file__).parent

def candidates(C,R):
 out=[(x.copy(),('center',i)) for i,x in enumerate(C)]
 for i,p in enumerate(C):
  for j in range(i):
   q=C[j];d=np.linalg.norm(q-p);a,b=R[i],R[j]
   if d==0 or d<abs(a-b) or d>a+b:continue
   u=(q-p)/d;A=(a*a-b*b+d*d)/(2*d);B=np.sqrt(max(0,a*a-A*A));J=np.array([-u[1],u[0]])
   out.extend([(p+A*u+B*J,('pair',i,j)),(p+A*u-B*J,('pair',i,j))])
 return out

def test(C,R):
 cand=candidates(np.array(C),np.array(R));items=[(float(np.min(R-np.linalg.norm(C-x,axis=1))),x,tag)for x,tag in cand];return max(items,key=lambda z:z[0])
# Include containment and tangency to audit cases where area-based lens tests fail.
known=[('nested',[[0,0],[0,0]],[1,.5],True),('external-tangent',[[0,0],[2,0]],[1,1],True),('empty',[[0,0],[3,0]],[1,1],False),('lens',[[0,0],[1,0]],[1,1],True),('three-pairwise-only',[[0,0],[1.9,0],[.95,1.9*np.sqrt(3)/2]],[1,1,1],False)]
rows=[]
for name,C,R,ok in known:
 q=test(np.array(C,float),np.array(R,float));assert (q[0]>=-1e-13)==ok
 rows.append({'case':name,'max_candidate_min_slack':q[0],'feasible':ok})
raw=json.loads((P/'r21_residual_vertices_control.json').read_text())
for side in raw['sides']:
 C=np.vstack([[0.,0.],np.array(side['points'])]);R=np.r_[.62,np.full(len(C)-1,.38)];q=test(C,R)
 assert q[0]>=-1e-12
 rows.append({'case':f'candidate-side-{side["side"]}','min_slack':q[0],'hub':q[1].tolist(),'witness_type':q[2]})
(P/'r21_disk_intersection_control.json').write_text(json.dumps({'scope':'numeric controls for finite predicate; not certified n11 bound','cases':rows},indent=2))
print('five known disk-intersection cases, two candidate split predicates; all calibrated')
