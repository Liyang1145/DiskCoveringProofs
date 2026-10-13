"""Numeric independent geometry calibration of safearea decomposition on savedactualcover."""
import json,math,numpy as np
from itertools import combinations
from pathlib import Path
from fractions import Fraction
P=Path(__file__).resolve().parent
D=json.loads((P/'improved-upper-test.json').read_text());G=json.loads((P/'stress-barycentric-result.json').read_text())
C=np.array([[float(Fraction(x))for x in p]for p in D['centers']]);r=float(D['threshold_decimal']);faces=[x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]]
def angle(u,v):return math.atan2(abs(float(np.linalg.det(np.array([u,v])))),float(u@v))
W={}
for f in faces:
 p,q,v=C[f];w=np.linalg.solve(2*np.array([q-p,v-p]),np.array([q@q-p@p,v@v-p@p]));assert np.linalg.norm(w)<1
 ds=np.sum((C-w)**2,axis=1);assert max(ds[f])-min(ds)<1e-12
 for e in combinations(f,2):W.setdefault(tuple(sorted(e)),[]).append(w)
owneranchors={};boundary=[]
for a in G['anchors']:
 w=np.array([math.cos(float(a['theta'])),math.sin(float(a['theta']))]);e=tuple(sorted(a['owners']));W[e].append(w)
 for i in e:owneranchors.setdefault(i,[]).append(w)
angles=np.zeros(14);area=0;pairbound=0;congruence=0
for e,ww in W.items():
 assert len(ww)==2
 x,y=ww;bs=[]
 for i in e:
  u,v=x-C[i],y-C[i];beta=angle(u,v);angles[i]+=beta;bs.append(beta);area+=abs(float(np.linalg.det(np.array([u,v]))))/2
 congruence=max(congruence,abs(bs[0]-bs[1]));pairbound+=r*r*math.sin(bs[0])
capactual=0;trianglebound=0;alphas=[]
for i,ww in owneranchors.items():
 assert len(ww)==2
 x,y=ww;alpha=angle(x-C[i],y-C[i]);theta=angle(x,y);assert theta<=2*math.asin(r)+1e-12
 alphas.append(alpha);angles[i]+=alpha;area+=abs(float(np.linalg.det(np.array([x-C[i],y-C[i]]))))/2+(theta-math.sin(theta))/2
 capactual+=(theta-math.sin(theta))/2;trianglebound+=r*r*math.sin(alpha)/2
capbound=math.pi*(1-math.sin(2*math.asin(r))/(2*math.asin(r)))
assert max(abs(angles-2*math.pi))<1e-12 and abs(area-math.pi)<1e-12 and congruence<1e-12
assert pairbound+trianglebound+capbound>=area
out={'status':'numeric_geometry_controls_only','object':'C1148savedrationalcover','edges':len(W),'faces':len(faces),'area':area,'angle_sum_max_residual':max(abs(angles-2*math.pi)),'congruence_angle_residual':congruence,'boundary_view_angles':alphas,'boundary_view_angle_sum':sum(alphas),'actual_cap_area':capactual,'cap_bound':capbound,'evaluated_safe_area_bound':pairbound+trianglebound+capbound}
(P/'area-safe-geometry-control.json').write_text(json.dumps(out,indent=2));print(out)
