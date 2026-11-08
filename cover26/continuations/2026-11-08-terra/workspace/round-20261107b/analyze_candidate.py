"""Numerical contact reconnaissance; this is not a proof certificate."""
from pathlib import Path
from fractions import Fraction
import json,math
import numpy as np
from scipy.spatial import Delaunay

ROOT=Path(__file__).resolve().parent.parent
data=json.loads((ROOT/'minmaxarena/n26-origin-certificate.json').read_text())
C=np.array([[float(Fraction(z)) for z in p] for p in data['centers']])
axis=C[16]/np.linalg.norm(C[16]);rot=np.array([axis,[-axis[1],axis[0]]])
C=C@rot.T
R=float(data['radius'])
print('rotated centers',json.dumps(C.tolist()))
print('reflection errors',max(min(np.linalg.norm(C-p,axis=1)) for p in C*np.array([1,-1])))
orbit=lambda p:tuple(sorted((tuple(np.round(np.abs(C[i]),7)) for i in p)))
def circum(indices):
    a,b,c=C[list(indices)]
    p=np.linalg.solve(2*np.array([b-a,c-a]),np.array([b@b-a@a,c@c-a@a]))
    return p,np.linalg.norm(p-a)
active={}
for tri in Delaunay(C).simplices:
    p,r=circum(tri)
    if np.linalg.norm(p)>1:continue
    active.setdefault(orbit(tri),[]).append({'sites':sorted(map(int,tri)), 'radius':r,'center':p.tolist()})
print('interior orbits',json.dumps(list(active.values()),indent=2))
print('boundary radials',[(i,float(np.linalg.norm(C[i])),math.sqrt(1-R*R)) for i in range(5)])
rows=[]
for i in range(4):
    a,b=C[i],C[i+1];v=b-a;ll=v@v;h=(b@b-a@a)/2
    foot=h*v/ll
    delta=1-foot@foot
    tangent=np.array([-v[1],v[0]])*math.sqrt(delta/ll)
    p=max([foot+tangent,foot-tangent],key=lambda z:z[0]+z[1])
    rows.append({'sites':[i,i+1],'point':p.tolist(),'radius':float(np.linalg.norm(p-a))})
print('boundary contacts',json.dumps(rows,indent=2))
out={'rotated_centers':C.tolist(),'radius':R,'interior_orbits':list(active.values()),'boundary_contacts':rows}
(Path(__file__).resolve().parent/'numerical_contacts.json').write_text(json.dumps(out,indent=2))
