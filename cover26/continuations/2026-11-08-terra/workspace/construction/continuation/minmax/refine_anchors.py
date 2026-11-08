import json,math
from fractions import Fraction as F
from pathlib import Path
p=Path(__file__).parent;d=json.loads((p/'rational_geometry.json').read_text());C=[tuple(map(F,x)) for x in d['centers']];R=F(d['radius']);Q=[tuple(map(F,x)) for x in d['boundary_anchors']]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def sub(a,b):return a[0]-b[0],a[1]-b[1]
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def maker(q,delta):
 th=math.atan2(float(q[1]),float(q[0]))+delta;x=math.cos(th);y=math.sin(th)
 if x>-.5:
  t=F(round(y/(1+x)*10**13),10**13);return ((1-t*t)/(1+t*t),2*t/(1+t*t))
 t=F(round(y/(1-x)*10**13),10**13);return ((t*t-1)/(1+t*t),2*t/(1+t*t))
for delta in (1.1e-9,1.2e-9,1.3e-9,1.4e-9,1.5e-9,1.6e-9,1.7e-9,1.8e-9,1.9e-9):
 qs=Q.copy()
 for i in (0,8): qs[i]=maker(Q[i],-delta)
 for i in (7,15): qs[i]=maker(Q[i],delta)
 good=all(dot(sub(qs[i],C[j]),sub(qs[i],C[j]))<=R*R for i in (0,7,8,15) for j in (i,(i+1)%16))
 crossgood=all(cross(sub(qs[i],qs[(i-1)%16]),sub(C[i],qs[(i-1)%16]))>0 for i in (0,8))
 print(delta,good,crossgood)
 if good and crossgood:
  d['boundary_anchors']=[[str(x),str(y)] for x,y in qs]; (p/'rational_geometry.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf8');break

