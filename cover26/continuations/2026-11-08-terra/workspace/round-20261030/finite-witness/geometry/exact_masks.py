"""One exploratory instance. Geometry generation/acceptance uses Python integers.
Decimal points rounded inward; no floating-point is used in mask acceptance.
"""
from fractions import Fraction as F
from pathlib import Path
import math,json,time
p=Path(__file__).resolve().parent;r=225000;scale=10**6
rings=[(999999,80),(800000,64),(600000,48),(400000,32),(200000,16)]
P=[(round(rho*math.cos(2*math.pi*(k+(j%2)*.5)/n)),round(rho*math.sin(2*math.pi*(k+(j%2)*.5)/n))) for j,(rho,n) in enumerate(rings) for k in range(n)]+[(0,0)]
assert all(x*x+y*y<=scale*scale for x,y in P) and len(set(P))==len(P)
def sgn(a,b,z):
 if b==0 or z==0:return (a>0)-(a<0)
 if a==0:return (b>0)-(b<0)
 if (a>0)==(b>0):return (a>0)-(a<0)
 v=a*a-b*b*z
 return ((v>0)-(v<0))*((a>0)-(a<0))
masks=set(); witness={};t=time.monotonic()
for i,(x,y) in enumerate(P):
 bits=0
 for k,(u,v) in enumerate(P):
  if (x-u)**2+(y-v)**2<=r*r:bits|=1<<k
 masks.add(bits);witness[bits]={"kind":"point","i":i}
count=0
for i,(x,y) in enumerate(P):
 for j,(x2,y2) in enumerate(P[:i]):
  dx=x2-x;dy=y2-y;D=dx*dx+dy*dy;T=4*r*r-D
  if T<0:continue
  assert D>0
  z=T*D;plus=0;minus=0
  for k,(u,v) in enumerate(P):
   q=x+x2-2*u;s=y+y2-2*v
   a=(4*r*r-q*q-s*s-T)*D; b=2*(q*dy-s*dx)
   if sgn(a,b,z)>=0:plus|=1<<k
   if sgn(a,-b,z)>=0:minus|=1<<k
  masks.add(plus);masks.add(minus);witness[plus]={"kind":"pair","i":i,"j":j,"sign":1};witness[minus]={"kind":"pair","i":i,"j":j,"sign":-1};count+=1
ordered=sorted(masks,key=int.bit_count,reverse=True);inv=[set() for _ in P];kept=[]
for bits in ordered:
 indices=[i for i in range(len(P)) if bits>>i&1]; short=min((inv[i] for i in indices),key=len)
 if any(bits&kept[j]==bits for j in short):continue
 j=len(kept);kept.append(bits)
 for i in indices:inv[i].add(j)
# Canonical order, and origin-denominated coordinates.
result={'radius':'9/40','points':[[str(F(x,scale)),str(F(y,scale))] for x,y in P],
 'masks':[hex(x) for x in sorted(kept)],'geometry_scope':'All real centers: point centers and both exact radius-9/40 circle-boundary intersections for each distinct sample pair at separation <=2r; singleton cases included. All mask membership and dominance integer-exact.',
 'mask_witnesses':{hex(x):witness[x] for x in sorted(kept)},
 'pair_count':count,'candidate_unique_masks':len(masks),'maximal_masks':len(kept)}
(p/'five_ring_exact.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
print('PASS exact masks',len(P),'points',count,'pairs',len(masks),'unique',len(kept),'maximal','seconds',round(time.monotonic()-t,2),flush=True)

