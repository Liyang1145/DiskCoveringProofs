"""Exact verification that 23 radius-9/40 disks cover this finite point set."""
from fractions import Fraction as F
from pathlib import Path
import json
if not __debug__:raise RuntimeError('Run without -O')
p=Path(__file__).resolve().parent;data=json.loads((p/'five_ring_exact.json').read_text());sol=json.loads((p/'finite_cover_23.json').read_text());S=10**6;R=225000
P=[]
for x,y in data['points']:
 x=F(x)*S;y=F(y)*S;assert x.denominator==y.denominator==1
 X,Y=int(x),int(y);assert X*X+Y*Y<=S*S;P.append((X,Y))
assert data['radius']==sol['radius']=='9/40' and len(sol['selected_witnesses'])==23

def sign(a,b,z):
 assert z>=0
 if not b or not z:return (a>0)-(a<0)
 if not a:return (b>0)-(b<0)
 if (a>0)==(b>0):return (a>0)-(a<0)
 q=a*a-b*b*z
 return ((q>0)-(q<0))*((a>0)-(a<0))
covered=set()
for mask,wit in zip(sol['selected_masks'],sol['selected_witnesses']):
 i=wit['i'];x,y=P[i];captured=set()
 if wit['kind']=='point':
  for k,(u,v) in enumerate(P):
   if (u-x)**2+(v-y)**2<=R*R:captured.add(k)
 else:
  assert wit['kind']=='pair';j=wit['j'];sg=wit['sign'];assert i!=j and sg in (-1,1)
  xx,yy=P[j];dx=xx-x;dy=yy-y;D=dx*dx+dy*dy;T=4*R*R-D;assert D>0 and T>=0
  for k,(u,v) in enumerate(P):
   q=x+xx-2*u;s=y+yy-2*v
   a=(4*R*R-q*q-s*s-T)*D;b=sg*2*(q*dy-s*dx)
   if sign(a,b,D*T)>=0:captured.add(k)
 exact=sum(1<<k for k in captured)
 assert exact==int(mask,16)
 covered.update(captured)
assert covered==set(range(len(P)))
print('PASS:',len(P),'rational unit-disk points covered by 23 explicit radius-9/40 disks')
print('All input points and 23 centers certified with exact integer/square-root comparisons')
