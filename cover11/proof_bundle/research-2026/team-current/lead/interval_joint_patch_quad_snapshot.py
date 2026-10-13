"""Natural directedinterval jointpatch, all7physicalcoordinates. Broad domain, exactrationalz.
Scope necessarylocalflatpatch relaxation. Every rejectedbox has an explicitnecessarypredicate.
"""
from pathlib import Path
from mpmath import iv
import json,math
P=Path(__file__).parent;iv.dps=25
frozen=P/'joint_nested_frozen.json';j=json.loads(frozen.read_text());z=[iv.mpf(f'{v:.9f}')for v in j['z']];assert all(x==0 for x in z[50:73]);R=iv.mpf(19)/50;pi=iv.pi;g=2*pi-16*iv.asin(R) if hasattr(iv,'asin') else None
I=lambda a,b=None:iv.mpf(a if b is None else [a,b])
def asin(x):return iv.atan2(x,iv.sqrt(1-x*x))
def acos(x):return pi/2-asin(x)
g=2*pi-16*asin(R)
def lf(x):return math.nextafter(float(x.a),-math.inf)
def uf(x):return math.nextafter(float(x.b),math.inf)
def clip(x,l,h):
 l=I(l);h=I(h);a=max(x.a,l.a);b=min(x.b,h.b)
 return None if a>b else I(a,b)
def pos(x):return I(max(I(0).a,x.a),max(I(0).a,x.b))
def quad_range(a,b,x):
 # Pointintervalcoefficients; enclosurebyendpoint evaluations+stationaryvalue ifrelevant.
 va=a*I(x.a)**2+b*I(x.a);vb=a*I(x.b)**2+b*I(x.b)
 low=min(va.a,vb.a);high=max(va.b,vb.b)
 if a.a>0 or a.b<0:
  peak=-b/(2*a)
  if peak.b>=x.a and peak.a<=x.b:
   val=-b*b/(4*a);low=min(low,val.a);high=max(high,val.b)
 else:
  raw=a*x*x+b*x;low=min(low,raw.a);high=max(high,raw.b)
 return I(low,high)
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def sector(r,s,b,w,ii):
 # local chart neighbor fixed c, endpointP1, predecessorP0 clockwise w
 cb=iv.cos(b);sb=iv.sin(b);c=[s-2*r*sb*cb,-2*r*sb*sb];p1=[s,-r];cw=iv.cos(w);sw=iv.sin(w);p0=[s*cw-r*sw,-s*sw-r*cw]
 v0=[p0[k]-c[k]for k in range(2)];v1=[p1[k]-c[k]for k in range(2)]
 d2=clip(dot(v0,v0),(R*I(19)/100)**2,r*r)
 if d2 is None:return None
 orient=cross(v0,v1)
 if orient.b<0:return None
 # orientationnonnegative exactnecessary. Use (physical) sectortriangle area directly.
 orient=pos(orient);alpha=iv.atan2(orient,dot(v0,v1));u=iv.sqrt(d2)/R
 chord=[p1[k]-p0[k]for k in range(2)];back=[-x for x in v0]
 # L angle atP0 between c-P0 andP1-P0
 lc=cross(chord,back)
 if lc.b<0:return None
 L=iv.atan2(pos(lc),dot(chord,back))
 mu,h,d,dl=(z[1],z[112],z[34],z[96])if ii==1 else(z[3],z[115],z[39],z[101])
 return orient/2+(w-iv.sin(w))/2-mu*alpha+quad_range(-d,-dl,u)+h*(L+w/2)
def evaluate(box,filters=True):
 r,b1,b2,A,w1,w3,H=box;s=iv.sqrt(1-r*r);B=b1+b2-A;bc=acos(r)
 B=clip(B,0,pi)
 if B is None:return None
 if filters:
  for b,w in [(b1,w1),(b2,w3)]:
   if b.b<(bc/2).a or b.a>bc.b:return None
   X=-r*iv.cos(2*b+asin(r));D=s*s-2*s*r*iv.sin(b)*iv.cos(b)+2*r*r*iv.sin(b)**2
   if X.b<0:return None
   W=2*iv.atan2(pos(X),D)
   if w.a>W.b:return None
  de=b1-A
  # hubnorm and siteface radiusbounds (D H triangle)
  if (H*H-2*s*iv.cos(de)*H+2*r*(1-r)).a>0:return None
  for b,th in [(b1,A),(b2,B)]:
   dd=2*r*iv.sin(b)
   if (H*H+dd*dd-2*H*dd*iv.cos(th)-4*r*r*iv.sin(th)**2).a>0:return None
 # Hvalue: positive triangleheight, denominator no zero inactualmodels (C840 pairseparation)
 hvalue=I(0)
 for b,th,az,bz,gz in [(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]:
  dd=2*r*iv.sin(b);yy=dd*iv.sin(th);xx=H-dd*iv.cos(th);yy=pos(yy)
  lsq=clip(xx*xx+yy*yy,I(1)/50000**2,4*r*r)
  if lsq is None:return None
  ang=iv.atan2(yy,xx);ee=iv.sqrt(lsq)/(2*R)
  hvalue+=H*yy/2+az*ang+quad_range(bz,gz,ee)
 f=sector(r,s,b1,w1,1);gg=sector(r,s,b2,w3,3)
 if f is None or gg is None:return None
 w2=2*asin(r)
 K=pi*(z[113]+z[114]-z[2])+z[1]*(b1-pi+A)+z[3]*(b2-pi+B)+(w2-iv.sin(w2))/2+r*r*(iv.sin(2*b1)+iv.sin(2*b2))/2
 return K+hvalue+f+gg
# Broadclosedboxcoversallactualparameters; rupperenlarged .38.
domain=[(lf(I(3)/8),uf(R)),(lf(acos(R)/2),uf(acos(I(3)/8))),(lf(acos(R)/2),uf(acos(I(3)/8))),(0,uf(2*acos(I(3)/8))),(lf(g),uf(2*asin(R))),(lf(g),uf(2*asin(R))),(0,uf(2*R))]
if __name__=='__main__':
 print('root',evaluate([I(l,h)for l,h in domain]))
