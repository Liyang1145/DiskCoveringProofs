"""Six-variable coupled smooth boundary objective. No physical derivative clipping."""
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt,atan2,asin
from interval_joint_patch import I,iv,R,z,pi,g,uf
import allbearing_boundary_jet as hub

def width(r,b,w,j):
 s=sqrt(1-r*r);ph=asin(r);x0=2*b-pi/2+ph;p=cos(w)-r*cos(x0+w);x=-sin(w)+r*sin(x0+w)
 cx=s-r*sin(2*b);cy=-2*r*sin(b)**2;px=s*cos(w)-r*sin(w);py=-s*sin(w)-r*cos(w)
 q=(px-cx)**2+(py-cy)**2;den=1-p
 cn=1+r.v*r.v-2*r.v*iv.cos(x0.v)
 if cn.a>=0 and cn.b<1:
  gap=1-iv.sqrt(cn);den.v=I(max(den.v.a,gap.a),den.v.b);q.v=I(max(q.v.a,(gap**2).a),q.v.b)
 u=sqrt(q)/R;eta=atan2(x,den);mu,h,d,l=(z[1],z[112],z[34],z[96])if j==0 else(z[3],z[115],z[39],z[101])
 return -r*s*sin(b)**2+Jet(I(1)/2-mu)*w+x/2+Jet(mu+h)*eta-Jet(d)*u*u-Jet(l)*u,q

def objective(box,j):
 r,b1,b2,p,w1,w3=[Jet(v,[I(int(i==k))for k in range(7)])for i,v in enumerate(box)]
 ans=hub.objective(box[:4],j)
 ans+=Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*asin(r)
 qs=[]
 for b,w,i in [(b1,w1,0),(b2,w3,1)]:
  f,q=width(r,b,w,i);ans+=f;qs.append(q.v)
 return ans,qs

def legal(box,j):
 if not hub.legal(box[:4],j):return False
 r,b1,b2,p,w1,w3=box;ph=pi/2-iv.atan2(iv.sqrt(1-r*r),r)
 for b,w in [(b1,w1),(b2,w3)]:
  x0=2*b-pi/2+ph;X=r*iv.sin(x0);D=1-r*iv.cos(x0)
  if X.b<0:return False
  W=2*iv.atan2(I(max(I(0).a,X.a),X.b),D)
  if w.a>W.b:return False
 return True

def bound(box,j):
 if not legal(box,j):return None
 try:
  f,qs=objective(box,j)
  if any((q-box[0]**2).a>0 for q in qs):return None
  mid=[I((float(v.a)+float(v.b))/2)for v in box];fm,_=objective(mid,j)
  mv=fm.v+sum((d*(v-m)for d,v,m in zip(f.d,box,mid)),I(0))
  return min(uf(f.v),uf(mv)),[uf(abs(d))for d in f.d[:6]]
 except Unsafe:return float('inf'),[1]*6
