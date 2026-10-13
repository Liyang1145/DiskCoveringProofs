"""Unified 4D full-extension value AD on face polar / norm central-angle charts."""
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt,atan2
from interval_joint_patch import I,iv,R,z

def objective(box,j):
 r,b1,b2,p=[Jet(v,[I(int(i==k))for k in range(7)])for i,v in enumerate(box)]
 if j<2:
  A=b1-p;B=b2+p;H=2*r*sin(2*b1-p)if j==0 else 2*r*sin(2*b2+p)
  ans=Jet(z[3]-z[1])*p+H*r*(sin(b1)*sin(A)+sin(b2)*sin(B))
  for i,(b,ang,a,bb,gg)in enumerate([(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]):
   if i==j:e=r*sin(ang)/R;phi=b
   else:
    X=H-2*r*sin(b)*cos(ang);Y=2*r*sin(b)*sin(ang);e=sqrt(X*X+Y*Y)/(2*R);phi=atan2(Y,X)
   ans+=Jet(a)*phi+Jet(bb)*e*e+Jet(gg)*e
  return ans
 v=sqrt(1-r*r)+(1-r)*cos(p);t=(1-r)*sin(p)
 ans=r*(sin(b1)**2+sin(b2)**2)*v+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*t
 for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
  X=v-r*sin(2*b);Y=2*r*sin(b)**2+sg*t;e=sqrt(X*X+Y*Y)/(2*R)
  ans+=Jet(a)*atan2(Y,X)+Jet(bb)*e*e+Jet(gg)*e
 return ans

def legal(box,j):
 r,b1,b2,p=box;s=iv.sqrt(1-r*r)
 if (iv.cos(b1)-r).b<0 or (iv.cos(b2)-r).b<0:return False
 if j<2:
  A=b1-p;B=b2+p
  if A.b<=0 or B.b<=0 or A.a>=iv.pi.b or B.a>=iv.pi.b:return False
  H=2*r*iv.sin(2*b1-p)if j==0 else 2*r*iv.sin(2*b2+p)
  if H.b<=0:return False
  cap=2*r*iv.sin(2*b2+p)if j==0 else 2*r*iv.sin(2*b1-p)
  if (H-cap).a>0 or (H*H-2*s*iv.cos(p)*H+2*r*(1-r)).a>0:return False
 else:
  v=s+(1-r)*iv.cos(p);t=(1-r)*iv.sin(p)
  for b,sg in [(b1,-1),(b2,1)]:
   if ((v-r*iv.sin(2*b))**2+(t-sg*r*iv.cos(2*b))**2-r*r).a>0:return False
  if (v*iv.tan(b1)-t).b<=0 or (t+v*iv.tan(b2)).b<=0:return False
 return True

def value_bound(box,j):
 f=objective(box,j);mid=[I((float(v.a)+float(v.b))/2)for v in box];fm=objective(mid,j)
 mv=fm.v+sum((d*(v-m)for d,v,m in zip(f.d,box,mid)),I(0))
 return I(max(f.v.a,mv.a),min(f.v.b,mv.b)),f
