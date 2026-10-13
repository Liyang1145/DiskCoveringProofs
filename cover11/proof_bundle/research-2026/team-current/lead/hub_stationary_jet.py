"""5-variable full-extension AD of exact Cartesian hub gradient; no physical clipping."""
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt
from interval_joint_patch import I,iv,R,z,lf,uf

def gradient(box):
 r,b1,b2,v,t=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)]
 gx=r*(sin(b1)**2+sin(b2)**2);gy=r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))
 for b,sg,a,beta,c in [(b1,-1,z[1]-z[9],-z[16]/(4*R*R),z[78]/(2*R)),(b2,1,z[3]-z[9],z[20]/(4*R*R),-z[82]/(2*R))]:
  X=v-r*sin(2*b);Y=t+sg*2*r*sin(b)**2;Q=X*X+Y*Y;L=sqrt(Q);W=Jet(2*beta)-Jet(c)/L
  gx+=W*X-Jet(a*sg)*Y/Q;gy+=W*Y+Jet(a*sg)*X/Q
 return gx,gy

def enclosure(box):
 g=gradient(box);mid=[I((float(x.a)+float(x.b))/2)for x in box];gm=gradient(mid);tight=[]
 for a,b in zip(g,gm):
  mv=b.v+sum((d*(x-m)for d,x,m in zip(a.d,box,mid)),I(0))
  tight.append(I(max(a.v.a,mv.a),min(a.v.b,mv.b)))
 return tight,g

def legal(box):
 r,b1,b2,v,t=box;s=iv.sqrt(1-r*r)
 if (iv.cos(b1)-r).b<0 or (iv.cos(b2)-r).b<0:return False
 if ((v-s)**2+t*t-(1-r)**2).a>0:return False
 for b,sg in [(b1,-1),(b2,1)]:
  if ((v-r*iv.sin(2*b))**2+(t-sg*r*iv.cos(2*b))**2-r*r).a>0:return False
 if (v*iv.tan(b1)-t).b<=0 or (t+v*iv.tan(b2)).b<=0:return False
 return True
