"""First-order outer AD of explicit Cartesian face derivative; MVT over r,b1,b2,delta.
No physical clipping. Used solely as stationary-point exclusion; same frozen objective.
"""
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt
from interval_joint_patch import I,R,z,uf,lf

def derivative(box,j):
 r,b1,b2,d=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)]
 A=b1-d;B=b2+d;b,c=(b1,A)if j==0 else(b2,B)
 v=r*(sin(2*b)+sin(2*c));t=(1 if j==0 else -1)*r*(cos(2*c)-cos(2*b))
 vd=(-2 if j==0 else 2)*r*cos(2*c);td=2*r*sin(2*c)
 ans=r*(sin(b1)**2+sin(b2)**2)*vd+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*td
 for i,(b,ang,sg,a,bb,gg)in enumerate([(b1,A,-1,z[1]-z[9],-z[16],-z[78]),(b2,B,1,z[3]-z[9],z[20],z[82])]):
  if i==j:
   e=r*sin(ang)/R;ed=(-1 if j==0 else 1)*r*cos(ang)/R;pd=Jet(I(-1 if j==0 else 1))
  else:
   X=v-2*r*sin(b)*cos(b);Y=2*r*sin(b)**2+sg*t;Q=X*X+Y*Y;root=sqrt(Q)
   e=root/(2*R);ed=(X*vd+Y*sg*td)/(root*2*R);pd=(X*sg*td-Y*vd)/Q
  ans+=Jet(a)*pd+(2*Jet(bb)*e+Jet(gg))*ed
 return ans

def enclosure(box,j):
 f=derivative(box,j);mid=[I((float(x.a)+float(x.b))/2)for x in box];fc=derivative(mid,j)
 centered=fc.v+sum((g*(x-m)for g,x,m in zip(f.d,box,mid)),I(0))
 return I(max(f.v.a,centered.a),min(f.v.b,centered.b)),f.d[:4]
