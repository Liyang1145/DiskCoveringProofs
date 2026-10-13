from face_derivative_outer_jet import derivative as face
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt
from interval_joint_patch import I,R,z

def derivative(box,j):
 if j<2:return face(box,j)
 r,b1,b2,p=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)]
 v=sqrt(1-r*r)+(1-r)*cos(p);t=(1-r)*sin(p);vd=-(1-r)*sin(p);td=(1-r)*cos(p)
 ans=r*(sin(b1)**2+sin(b2)**2)*vd+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*td
 for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
  X=v-r*sin(2*b);Y=2*r*sin(b)**2+sg*t;Q=X**2+Y**2;root=sqrt(Q);e=root/(2*R);ed=(X*vd+Y*sg*td)/(root*(2*R));pd=(X*sg*td-Y*vd)/Q
  ans+=Jet(a)*pd+(2*Jet(bb)*e+Jet(gg))*ed
 return ans

def enclosure(box,j):
 f=derivative(box,j);mid=[I((float(x.a)+float(x.b))/2)for x in box];fc=derivative(mid,j);mv=fc.v+sum((d*(x-m)for d,x,m in zip(f.d,box,mid)),I(0));return I(max(f.v.a,mv.a),min(f.v.b,mv.b))
