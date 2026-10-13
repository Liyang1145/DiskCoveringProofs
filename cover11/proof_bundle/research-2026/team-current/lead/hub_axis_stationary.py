"""Three-variable universal hub stationary equations; pole-cleared positive curvature."""
from patch_smooth_jet import Jet,Unsafe,sqrt
from interval_joint_patch import I,R,z,uf,lf
beta1=-z[16]/(4*R*R);beta2=z[20]/(4*R*R);c1=z[78]/(2*R);c2=-z[82]/(2*R);a1=z[1]-z[9];a2=z[3]-z[9]
def equations(box):
 d,x,y=[Jet(v,[I(int(i==k))for k in range(7)])for i,v in enumerate(box)];u=y-d/2;v=y+d/2;q1=x*x+u*u;q2=x*x+v*v;l1=sqrt(q1);l2=sqrt(q2)
 gx=(d/2+2*(Jet(beta1)+Jet(beta2))*x)*q1*q2-x*(Jet(c1)*l1*q2+Jet(c2)*l2*q1)+Jet(a1)*u*q2-Jet(a2)*v*q1
 gy=(2*Jet(beta1)*u+2*Jet(beta2)*v)*q1*q2-Jet(c1)*u*l1*q2-Jet(c2)*v*l2*q1-Jet(a1)*x*q2+Jet(a2)*x*q1
 curvature=2*(Jet(beta1)+Jet(beta2))*q1*q1*q2*q2-x*x*(Jet(c1)*l1*q2*q2+Jet(c2)*l2*q1*q1)+2*x*(Jet(a1)*u*q2*q2-Jet(a2)*v*q1*q1)
 return [gx,gy,curvature]
def direct(box):
 d,x,y=[Jet(v,[I(int(i==k))for k in range(7)])for i,v in enumerate(box)];u=y-d/2;v=y+d/2;q1=x*x+u*u;q2=x*x+v*v;l1=sqrt(q1);l2=sqrt(q2)
 w1=Jet(2*beta1)-Jet(c1)/l1;w2=Jet(2*beta2)-Jet(c2)/l2
 return [d/2+(w1+w2)*x+Jet(a1)*u/q1-Jet(a2)*v/q2,w1*u+w2*v-Jet(a1)*x/q1+Jet(a2)*x/q2]
def direct_bounds(box):
 fs=direct(box);mid=[I((float(v.a)+float(v.b))/2)for v in box];fm=direct(mid);out=[]
 for a,b in zip(fs,fm):
  mv=b.v+sum((g*(v-m)for g,v,m in zip(a.d,box,mid)),I(0));out.append(I(max(a.v.a,mv.a),min(a.v.b,mv.b)))
 return out,fs

def bounds(box):
 f=equations(box);mid=[I((float(v.a)+float(v.b))/2)for v in box];fm=equations(mid);out=[]
 for a,b in zip(f,fm):
  mv=b.v+sum((g*(v-m)for g,v,m in zip(a.d,box,mid)),I(0));out.append(I(max(a.v.a,mv.a),min(a.v.b,mv.b)))
 return out
