"""Face-circle objective with active length and angle evaluated symbolically.
Uses direct fixed Cartesian frame; active angle is A (face1) or B(face2), not bj.
"""
from face_second_jet import J,sin,cos,sqrt,angle,Unsafe
from interval_joint_patch import R,z

def objective(box,j):
 r,b1,b2,d=box;r,b1,b2=map(J,[r,b1,b2]);d=J(d,1);A=b1-d;B=b2+d
 b,c=(b1,A)if j==0 else(b2,B)
 v=r*(sin(2*b)+sin(2*c));t=(1 if j==0 else -1)*r*(cos(2*c)-cos(2*b))
 ans=r*(sin(b1)*sin(b1)+sin(b2)*sin(b2))*v+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*t
 for i,(b,ang,sg,a,bb,gg)in enumerate([(b1,A,-1,z[1]-z[9],-z[16],-z[78]),(b2,B,1,z[3]-z[9],z[20],z[82])]):
  if i==j:e=r*sin(ang)/R;phi=ang
  else:
   Y=2*r*sin(b)*sin(b)+sg*t;X=v-2*r*sin(b)*cos(b);e=sqrt(X*X+Y*Y)/(2*R);phi=angle(Y,X)
  ans+=J(a)*phi+J(bb)*e*e+J(gg)*e
 return ans
