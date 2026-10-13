from face_second_jet import J,sin,cos,sqrt,angle
from interval_joint_patch import I,iv,R,z,pi,P
import json

def width(r,b,w,j):
 r=J(r);b=J(b);w=J(w,1);s=sqrt(1-r*r);ph=angle(r,s);x0=2*b-pi/2+ph;p=cos(w)-r*cos(x0+w);x=-sin(w)+r*sin(x0+w)
 q=x*x+(1-p)*(1-p);u=sqrt(q)/R;eta=angle(x,1-p);mu,h,d,l=(z[1],z[112],z[34],z[96])if j==0 else(z[3],z[115],z[39],z[101])
 return -r*s*sin(b)*sin(b)+J(I(1)/2-mu)*w+x/2+J(mu+h)*eta-J(d)*u*u-J(l)*u,q
if __name__=='__main__':
 r,b,w=map(I,['.379','.9','.19']);rows=[]
 for j in [0,1]:
  f,q=width(r,b,w,j);rows.append({'j':j,'second':str(f.h),'first':str(f.d),'value':str(f.v),'q':str(q.v),'cosb_minus_r':str(iv.cos(b)-r),'q_minus_r2':str(q.v-r*r),'q_minus_gate':str(q.v-(R*I('.19'))**2)})
 (P/'width_curvature_control.json').write_text(json.dumps(rows,indent=2));print(rows)
