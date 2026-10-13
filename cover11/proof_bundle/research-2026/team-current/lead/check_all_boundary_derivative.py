import json
from interval_joint_patch import I,P
from all_boundary_derivative import derivative
from allbearing_boundary_jet import objective
from face_second_jet import J,sin,cos,sqrt,angle
from interval_joint_patch import R,z
rows=[]
for j in range(3):
 for b1,b2,p in [('.8','.9','-.1'),('.7','.8','.05'),('1','.95','.2')]:
  if j==2:p=str(3.14+float(p))
  box=list(map(I,['.3795',b1,b2,p]));explicit=derivative(box,j);base=objective(box,j)
  assert explicit.v.a<=base.d[3].b and base.d[3].a<=explicit.v.b
  if j==2:
   r,b1,b2=map(J,box[:3]);th=J(box[3],1);v=sqrt(1-r*r)+(1-r)*cos(th);t=(1-r)*sin(th);f=r*(sin(b1)*sin(b1)+sin(b2)*sin(b2))*v+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*t
   for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
    X=v-r*sin(2*b);Y=2*r*sin(b)*sin(b)+sg*t;e=sqrt(X*X+Y*Y)/(2*R);f+=J(a)*angle(Y,X)+J(bb)*e*e+J(gg)*e
   assert explicit.d[3].a<=f.h.b and f.h.a<=explicit.d[3].b
  rows.append({'branch':j,'point':[str(a)for a in box],'gradient_difference':str(explicit.v-base.d[3])})
(P/'all_boundary_derivative_control.json').write_text(json.dumps(rows,indent=2));print('9 derivativecontrols,3normcurvaturecontrols passed')
