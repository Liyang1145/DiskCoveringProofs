import json,math
from low_corner_jet import coords,objective
from low_low_boundary_jet import objective as orig
from interval_joint_patch import I,P
rows=[]
for j in [0,1,2]:
 for sg in [-1,1]if j<2 else[1]:
  for bb1,bb2 in [('.7','.8'),('.84','.85'),('1','1')]:
   box=list(map(I,['.3795',bb1,bb2]));r,b1,b2,v,t=coords(box,j,sg);rr=.3795;ss=math.sqrt(1-rr*rr);vv=float(v.v.mid);tt=float(t.v.mid);b=float(box[j if j==2 else j+1].mid)
   if j<2:
    face=(vv-rr*math.sin(2*b))**2+(tt-(-1 if j==0 else 1)*rr*math.cos(2*b))**2-rr*rr;norm=(vv-ss)**2+tt*tt-(1-rr)**2;assert max(abs(face),abs(norm))<1e-12
    p=math.atan2(tt,vv-ss);other=orig(box+[I(p)],2)
   else:p=math.atan2(tt,vv);other=orig(box+[I(p)],0)
   val=objective(box,j,sg);err=abs(float(val.v.mid)-float(other.v.mid));assert err<1e-10
   rows.append({'j':j,'sg':sg,'b1':bb1,'b2':bb2,'value_difference':err})
(P/'low_corners_control.json').write_text(json.dumps(rows,indent=2));print('15corner Cartesian/angle-chart controls passed')
