import json
from interval_joint_patch import I,pi,P
from face_complement_jet import objective
from low_low_boundary_jet import objective as old
from coincident_face_jet import objective as co
rows=[]
for j in [0,1]:
 for b1,b2,p in [('.7','.8','.1'),('.84','.85','-.1'),('.95','.95','.3')]:
  box=list(map(I,['.3795',b1,b2,p]));a=objective(box,j);b=old(box,j)
  err=max(abs(float((a.v-b.v).mid)),*[abs(float((x-y).mid))for x,y in zip(a.d,b.d)]);assert err<1e-15;rows.append({'j':j,'error':err})
for b,A in [('.7','.3'),('.8','.7'),('.95','1.1')]:
 box=list(map(I,['.3795',b,A]));a=co(box);r,b,A=box;other=old([r,b,pi/2-b,b-A],0);assert abs(float((a.v-other.v).mid))<1e-15
 rows.append({'coincident':True,'difference':str(a.v-other.v)})
(P/'face_complement_control.json').write_text(json.dumps(rows,indent=2));print('6fullvalue/gradient +3coincidencecontrols PASS')
