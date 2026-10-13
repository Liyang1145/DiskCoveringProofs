import json
from low_corner_jet import coords,objective,legal
from legal_cartesian_value import value
from interval_joint_patch import I,P
rows=[]
for j in [0,1,2]:
 for sg in [-1,1]if j<2 else[1]:
  for b1,b2 in [('.65','.65'),('.7','.8'),('.84','.85'),('1','1')]:
   box=list(map(I,['.3795',b1,b2]))
   if not legal(box,j,sg):continue
   args=coords(box,j,sg);val=value(*[x.v for x in args]);f=objective(box,j,sg);assert val is not None and val.b>=f.v.a
   rows.append({'j':j,'sign':sg,'b1':b1,'b2':b2,'upper_gap':str(val-f.v)})
(P/'legal_cartesian_value_control.json').write_text(json.dumps(rows,indent=2));print(len(rows),'legalpointvaluecontrols passed')
