from face_totalangle_jet import objective,legal
from low_low_boundary_jet import objective as old
from interval_joint_patch import I,P
import json
rows=[]
for j in [0,1]:
 for b,T,A in [('.7','1.5','.2'),('.84','1.6','.8'),('.95','1.7','1.2')]:
  box=list(map(I,['.3795',b,T,A]));r,b,T,A=box;other=T-b;p=(b-A)if j==0 else(A-b);orig=[r,b,other,p]if j==0 else[r,other,b,p];f=objective(box,j);g=old(orig,j)
  # chainrule map
  gd=[g.d[0],g.d[1]-g.d[2]+g.d[3],g.d[2],-g.d[3]]if j==0 else[g.d[0],g.d[2]-g.d[1]-g.d[3],g.d[1],g.d[3]]
  err=max(abs(float((f.v-g.v).mid)),*[abs(float((a-b).mid))for a,b in zip(f.d,gd)]);assert err<1e-14;rows.append({'j':j,'err':err})
(P/'face_totalangle_control.json').write_text(json.dumps(rows,indent=2));print('6totalangle value/chainrulegradient controls PASS')
