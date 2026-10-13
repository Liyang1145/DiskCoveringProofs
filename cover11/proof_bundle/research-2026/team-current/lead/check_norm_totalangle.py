import json
from norm_totalangle_jet import objective
from low_low_boundary_jet import objective as old
from interval_joint_patch import I,pi,P
rows=[]
for b,T,q in [('.65','1.57','-.5'),('.8','1.571','.3'),('.95','1.569','0')]:
 box=list(map(I,['.3795',b,T,q]));r,b,T,q=box;f=objective(box);g=old([r,b,T-b,pi+q],2);gd=[g.d[0],g.d[1]-g.d[2],g.d[2],g.d[3]]
 err=max(abs(float((f.v-g.v).mid)),*[abs(float((a-b).mid))for a,b in zip(f.d,gd)]);assert err<1e-13;rows.append({'error':err})
(P/'norm_totalangle_control.json').write_text(json.dumps(rows,indent=2));print('3 normtotalangle value/fullgradient controls PASS')
