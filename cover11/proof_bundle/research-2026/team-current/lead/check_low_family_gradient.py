import json
from interval_joint_patch import I,P
from low_low_boundary_jet import objective
rows=[]
for j in range(3):
 for b1,b2 in [(.65,.7),(.84,.85),(.7853981633974483,.7853981633974483)]:
  x=[.3795,b1,b2,.1 if j<2 else 2.8];f=objective(list(map(I,x)),j)
  for direction in [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,1,-1,0]]:
   h=1e-6;plus=objective([I(a+h*d)for a,d in zip(x,direction)],j);minus=objective([I(a-h*d)for a,d in zip(x,direction)],j);fd=(float(plus.v.mid)-float(minus.v.mid))/(2*h);ad=sum(float(d.mid)*v for d,v in zip(f.d,direction));err=abs(ad-fd);assert err<2e-6
   rows.append({'j':j,'point':x,'direction':direction,'error':err})
(P/'low_family_gradient_control.json').write_text(json.dumps(rows,indent=2));print(len(rows),'FD directional controls PASS; maxerror',max(x['error']for x in rows))
