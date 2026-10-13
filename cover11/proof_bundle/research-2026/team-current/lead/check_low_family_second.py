import json
from low_family_second import objective
from low_low_boundary_jet import objective as first
from interval_joint_patch import I,P
rows=[]
for j in range(3):
 for b1,b2 in [(.65,.7),(.84,.85),(.95,.95)]:
  x=[.3795,b1,b2,.1 if j<2 else 2.8]
  for direction in [[0,1,0,0],[0,0,1,0],[0,1,-1,0],[0,0,0,1]]:
   f=objective(list(map(I,x)),j,direction);a=first(list(map(I,x)),j);ad=sum(float(d.mid)*v for d,v in zip(a.d,direction));assert abs(ad-float(f.d.mid))<1e-10;assert abs(float(a.v.mid)-float(f.v.mid))<1e-10
   h=1e-5;plus=first([I(v+h*d)for v,d in zip(x,direction)],j);minus=first([I(v-h*d)for v,d in zip(x,direction)],j);fd=sum((float(u.mid)-float(v.mid))*w for u,v,w in zip(plus.d,minus.d,direction))/(2*h);err=abs(fd-float(f.h.mid));assert err<1e-4
   rows.append({'j':j,'point':x,'direction':direction,'curvature':float(f.h.mid),'error':err})
(P/'low_family_second_control.json').write_text(json.dumps(rows,indent=2));print('36 secondAD controls maxerror',max(x['error']for x in rows));print('positivecurvature',sum(x['curvature']>0 for x in rows))
