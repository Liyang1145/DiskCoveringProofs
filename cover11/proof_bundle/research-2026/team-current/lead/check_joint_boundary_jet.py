from pathlib import Path
import numpy as np,json,math
from interval_joint_patch import I
import joint_boundary_jet as j
import patch_smooth_jet as p
rows=[]
for branch in [0,1,2]:
 for b1,b2,pp in [(.85,.93,.2),(1.1,1.04,-.1),(.76,.88,-.2)]:
  r=.3795;w1=.18;w3=.19
  if branch==2:pp=math.pi+pp
  vals=[r,b1,b2,pp,w1,w3];f,_=j.objective(list(map(I,vals)),branch)
  if branch<2:
   de=pp;H=2*r*math.sin(2*b1-de)if branch==0 else 2*r*math.sin(2*b2+de)
  else:
   v=math.sqrt(1-r*r)+(1-r)*math.cos(pp);t=(1-r)*math.sin(pp);de=math.atan2(t,v);H=math.hypot(v,t)
  old=p.objective(list(map(I,[r,b1,b2,de,w1,w3,H])));err=abs(float(f.v.mid)-float(old.v.mid));assert err<1e-12
  fd=[];eps=1e-6
  for k in range(6):
   va=vals.copy();vb=vals.copy();va[k]+=eps;vb[k]-=eps
   fa=j.objective(list(map(I,va)),branch)[0];fb=j.objective(list(map(I,vb)),branch)[0]
   derivative=float((fa.v-fb.v).mid)/(2*eps);fd.append(abs(derivative-float(f.d[k].mid)))
  assert max(fd)<1e-6
  rows.append({'branch':branch,'box':vals,'value_error':err,'gradient_fd_errors':fd})
Path(__file__).with_name('joint_boundary_jet_control.json').write_text(json.dumps(rows,indent=2));print('9 value/6gradientcontrols passed',max(max(r['gradient_fd_errors'])for r in rows))
