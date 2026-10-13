import json
from face_normarc_jet import ends,objective
from face_totalangle_jet import objective as old
from patch_smooth_jet import Jet
from interval_joint_patch import I,iv,P
rows=[]
for j in [0,1]:
 for b,T,q in [('.65','1.3','.2'),('.8','1.6','.7'),('1','1.9','.9')]:
  box=list(map(I,['.3795',b,T,q]));r,b,T,q=box;lo,hi=ends(Jet(r),Jet(b));A=lo.v+(hi.v-lo.v)*q;f=objective(box,j);g=old([r,b,T,A],j);assert abs(float((f.v-g.v).mid))<1e-14
  for x in [lo.v,hi.v]:
   residual=1-iv.sqrt(1-r*r)*(iv.sin(2*b)+iv.sin(2*x))-r*iv.cos(2*(b+x));assert residual.a<=0<=residual.b
  for k in range(4):
   h=I('1e-6');plus=box.copy();minus=box.copy();plus[k]+=h;minus[k]-=h;fd=(objective(plus,j).v-objective(minus,j).v)/(2*h);err=abs(float((fd-f.d[k]).mid));assert err<2e-6
  rows.append({'j':j,'A':str(A),'lo':str(lo.v),'hi':str(hi.v)})
(P/'face_normarc_control.json').write_text(json.dumps(rows,indent=2));print('6 chartvalues/24FDderivatives/12endcapcontrols PASS')
