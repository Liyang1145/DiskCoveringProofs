"""Certify exact switchingridge delta=b1-b2 maximizes H-eliminated objective onlocalbox."""
import interval_joint_patch as k
from interval_joint_patch import I,iv,R,z,lf,uf
from pathlib import Path
import json
r=I('.379','.38');b1=I('1.105','1.108');b2=I('1.068','1.071');de=I('.035','.040');A=b1-de;B=b2+de
rows=[]
for branch in [1,2]:
 arg=2*b1-de if branch==1 else 2*b2+de
 H=2*r*iv.sin(arg);Hd=(-2 if branch==1 else 2)*r*iv.cos(arg)
 result=z[3]-z[1]
 for b,th,td,az,bz,gz in [(b1,A,-1,z[1]-z[9],-z[16],-z[78]),(b2,B,1,z[3]-z[9],z[20],z[82])]:
  D=2*r*iv.sin(b);y=D*iv.sin(th);yd=D*iv.cos(th)*td;x=H-D*iv.cos(th);xd=Hd+D*iv.sin(th)*td;Q=x*x+y*y;Qd=2*x*xd+2*y*yd;assert Q.a>0
  result+=(Hd*y+H*yd)/2+az*(x*yd-y*xd)/Q+bz*Qd/(4*R*R)+gz*Qd/(4*R*iv.sqrt(Q))
 rows.append([lf(result),uf(result)])
assert rows[0][0]>0 and rows[1][1]<0,rows
# ridgeinsideboxforallb1,b2? b1-b2 range [.034,.040], includesbelow. Onlyconditionalifinbox; foroffboxclosestendpoint.
out={'scope':'sameouterboxash_monotone_box_certificate; feasibleH upperactive; two smoothbranches','derivatives':rows,'ridge':'delta=b1-b2','claim':'strictlyincreasing onleftbranch anddecreasing onrightbranch whereverfeasible inbox; ifridgefeasible maximizerthere, else onlyconditionalmonotonicbranchstatement'};Path(__file__).with_name('delta_ridge_certificate.json').write_text(json.dumps(out,indent=2));print(out)
