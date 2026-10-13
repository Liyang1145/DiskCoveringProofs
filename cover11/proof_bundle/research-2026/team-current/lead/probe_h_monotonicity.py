"""Diagnostic FH derivative oncandidateouterfiber; can decide endpointlemma worth certifying."""
from pathlib import Path
import json,math,numpy as np
import interval_patch_delta as f
import interval_joint_patch as k
P=Path(__file__).parent;row=max(json.loads((P/'nested_patch_frozen_attack.json').read_text())['runs'],key=lambda x:x['value']);r,b1,b2,_,_,qa,_=row['chart'];A=qa*(b1+b2);B=b1+b2-A;outer=[r,b1,b2,b1-A];st=f.setup([k.I(str(v))for v in outer]);lo,hi=st[1][2][1];z=np.array(json.loads(k.frozen.read_text())['z']);R=.38
vals=[]
for H in np.linspace(lo,hi,101):
 val=0
 for b,th,az,bz,gz in [(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]:
  dd=2*r*math.sin(b);yy=dd*math.sin(th);xx=H-dd*math.cos(th);lsq=xx*xx+yy*yy
  val+=yy/2-az*yy/lsq+bz*xx/(2*R*R)+gz*xx/(2*R*math.sqrt(lsq))
 vals.append(val)
out={'outer':outer,'Hfiber':[lo,hi],'derivative_range_numeric':[min(vals),max(vals)],'scope':'samplesonly'};(P/'h_monotonicity_probe.json').write_text(json.dumps(out,indent=2));print(out)
