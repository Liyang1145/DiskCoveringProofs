"""Independent finite-difference crosscheck of localdelta derivative afterH substitution. Calibrationonly."""
import patch_cancel_jet as j
import interval_joint_patch as k
import math,json
from pathlib import Path
r=.3795;b1=1.107;b2=1.0695;rows=[]
for branch,de in [(1,.036),(2,.039)]:
 def val(d):
  H=2*r*math.sin(2*b1-d if branch==1 else 2*b2+d)
  return float(j.objective([k.I(str(x))for x in[r,b1,b2,d,.7,.72,H]]).v.mid)
 H=2*r*math.sin(2*b1-de if branch==1 else 2*b2+de);Hd=(-2 if branch==1 else 2)*r*math.cos(2*b1-de if branch==1 else 2*b2+de)
 jet=j.objective([k.I(str(x))for x in[r,b1,b2,de,.7,.72,H]]);ad=float(jet.d[3].mid)+float(jet.d[6].mid)*Hd
 h=1e-5;fd=(val(de+h)-val(de-h))/(2*h);assert abs(ad-fd)<1e-8;rows.append({'branch':branch,'analyticchain':ad,'FD':fd})
Path(__file__).with_name('ridge_derivative_control.json').write_text(json.dumps(rows,indent=2));print(rows)
