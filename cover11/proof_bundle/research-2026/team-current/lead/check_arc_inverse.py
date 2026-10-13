from pathlib import Path
import math,json
from mpmath import iv
iv.dps=35;R=iv.mpf(19)/50
asin=lambda x:iv.atan2(x,iv.sqrt(1-x*x))
g=2*iv.pi-16*asin(R);assert g.b<(2*asin(iv.mpf(3)/8)).a
r=R;eta=g/2;b=(iv.pi/2-asin(r)+asin(iv.sin(eta)/r)-eta)/2
maxerr=0
for r in [.375,.377,.38]:
 for frac in [0,.01,.1,.5,.9,1]:
  eta=frac*math.asin(r);x=math.asin(min(1,math.sin(eta)/r))-eta;W=2*math.atan2(r*math.sin(x),1-r*math.cos(x));maxerr=max(maxerr,abs(W-2*eta))
  assert -1e-14<=x<=math.acos(r)+1e-14
out={'scope':'analyticinversecalibrationanddirectedfloorcheck','uniform_bmin_interval':str(b),'g_interval':str(g),'g_lt_2asin_3over8':True,'float_residual':maxerr};p=Path(__file__).parent/'arc_inverse_control.json';p.write_text(json.dumps(out,indent=2));print(out)
