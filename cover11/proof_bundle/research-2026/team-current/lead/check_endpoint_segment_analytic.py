"""Independent analytic segment maximum: coefficient cancellation and derivative sign."""
from pathlib import Path
from fractions import Fraction as F
from mpmath import iv
import json
iv.dps=45;P=Path(__file__).parent;j=json.loads((P/'endpoint_frozen_dual_0_4.json').read_text());z=[F(f'{v:.9f}') for v in j['z']]
def I(f):return iv.mpf(f.numerator)/f.denominator
rows=[]
for i in [0,4]:
 assert z[32+2*i]+z[33+2*i]==0 and z[94+2*i]+z[95+2*i]==0 and z[71]==0
 h=(z[112+(i-1)%9]+z[112+i])/2
 lower=F(3,8)**2+h;assert lower>0
 # F'(w)=sin²(w/2)+h; w/2>=asin(3/8); hence max at t=1.
 r=I(F(19,50));w=2*iv.atan2(r,iv.sqrt(1-r*r));upper=(w-iv.sin(w))/2-I(z[i])*iv.pi+I(h)*w
 assert upper.b < I(F(-9891,200000)).a
 rows.append({'sector':i,'derivative_lower_exact':str(lower),'exact_max_enclosure':str(upper),'rational_upper':'-9891/200000'})
(P/'endpoint_segment_analytic_control.json').write_text(json.dumps(rows,indent=2));print(rows)
