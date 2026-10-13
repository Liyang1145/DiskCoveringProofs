"""Assemble complete interval bounds + uniformcorner segment, no floatlower used."""
from pathlib import Path
import json
from fractions import Fraction
from mpmath import iv
iv.dps=40;P=Path(__file__).parent
j=json.loads((P/'endpoint_frozen_dual_0_4.json').read_text());z=[iv.mpf(f'{v:.9f}') for v in j['z']];rows=json.loads((P/'endpoint_sector_corner.partial.json').read_text());seg=json.loads((P/'endpoint_segment_control.json').read_text())
expected=['face'+str(i) for i in range(11)]+['switch'+str(i) for i in range(9)]+['ring'+str(i) for i in range(9)]
assert [r['factor'] for r in rows]==expected
assert all(z[k].a>=0 for k in range(50,73));assert z[72]==0
pi=iv.pi;const=pi*(sum(z[:9])+2*sum(z[9:11])+sum(z[50:71])-2*z[71])-pi*sum(z[112:]);out=[]
for i in [0,4]:
 s=next(s for s in seg['rows'] if s['sector']==i);assert s['rational_upper']=='-9891/200000';corner=-iv.mpf(9891)/200000
 bound=const+sum(iv.mpf(r['upper']) for r in rows if r['factor']!='ring'+str(i))+corner
 assert bound.b<pi.a
 out.append({'sector':i,'upper':str(bound),'strict':True})
obj={'scope':'all actual inward q0k4 covers with allowance r in[3/8,37999/100000]; sectoralpha_pi impossible at0and4 via uniform tsegment[75/76,1] infixedR0=.38 units','R_normalization':'19/50','actual_allowance_interval':['3/8','37999/100000'],'conditional_upper':out,'pi':str(pi),'factor_source':'endpoint_sector_corner.partial.json','segment_source':'endpoint_segment_control.json','coefficients_9decimal':[f'{v:.9f}' for v in j['z']]}
(P/'endpoint_sector_uniform_certificate.json').write_text(json.dumps(obj,indent=2));print(out)
