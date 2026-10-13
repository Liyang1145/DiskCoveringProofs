"""Small explicit near-degenerate band; inherited audited interval ring function."""
from pathlib import Path
import json,sys
from mpmath import iv
P=Path(__file__).parent;sys.argv=['x','0','4'];ns={'__file__':str(P/'certify_q0_closure.py')};exec((P/'certify_q0_closure.py').read_text().replace("f'q0_closure_dual_{start}_{span}.json'","'endpoint_frozen_dual_0_4.json'").split('# Heap entries')[0],ns)
iv.dps=35;z=ns['z'];pi=iv.pi;rows=json.loads((P/'endpoint_sector_corner.partial.json').read_text());assert len(rows)==29
const=pi*(sum(z[:9])+2*sum(z[9:11])+sum(z[50:71])-2*z[71])-pi*sum(z[112:]);out=[]
# exact covering of alpha[pi-1e-8,pi],u,v[493/500,1] by 20x20 boxes.
for i in [0,4]:
 fun=ns['factors'][20+i][1];upper=None
 for j in range(20):
  for k in range(20):
   u0=iv.mpf(493)/500+iv.mpf(7*j)/10000;u1=iv.mpf(493)/500+iv.mpf(7*(j+1))/10000
   v0=iv.mpf(493)/500+iv.mpf(7*k)/10000;v1=iv.mpf(493)/500+iv.mpf(7*(k+1))/10000
   val=fun([iv.mpf([(pi-iv.mpf('1e-8')).a,pi.b]),iv.mpf([u0.a,u1.b]),iv.mpf([v0.a,v1.b])]);assert val is not None
   if upper is None or val.b>upper:upper=val.b
 total=const+sum(iv.mpf(r['upper']) for r in rows if r['factor']!='ring'+str(i))+upper
 out.append({'sector':i,'factor_upper':str(upper),'area_upper':str(total),'strict':bool(total.b<pi.a)})
print(out);(P/'endpoint_sector_band_certificate.json').write_text(json.dumps({'scope':'continuous alpha[pi-1e-8,pi],u,v[493/500,1] in R0=.38 units','rows':out},indent=2));assert all(r['strict'] for r in out)
