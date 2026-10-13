"""Directed 1D segment upper for actual radius3/8..19/50 at fixed normalization19/50."""
from pathlib import Path
import json
from mpmath import iv
iv.dps=40;P=Path(__file__).parent;j=json.loads((P/'endpoint_frozen_dual_0_4.json').read_text());z=[iv.mpf(f'{v:.9f}') for v in j['z']];R=iv.mpf(19)/50;pi=iv.pi
# Rational endpoint boxes; union covers[75/76,1] exactly, count bounded1000.
N=1000;rows=[]
for i in [0,4]:
 top=None
 for k in range(N):
  l=iv.mpf(75)/76+iv.mpf(k)/(76*N);h=iv.mpf(75)/76+iv.mpf(k+1)/(76*N);t=iv.mpf([l.a,h.b]);rt=R*t;w=2*iv.atan2(rt,iv.sqrt(1-rt*rt))
  f=(w-iv.sin(w))/2-z[i]*pi-(z[32+2*i]+z[33+2*i])*t*t-(z[94+2*i]+z[95+2*i])*t+z[71]*w+(z[112+(i-1)%9]+z[112+i])*w/2
  if top is None or f.b>top:top=f.b
 assert top < iv.mpf('-0.049455').a
 rows.append({'sector':i,'upper':str(top),'rational_upper':'-9891/200000','upper_internal':str(top._mpi_[1]),'boxes':N})
(P/'endpoint_segment_control.json').write_text(json.dumps({'scope':'directed continuous segment bound, not fullfactorcertificate','rows':rows},indent=2));print(rows)
