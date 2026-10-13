from pathlib import Path
import math,json,numpy as np
P=Path(__file__).parent;s=(P/'check_arc_chart.py').read_text();m="\nif __name__";assert s.count(m)==1
ns={'__file__':str(P/'check_arc_chart.py')};exec(s.split(m)[0],ns)
rng=np.random.default_rng(1261);z=ns['ns']['z'];R=.38;best=[(1e9,None),(1e9,None)]
for _ in range(50000):
 r=rng.uniform(.375,.38);s=math.sqrt(1-r*r);b=rng.uniform(math.acos(r)/2,math.acos(r));W=ns['width'](r,b)
 if W<ns['g']:continue
 w=rng.uniform(ns['g'],W);c=np.array([s-2*r*math.sin(b)*math.cos(b),-2*r*math.sin(b)**2]);p=np.array([s*math.cos(w)-r*math.sin(w),-s*math.sin(w)-r*math.cos(w)]);D=float(np.sum((p-c)**2));u=math.sqrt(D)/R;dot=float(c@p);X=float(c[0]*p[1]-c[1]*p[0])
 for k,(mu,h,d,dl) in enumerate([(z[1],z[112],z[34],z[96]),(z[3],z[115],z[39],z[101])]):
  der=(1-dot)*(.5+(-mu-h)/D)+h+(2*d+dl/u)*X/(R*R)
  if der<best[k][0]:best[k]=(der,[r,b,w])
print(best);(P/'width_derivative_probe.json').write_text(json.dumps(best,indent=2))
