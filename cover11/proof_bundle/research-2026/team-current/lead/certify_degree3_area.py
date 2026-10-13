"""Directed interval certificate of repaired area relaxation; rational grid, Lipschitz enclosure.
No optimizer imported or trusted. Reads only rounded rational dual multipliers.
"""
import json
from pathlib import Path
from mpmath import iv
iv.dps=35
P=Path(__file__).parent
R=iv.mpf(19)/50;R2=R*R;N=2048;step=iv.mpf(22)/(7*N)
# Whole [0,pi] subset [0,22/7]. Every point within step of a grid node.
grid=[]
for k in range(N+1):
 a=step*k;s=iv.sin(a/2)
 v=iv.mpf([max(.5,float(s.a)),max(.5,float(s.b))]) if False else None
 # no float endpoints: max with rational 1/2 by endpoint selection
 half=iv.mpf(1)/2
 if s.b<=half.a:v=half
 elif s.a>=half.b:v=s
 else:v=iv.mpf([half.a,s.b])
 v=R*v
 w=2*iv.atan2(v,iv.sqrt(1-v*v))
 F=R2*iv.sin(a)/2+(w-iv.sin(w))/2
 grid.append((a,iv.sin(a),w,F))
J=json.loads((P/'area_repaired_dual.json').read_text())
results=[]
for j in J:
 mu=[iv.mpf(f'{x:.8f}') for x in j['z'][:11]];lam=iv.mpf(f'{j["z"][11]:.8f}')
 assert lam.a>=0
 core=[i for i in range(9) if not(j['q'] and i==1)]
 u,v=j['edge'];p=core.index(u);cc=core[p:]+core[:p];assert cc[1]==v
 edges=[(i,(i+1)%9) for i in range(9)]+([(0,2)] if j['q'] else [])
 edges +=[(9,u),(9,v)]+[(10,x) for x in cc]+[(9,10)]
 upper=2*iv.pi*(sum(mu)-lam)
 # sin Lipschitz 1; signed linear slope absolute bounds
 for i,k in edges:
  b=mu[i]+mu[k]
  vals=[R2*s-b*a for a,s,w,F in grid]
  m=max(z.b for z in vals)
  upper+=m+(R2+abs(b))*step
 # w has global Lipschitz <=1, F <=1 as proved in accompanying note.
 for i in range(9):
  vals=[F+lam*w-mu[i]*a for a,s,w,F in grid]
  upper+=max(z.b for z in vals)+(1+lam+abs(mu[i]))*step
 assert upper.b<iv.pi.a,(j,upper)
 results.append({'q':j['q'],'small_hub_edge':j['edge'],'upper_interval':str(upper),'pi_interval':str(iv.pi),'strict_less_pi':True,'mu':[str(x) for x in mu],'lambda':str(lam)})
 print('CERTIFIED',j['q'],j['edge'],str(upper),flush=True)
(P/'degree3_area_certificate.json').write_text(json.dumps({'status':'proved-interval arithmetic conditional on geometric interface','radius':'19/50','N':N,'grid_step':'22/(7*2048)','results':results},indent=2))
