"""Independent scalar-loop dual identity calibration on six radius-compatible states.
No helper imported from proposer or certificate kernel. Numeric calibration, not proof.
"""
import json,math
from pathlib import Path
P=Path(__file__).parent;R=.38;pi=math.pi;out=[]
for row in json.loads((P/'area_shared_radius.json').read_text()):
 st,sp=row['start'],row['span'];z=json.loads((P/f'shared_factor_capdual_{st}_{sp}.json').read_text())['z'];faces=row['faces'];edges=[tuple(e) for e in row['edges']];x=row['x'];ang=[x[3*t:3*t+3] for t in range(11)];rad=[math.exp(v) for v in x[42:]];gam=x[33:42]
 const=pi*(sum(z[:9])+2*sum(z[9:11])+sum(z[50:71])-2*z[71]-2*z[72])+2*z[72]*math.asin(2*R)
 dual=const;area=0;width=[];slack=[]
 for t,f in enumerate(faces):
  v=2*R*R*rad[t]**2*math.prod(math.sin(a) for a in ang[t]);area+=v
  for k,i in enumerate(f):
   e=tuple(sorted(j for j in f if j!=i));ee=edges.index(e);adj=[tt for tt,ff in enumerate(faces) if e[0] in ff and e[1] in ff];sign=1 if adj[0]==t else -1
   v-= (z[i]+z[50+ee])*ang[t][k];v+=sign*z[11+ee]*rad[t]**2*math.sin(ang[t][k])**2
  dual+=v
 for bi in range(9):
  i,j=bi,(bi+1)%9;ee=edges.index(tuple(sorted((i,j))));b=pi/2-gam[bi];xx=rad[11+bi]**2;v=R*R*xx*math.sin(2*b)/2;area+=v
  v+=(z[i]+z[j]-z[50+ee])*b+xx*(-z[11+ee]*math.sin(b)**2+z[32+2*i+1]+z[32+2*j]);dual+=v
 for i in range(9):
  a=2*pi-sum(ang[t][f.index(i)] for t,f in enumerate(faces) if i in f)-gam[(i-1)%9]-gam[i];u=rad[11+(i-1)%9];v=rad[11+i];w=2*math.asin(R*math.sqrt(u*u+v*v-2*u*v*math.cos(a))/2);width.append(w)
  S=R*R*u*v*math.sin(a)/2+(w-math.sin(w))/2;area+=S;dual+=S+(z[71]+(z[72] if i>=3 else 0))*w-z[i]*a-z[32+2*i]*u*u-z[32+2*i+1]*v*v
 for ee,(i,j) in enumerate(edges):
  aa=[ang[t][next(k for k,v in enumerate(f) if v not in (i,j))] for t,f in enumerate(faces) if i in f and j in f]
  if len(aa)==1:bi=next(b for b in range(9) if set((b,(b+1)%9))=={i,j});aa.append(pi/2-gam[bi])
  slack.append(pi-sum(aa))
 expected=area+z[71]*(sum(width)-2*pi)+z[72]*(sum(width[3:])-2*pi+2*math.asin(2*R))+sum(z[50+e]*s for e,s in enumerate(slack))
 error=abs(dual-expected);assert error<2e-7;assert abs(area-row['area'])<2e-8
 out.append({'start':st,'span':sp,'identity_error':error,'area_error':abs(area-row['area'])})
(P/'shared_dual_identity_calibration.json').write_text(json.dumps(out,indent=2));print('six independent scalar-loop dual identities checked; max error',max(j['identity_error'] for j in out))
