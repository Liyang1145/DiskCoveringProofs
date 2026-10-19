"""Strict-total budget for the two representatives (Lean canonicalTotalUpperQ < piLo), exact Fractions.
faceMax/sectorMax proposals = historical interval-B&B uppers (mpmath iv, NOT Lean evidence) rounded UP
to a grid; switchMax(k=7) = the nine batch bounds (proved in Lean, A25-accepted module)."""
import sys,json,math
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent)); import rep_tables as RT
def up(x,den): return F(math.ceil(x*den),den)
batch={8:F(141,10**6),0:F(7,50000),1:F(141,10**6),2:F(141,10**6),3:F(51029,10**6),4:F(4839,200000),5:F(141,10**6),6:F(141,10**6),7:F(14023,10**6)}
out={}
for start,k,cls in [(0,7,'q1bal'),(2,1,'q1bal'),(0,2,'q0')]:
  T=RT.build(start,k,cls); hu=T['hist_upper']; off=2 if cls=='q1bal' else 1; tag=('k' if cls=='q1bal' else 'q0m')+str(k)
  # hist face t -> Lean face key
  fmap={}
  for t,f in enumerate(T['faces_h']): fmap[tuple(sorted((RT.sigma(v) if cls=='q1bal' else v) for v in f))]=hu[f'face{t}']
  for den in [10**5,10**6]:
    faceMax={f:up(v,den) for f,v in fmap.items()}
    secMax={j:up(hu[f'ring{(j+off)%9}'],den) for j in range(9)}
    swMax=batch if (cls=='q1bal' and k==7) else {j:up(hu[f'switch{(j+off-1)%9}'],den) for j in range(9)}
    tot=T['sharp']+sum(faceMax.values())+sum(swMax.values())+sum(secMax.values())
    out[f'{tag}_den{den}']=dict(sharp=float(T['sharp']),faces=float(sum(faceMax.values())),switches=float(sum(swMax.values())),sectors=float(sum(secMax.values())),total=float(tot),slack=float(RT.PI_LO-tot),strict=tot<RT.PI_LO,
       faceMax={','.join(map(str,f)):f'{v.numerator}/{v.denominator}' for f,v in faceMax.items()},sectorMax={j:f'{v.numerator}/{v.denominator}' for j,v in secMax.items()},switchMax={j:f'{v.numerator}/{v.denominator}' for j,v in swMax.items()})
  hist_total=float(T['const'])*math.pi+2*float(T['eta'])*math.asin(0.76)+sum(hu.values())
  out[f'{tag}_hist_float_total']=hist_total
json.dump(out,open(Path(__file__).parent.parent/'data'/'budget.json','w'),indent=1)
for kk,v in out.items():
  print(kk, v if not isinstance(v,dict) else {a:v[a] for a in ['sharp','faces','switches','sectors','total','slack','strict']})
