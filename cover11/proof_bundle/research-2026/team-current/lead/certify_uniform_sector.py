"""Exact rational flow correction + interval arc support; not a solver certificate.
Independent 51-edge reconstruction. Certifies one angular box only.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import deque
import json
from mpmath import mp,iv
mp.dps=70;iv.dps=60
P=Path(__file__).resolve().parent
src=json.loads((P.parent/'r20-alternative/socp_sector_export.json').read_text())['runs']['0.02']
faces=[[9,k,k+1] for k in range(4)]+[[10,k,(k+1)%9] for k in range(4,9)]+[[9,10,0],[9,10,4]]
# nodes anchors0..8 sites9..19 auxiliaries20..30
edges=[]
for s in range(9):edges.extend([(9+s,s),(9+s,(s-1)%9)])
for j,face in enumerate(faces):edges.extend((9+s,20+j) for s in face)
p=[[F(round(float(v)*10**12),10**12) for v in row] for row in src['p_51']]
def balances(p):
 b=[[F(0),F(0)] for _ in range(31)]
 for (v,w),q in zip(edges,p):
  for k in range(2):b[v][k]+=q[k];b[w][k]-=q[k]
 return b
b=balances(p);before=max(abs(v) for row in b[9:] for v in row)
adj=[[] for _ in range(31)]
for j,(v,w) in enumerate(edges):adj[v].append((w,j));adj[w].append((v,j))
parent={i:None for i in range(9)};queue=deque(range(9));order=[]
while queue:
 v=queue.popleft();order.append(v)
 for w,j in adj[v]:
  if w not in parent:parent[w]=(v,j);queue.append(w)
assert len(parent)==31
for v in reversed(order):
 if v<9:continue
 w,j=parent[v];sgn=1 if edges[j][0]==v else -1
 for k in range(2):
  p[j][k]-=sgn*b[v][k];b[w][k]+=b[v][k];b[v][k]=0
b=balances(p);assert all(v==0 for row in b[9:] for v in row)
def I(q):return iv.mpf(q.numerator)/q.denominator
def lo(x):return mp.mpf(x.a)
def hi(x):return mp.mpf(x.b)
norm=sum(iv.sqrt(sum(I(v)**2 for v in row)) for row in p)
# Exact rational normalization exceeds interval norm upper endpoint.
B=F(str(mp.ceil(hi(norm)*10**12)+1))/10**12
assert I(B)>norm
p=[[v/B for v in row] for row in p];b=balances(p)
assert all(v==0 for row in b[9:] for v in row)
assert sum(iv.sqrt(sum(I(v)**2 for v in row)) for row in p)<1
h=iv.mpf(1)/50;terms=[]
for i in range(9):
 t=2*iv.pi*i/9;n=(iv.cos(t),iv.sin(t));tan=(-n[1],n[0]);a=sum(I(b[i][k])*n[k] for k in range(2));d=sum(I(b[i][k])*tan[k] for k in range(2))
 if i==0:term=a
 elif lo(a)>=0:term=a*iv.cos(h)-abs(d)*iv.sin(h)
 elif hi(a)<=0:term=a-abs(d)*iv.sin(h)
 else:term=a-abs(a)*(1-iv.cos(h))-abs(d)*iv.sin(h)
 terms.append(term)
lb=sum(terms)
assert lb>iv.mpf(39)/100,lb
out={'scope':'all independent angles |theta_i-2pi*i/9|<=1/50 for i1..8, theta0=0; canonical explicit51 graph; lowerbound on oracle radius not squared. No other angular boxes excluded.', 'radius_lower_gt_39_over_100':True,'lower_interval_diagnostic':[str(lo(lb)),str(hi(lb))],'normalization_rational':str(B),'initial_free_imbalance':str(before),'exact_free_balance':True,'forces_rational':[[str(v) for v in row] for row in p],'edges':edges,'faces':faces}
(P/'uniform_sector_certificate.json').write_text(json.dumps(out,indent=2))
print({k:v for k,v in out.items() if k not in ['forces_rational','edges','faces']})
