"""Certified coupled simplex patch, using C911 stored rational forces only.
No optimization: interval evaluation of vertex-concavity bound.
"""
import json
from fractions import Fraction as F
from pathlib import Path
from mpmath import mp,iv
mp.dps=80; iv.dps=65
D=Path(__file__).resolve().parent
cert=json.loads((D/'uniform_sector_certificate.json').read_text())
faces=[[9,k,k+1] for k in range(4)]+[[10,k,(k+1)%9] for k in range(4,9)]+[[9,10,0],[9,10,4]]
edges=[e for s in range(9) for e in [(9+s,s),(9+s,(s-1)%9)]]+[(9+s,20+j) for j,f in enumerate(faces) for s in f]
assert edges==[tuple(e) for e in cert['edges']]
p=[[F(v) for v in row] for row in cert['forces_rational']]
b=[[F(0),F(0)] for _ in range(31)]
for (v,w),q in zip(edges,p):
 for k in range(2):b[v][k]+=q[k];b[w][k]-=q[k]
assert all(v==0 for row in b[9:] for v in row)
def I(x):
 x=F(x);return iv.mpf(x.numerator)/x.denominator
def lo(x):return mp.mpf(x.a)
def hi(x):return mp.mpf(x.b)
def interval(a,b):return iv.mpf([a,b])
norm=sum(iv.sqrt(sum(I(v)**2 for v in row)) for row in p)
assert norm<1
L=2*iv.asin(I(F(19,50))) if hasattr(iv,'asin') else 2*iv.atan2(I(F(19,50)),iv.sqrt(1-I(F(19,50))**2))
deficit=9*L-2*iv.pi
assert deficit>0

def evaluate(t):
 # y=(1-t)/9 * ones + t*e_j. Exact rational barycentric vertices.
 ys=[[F(1-t,9)+(t if i==j else 0) for i in range(9)] for j in range(9)]
 assert all(sum(y)==1 and min(y)>=0 for y in ys)
 theta=[[iv.mpf(0)] for _ in ys]
 for th,y in zip(theta,ys):
  for i in range(8):th.append(th[-1]+L-deficit*I(y[i]))
 ranges=[];kappas=[]
 for i in range(9):
  a=min(lo(th[i]) for th in theta);z=max(hi(th[i]) for th in theta)
  ranges.append(interval(z,z)-interval(a,a))
  th=interval(a,z)
  work=I(b[i][0])*iv.cos(th)+I(b[i][1])*iv.sin(th)
  kappas.append(max(mp.mpf(0),-lo(work)))
 works=[sum(I(b[i][0])*iv.cos(th[i])+I(b[i][1])*iv.sin(th[i]) for i in range(9)) for th in theta]
 penalty=sum(iv.mpf(k)*r*r/8 for k,r in zip(kappas,ranges))
 lower=iv.mpf(min(lo(w) for w in works))-penalty
 return {'t':str(t),'vertex_min_lower':str(min(lo(w) for w in works)),'kappa_upper':[str(k) for k in kappas],'penalty_upper':str(hi(penalty)),'lower':str(lo(lower)),'above_19_50':bool(lower>I(F(19,50))),'theta_vertices_diagnostic':[[str(lo(z)) for z in th] for th in theta]},lower
rows=[]
for n in range(1,101):
 row,lb=evaluate(F(n,100));rows.append(row)
passed=[r for r in rows if r['above_19_50']]
assert passed
best=passed[-1]
# Recompute selected rational t, no monotonicity or sample-to-continuum inference.
check,lower=evaluate(F(best['t']));assert lower>I(F(19,50))
out={'scope':'All y in conv{(1-t)/9 ones+t e_j}, widths=L-(9L-2pi)y, theta0=0; t='+best['t'], 'status':'proved-interval coupled simplex patch, NOT global P', 'best_tested_t':best,'all_trial_summaries':[{k:r[k] for k in ['t','lower','above_19_50']} for r in rows], 'norm_upper':str(hi(norm)),'repro':'py -3 -B research-2026/team-current/lead/certify_uniform_simplex.py'}
(D/'uniform_simplex_certificate.json').write_text(json.dumps(out,indent=2))
print(json.dumps({'t':best['t'],'lower':best['lower'],'kappa':best['kappa_upper'],'penalty':best['penalty_upper'],'scope':out['scope']},indent=2))
