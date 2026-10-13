"""Exact independent verifier: no scipy, no producer imports, no polytope vertices."""
import json,hashlib
from pathlib import Path
from fractions import Fraction as F
import q11_chord_flow_fraction_replay as const
P=Path(__file__).resolve().parent;src=P/'q10-halfspace-angle-dual.json';cert=json.loads(src.read_text());dom=P/'q10-c1366-domain.json';assert cert['domain_sha256']==hashlib.sha256(dom.read_bytes()).hexdigest();p=json.loads(dom.read_text())['polytope']
def value(t):
 a,b,c=map(F,t);assert b==0 and a+10*c==0;return -c
N=[list(map(F,n))for n,b,name in p['inequalities']];rhs=[value(b)for n,b,name in p['inequalities']]
assert list(map(F,p['equality'][0]))==[1]*10 and value(p['equality'][1])==1
for i in range(10):assert any(n==[int(i==j)for j in range(10)] and b==0 for n,b in zip(N,rhs))
assert len(cert['rows'])==10 and {r['production_anchor']for r in cert['rows']}==set(range(10))
ref=list(map(F,json.loads((P/'q10-adaptive-flow-interval.json').read_text())['theta0']));bounds=[]
# Evaluate the affine angular expression by its two symbolic constants L, pi.
for row in cert['rows']:
 j=row['production_anchor'];assert row['literal_anchor']==(j+2)%10;ex=[]
 assert [d['sign']for d in row['dual']]==[1,-1]
 for d in row['dual']:
  sign=d['sign'];lam=F(d['lambda_value']);y=[F(0)]*len(N);ids=[]
  for k,v in d['multipliers']:assert k not in ids;ids.append(k);y[k]=F(v);assert y[k]<=0
  c=[sign*(F(9-i,10)-int(i<j))for i in range(10)]
  residual=[c[i]-lam-sum(yk*n[i]for yk,n in zip(y,N))for i in range(10)];v=sum(yk*b for yk,b in zip(y,rhs))+lam+max(residual);assert v==F(d['upper']);ex.append(v)
 low,high=-ex[1],ex[0];angles=[]
 # Domain of (s,L,pi) is Cartesian outerbox; multi-affine extrema at8corners.
 for s in [low,high]:
  for L in const.L:
   for pi in const.pi:
    refs=[ref[(k+2)%10]+(2*pi if k>=3 else 0)for k in range(10)];mean=sum(refs)/10
    angles.append((F(j)-F(9,2))*L+(10*L-2*pi)*s-refs[j]+mean)
 lo,hi=min(angles),max(angles);assert lo>-F(1,200) and hi<F(1,200);assert F(row['delta_lower'])<=lo<=hi<=F(row['delta_upper'])
 bounds.append([str(lo),str(hi)])
(P/'q10-halfspace-angle-dual-replay.json').write_text(json.dumps(dict(status='exact_halfspace_dual_replay',source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),bounds=bounds,scope='Everypointofhalfspaceintersection; novertexenumeration, noLPoptimalityneeded; constantsmodule shared.'),indent=2));print('20rationaldualsverified','maxabs',float(max(abs(F(v))for b in bounds for v in b)))
