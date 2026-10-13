"""Independent prefix reconstruction of currentpolytope mean-angle box."""
import json,hashlib
from fractions import Fraction as Q
from pathlib import Path
from area_safe_fraction_replay import L,pi,add,neg,mul,point
P=Path(__file__).resolve().parent;src=P/'q10-c1366-domain.json';dom=json.loads(src.read_text());poly=dom['polytope'];D=add(mul(point(10),L),neg(mul(point(2),pi)));th=list(map(Q,json.loads((P/'q10-quadratic-minorant-certificate.json').read_text())['theta0']))
# Reconstruct unwrapped angles and reorder to literal. subtract means onceperarray.
def minus(a,b):return add(a,neg(b))
reference=[]
for j in range(10):
 k=(j+2)%10;reference.append(add(point(th[k]),mul(point(2*int(j>=3)),pi)))
mean=mul(point(Q(1,10)),(sum(x[0]for x in reference),sum(x[1]for x in reference)));reference=[minus(x,mean)for x in reference];bounds=[]
for vertex in poly['vertex_set']:
 x=[]
 for row in vertex:
  a,b,c=map(Q,row);assert b==0 and a==-10*c;x.append(-c)
 assert sum(x)==1 and min(x)>=0
 phi=[point(0)];prefix=point(0)
 for j in range(1,10):
  prefix=add(prefix,mul(point(x[j-1]),D));phi.append(minus(mul(point(j),L),prefix))
 mean=mul(point(Q(1,10)),(sum(v[0]for v in phi),sum(v[1]for v in phi)));errors=[minus(minus(v,mean),reference[j])for j,v in enumerate(phi)];assert all(-Q(1,200)<v[0]<=v[1]<Q(1,200)for v in errors);bounds.append(errors)
out=dict(status='independent_prefix_angle_box_replay',source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),vertices=len(bounds),epsilon='1/200',maxabs=str(max(max(abs(a),abs(b))for rr in bounds for a,b in rr)),scope='conditional completeC1366polytope; directprefix angles andexactcyclicliteralmap; allaffinefunctions boundedatallvertices')
(P/'q10-angle-width-fraction-audit.json').write_text(json.dumps(out,indent=2));print(out['status'],float(Q(out['maxabs'])))
