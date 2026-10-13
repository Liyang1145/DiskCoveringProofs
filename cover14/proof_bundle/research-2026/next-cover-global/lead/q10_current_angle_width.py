"""Sourcebound exactinterval currentdomain angularwidth vs newlocalcell; notexclusion."""
import json,hashlib
from fractions import Fraction as F
from pathlib import Path
from q10_rational_polytope_audit import decode
import q11_chord_flow_fraction_replay as fr
P=Path(__file__).resolve().parent;src=P/'q10-c1366-domain.json';V,cs=decode(json.loads(src.read_text())['polytope']);D=(10*fr.L[0]-2*fr.pi[1],10*fr.L[1]-2*fr.pi[0]);ref=list(map(F,json.loads((P/'q10-adaptive-flow-interval.json').read_text())['theta0']))
# Productionj->literalj+2mod10. Choosecycliclifts correspondingtoliteraltheta2,...,theta9,theta0+2pi,theta1+2pi.
a=[]
for j in range(10):
 k=(j+2)%10;t=(ref[k],ref[k]);lift=0 if j<3 else 1
 # literaltheta5..9 principalnegative need+2pi; literal0,1afterwrap alsoneed+2pi
 a.append((t[0]+2*lift*fr.pi[0],t[1]+2*lift*fr.pi[1]))
mean=(sum(x[0]for x in a)/10,sum(x[1]for x in a)/10);target=[(lo-mean[1],hi-mean[0])for lo,hi in a]
out=[]
for j in range(10):
 coeff=[F(9-i,10)-int(i<j)for i in range(10)];vals=[]
 for v in V:
  s=sum(c*x for c,x in zip(coeff,v));base=(F(2*j-9,2)*fr.L[0],F(2*j-9,2)*fr.L[1]);base=(min(base),max(base));z=(s*D[0],s*D[1]);vals.append((base[0]+min(z)-target[j][1],base[1]+max(z)-target[j][0]))
 out.append(dict(production_anchor=j,literal_anchor=(j+2)%10,delta_lower=str(min(x[0]for x in vals)),delta_upper=str(max(x[1]for x in vals))))
(P/'q10-current-angle-width.json').write_text(json.dumps(dict(status='interval_domain_diagnostic_noexclusion',source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),vertices=len(V),bounds=out),indent=2));print([(x['production_anchor'],float(F(x['delta_lower'])),float(F(x['delta_upper'])))for x in out])
