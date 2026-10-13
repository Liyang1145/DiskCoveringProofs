"""Symbolic identity, exact known geometry and numeric candidate checks; no global certificate."""
from pathlib import Path
import json, math
import sympy as s
import numpy as np
P=Path(__file__).parent
x,y,A,k=s.symbols('x y A k',real=True)
r2=A*A+k*k
prod=((x+A)**2+y*y)*((x-A)**2+y*y)-4*y*y*r2
fact=(x*x+(y-k)**2-r2)*(x*x+(y+k)**2-r2)
assert s.expand(prod-fact)==0
Q=s.Rational
# a=(.3,.8), b=(-.3,.8), r=.5. Circle roots (0,.4),(0,1.2).
a=s.Matrix([Q(3,10),Q(4,5)]);b=s.Matrix([-Q(3,10),Q(4,5)]);r=Q(1,2)
pin=s.Matrix([0,Q(2,5)]);pout=s.Matrix([0,Q(6,5)])
assert (pin-a).dot(pin-a)==r*r and (pout-a).dot(pout-a)==r*r
assert pin.dot(pin)<1<pout.dot(pout)
controls=[]
for h in [s.Matrix([0,0]),s.Matrix([0,-Q(1,5)]),s.Matrix([Q(1,5),Q(1,10)])]:
 cross=s.det(s.Matrix.hstack(b-a,h-a))
 rho2=(a-b).dot(a-b)*(h-a).dot(h-a)*(h-b).dot(h-b)/(4*cross*cross)
 lhs=bool(rho2<=r*r);rhs=bool((h-pin).dot(h-pin)<=r*r)
 assert lhs==rhs and (h-pout).dot(h-pout)>r*r
 controls.append({'h':list(map(str,h)),'rho2':str(rho2),'feasible':lhs})
# numeric calibration of all9 neighboring ring roots, rational saved centers at allowance .38
obj=json.loads(Path('n11/upper/certified_object.json').read_text(encoding='utf-8'))
cs=np.array([[int(v)/1e17 for v in row] for row in obj['centers_scaled_1e17']])
ids=[i for i in range(11) if i not in (0,2)];ids.sort(key=lambda i:math.atan2(cs[i,1],cs[i,0]))
r=.38;rows=[]
for j,ia in enumerate(ids):
 ib=ids[(j+1)%9];a,b=cs[ia],cs[ib];m=(a+b)/2;d=np.linalg.norm(b-a);n=np.array([-(b-a)[1],(b-a)[0]])/d;k=math.sqrt(r*r-d*d/4)
 roots=[m-k*n,m+k*n];roots.sort(key=np.linalg.norm);pi,po=roots
 assert np.linalg.norm(pi)<1<np.linalg.norm(po)
 hubchecks=[]
 for ih in (0,2):
  h=cs[ih];cross=np.linalg.det(np.column_stack((b-a,h-a)));rho=d*np.linalg.norm(h-a)*np.linalg.norm(h-b)/(2*abs(cross))
  margin=r-np.linalg.norm(h-pi)
  assert (rho<=r)==(margin>=0)
  hubchecks.append({'hub':ih,'rho':rho,'disk_margin':margin})
 rows.append({'ring_pair':[ia,ib],'inner_norm':float(np.linalg.norm(pi)),'outer_norm':float(np.linalg.norm(po)),'hubs':hubchecks})
out={'scope':'symbolic identity, exact rational controls, numeric saved candidate at r=.38 only','identity':True,'exact_controls':controls,'candidate':rows}
(P/'r20_chain_convexification_controls.json').write_text(json.dumps(out,indent=2))
print('PASS symbolic identity;3 rational hub controls;9 candidate ring pairs/18 hub equivalences. min outer norm=',min(q['outer_norm'] for q in rows))
