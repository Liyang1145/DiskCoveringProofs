"""Diagnostic calibration, not continuum proof: direct point arcs vs interval upper."""
import hubline_capacity as H
from fractions import Fraction as F
import numpy as np,json,math,random
from pathlib import Path
p=json.loads((H.K.P/'evidence/hubline-point-0.json').read_text());W=p['proposal']['weights'];C=H.Certificate([(F(a),F(b)) for a,b in p['H']],W)
w=np.array([[float(F(v)) for v in r] for r in W]);s=.2;x=0;y=.0125;u=float(H.K.Uq);n=4;random.seed(14)
def direct(z,ph):
 rho=1-u+(math.sqrt(1-u*u)-(1-u))*z;al=math.acos(max(-1,min(1,(1+rho*rho-u*u)/(2*rho))))
 val=H.basis_arc(ph,al,True,n)@w[0]
 for j,(hx,ce) in enumerate([(x-s,math.pi),(x+s,0)]):
  dx=rho*math.cos(ph)-hx;dy=rho*math.sin(ph)-y;ell=math.hypot(dx,dy)
  if ell<2*u:val+=H.basis_arc_int(math.atan2(dy,dx),math.acos(ell/(2*u)),ce,math.pi-math.acos(s/u),True,n)@w[j+1]
 return float(val)
viol=[];mindiff=1;count=0
for i in range(500):
 z=F(random.randrange(10001),10000);q=F(random.randrange(10001),10000)
 if i<6:q=F(i%3,2);z=F(i//3)
 B=((z,z),(q,q));v=C.upper(B)
 assert v is not None
 exact=direct(float(z),2*math.pi*float(q));diff=float(v.b)-exact
 if diff < -1e-14:viol.append([str(B),diff])
 mindiff=min(mindiff,diff);count+=1
# Boxes with actual nonzero widths and arbitrary wrap/0/pi endpoints.
for i in range(100):
 z=F(random.randrange(9900),10000);q=F(random.randrange(9900),10000);dz=F(1,100);dq=F(1,100)
 v=C.upper(((z,z+dz),(q,q+dq)))
 if v is None:continue
 for j in range(9):
  exact=direct(float(z+dz*F(j%3,2)),2*math.pi*float(q+dq*F(j//3,2)));diff=float(v.b)-exact
  if diff < -1e-14:viol.append([i,j,diff])
  count+=1
out={'status':'diagnostic','points':count,'violations':viol,'minimum_point_difference_float':mindiff,'tolerance_float':1e-14}
print(json.dumps(out));(H.K.P/'evidence/hubline-controls.json').write_text(json.dumps(out,indent=2));assert not viol
