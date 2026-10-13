"""Independent symbolic norm identity + actual chord-coordinate calibration."""
from pathlib import Path
import sympy as S,math,random,json
P=Path(__file__).parent;k,h,H,y=S.symbols('k h H y',real=True)
p2=H**2+(h-y)**2;q2=H**2+(h+y)**2;dot=H**2+y*y-h*h;cross=2*h*H
expr=(k-H)**2+y*y-(1+dot-k*cross/h)
assert S.expand(expr)==k*k+h*h-1
rng=random.Random(846);error=0.;violation=0.;n=0
for _ in range(3000):
 r=rng.uniform(.375,.37999);w=rng.uniform(.04661754,2*math.asin(r));hh=math.sin(w/2);kk=math.cos(w/2);ss=math.sqrt(1-r*r)
 # arbitrary inward center, not necessarily covered; norm equivalence holds regardless
 rr=ss*math.sqrt(rng.random());t=rng.random()*2*math.pi;x,yy=rr*math.cos(t),rr*math.sin(t);HH=kk-x
 pp=math.hypot(HH,hh-yy);qq=math.hypot(HH,hh+yy);a=math.atan2(2*hh*HH,HH*HH+yy*yy-hh*hh)
 lhs=pp*qq*math.sin(a-w/2);res=lhs-(1-x*x-yy*yy)*hh;error=max(error,abs(res));assert lhs>=r*r*hh-1e-14
 if pp<=r and qq<=r:
  n+=1;u=pp/.38;v=qq/.38;L=u*v*(kk*math.sin(a)-hh*math.cos(a));rhs=max((75/76)**2,u*u,v*v)*hh;violation=max(violation,rhs-L);assert L>=rhs-1e-13
out={'exact_identity_remainder':'k²+h²−1','numeric_identity_error':error,'actual_covered_controls':n,'max_necessary_inequality_violation':violation,'scope':'exact algebra and3000geometric calibrationpoints; proof in INWARD-SECTOR-COUPLING.md'}
(P/'inward_sector_coupling_control.json').write_text(json.dumps(out,indent=2));print(out)
