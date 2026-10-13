"""Exactalgebra checks independent of geometricnumericcalibration."""
import sympy as S,json
from pathlib import Path
p,mu1,mu3,h1,h3,b1,b3,de,w1,w3,eta1,eta3,r,s,x1,x3,u1,u3,d1,d3,l1,l3=S.symbols('phi mu1 mu3 h1 h3 b1 b3 de w1 w3 eta1 eta3 r s x1 x3 u1 u3 d1 d3 l1 l3')
# suppresscommon gaugeconstantpi(z113+z114-z2) andFH
old=mu1*(2*b1-S.pi-de)+mu3*(2*b3-S.pi+de)+p-r*s+r*r*(S.sin(2*b1)+S.sin(2*b3))/2
for b,w,eta,x,mu,h,u,d,l in [(b1,w1,eta1,x1,mu1,h1,u1,d1,l1),(b3,w3,eta3,x3,mu3,h3,u3,d3,l3)]:
 X=r*r*S.sin(2*b)-r*s*S.cos(2*b)
 old+=(w+x-X)/2-mu*(w+2*b+p-S.pi/2-eta)-d*u*u-l*u+h*(S.pi/2+eta)
new=S.pi/2*(h1+h3-mu1-mu3)+(1-mu1-mu3)*p+(mu3-mu1)*de-r*s*(S.sin(b1)**2+S.sin(b3)**2)
for w,eta,x,mu,h,u,d,l in [(w1,eta1,x1,mu1,h1,u1,d1,l1),(w3,eta3,x3,mu3,h3,u3,d3,l3)]:new+=(S.Rational(1,2)-mu)*w+x/2+(mu+h)*eta-d*u*u-l*u
assert S.trigsimp(S.expand(old-new))==0
xx,ww=S.symbols('x w');dsq=2+r*r-2*r*S.cos(xx)-2*((1-r*S.cos(xx))*S.cos(ww)+r*S.sin(xx)*S.sin(ww));dalt=r*r+4*S.sin(ww/2)**2-4*r*S.sin(xx+ww/2)*S.sin(ww/2)
assert S.trigsimp(S.expand_trig(dsq-dalt))==0
out={'fullobjectivecancellation':True,'distancehalfangleidentity':True,'scope':'exactsymbolicidentities,notinequality'};Path(__file__).with_name('patch_cancellation_control.json').write_text(json.dumps(out,indent=2));print(out)
