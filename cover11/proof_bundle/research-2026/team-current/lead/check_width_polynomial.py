"""Exactsymbolic clearingdenominators and numericstationaryroot controls."""
from pathlib import Path
import sympy as S,json
P=Path(__file__).parent
y,d0,x0,c2,h,k,d,l,R=S.symbols('y d0 x0 c2 h k d l R',real=True);Q=1+y*y;pn=d0*(1-y*y)+2*x0*y;xn=x0*(1-y*y)-2*d0*y;dn=(1+c2)*Q-2*pn
An=dn*((1+2*h)*Q-pn)+2*k*(Q-pn)*Q+4*d*dn*xn/R**2
pp=pn/Q;xx=xn/Q;D=dn/Q;A=D*(1-pp+2*h)+2*k*(1-pp)+4*d*D*xx/R**2
assert S.cancel(An-Q**2*A)==0
G=An**2-4*l*l*dn*xn*xn*Q/R**2
assert S.cancel(G/Q**4-(A*A-4*l*l*D*xx*xx/R**2))==0
assert S.Poly(G,y).degree()<=8
out={'exactclearingidentity':True,'squaredidentity':True,'degree':S.Poly(G,y).degree(),'scope':'fixedouter stationary necessary polynomial only, no rootcoveragecertificate'};(P/'width_polynomial_control.json').write_text(json.dumps(out,indent=2));print(out)
