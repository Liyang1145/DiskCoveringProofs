"""Exact symbolic kernel controls for covering and strict-allowance reduction."""
from pathlib import Path
import sympy as s,json
P=Path(__file__).parent
R,d,t,c=s.symbols('R d t c',positive=True,real=True)
# For endpoint halfwidth cos(a)=c, d solves d²−2cd+1−R²=0.
D=s.symbols('D',real=True)
assert s.rem(1+d*d-2*d*t-R*R-2*d*(c-t),d*d-2*c*d+1-R*R,d)==0
# Roots obey dminus*dplus=1−R²; sign scale positive => strict coverage preserved.
a,b,l0,l1,l2,rho=s.symbols('a b l0 l1 l2 rho',real=True)
px=s.symbols('x0:3');py=s.symbols('y0:3');ls=[l0,l1,1-l0-l1];x=sum(ls[i]*px[i] for i in range(3));y=sum(ls[i]*py[i] for i in range(3))
expr=sum(ls[i]*((x-px[i])**2+(y-py[i])**2) for i in range(3))-(sum(ls[i]*(px[i]**2+py[i]**2) for i in range(3))-x*x-y*y)
assert s.expand(expr)==0
# Triangle radius inequality fan completion with X=cos s,Y=cos t,Z=cos theta.
X,Y,Z=s.symbols('X Y Z');lhs=X*X+Y*Y-2*X*Y*Z-(1-Z*Z);rhs=(Z-X*Y)**2-(1-X*X)*(1-Y*Y);assert s.expand(lhs-rhs)==0
out={'strict_boundary_root_identity':'zero exact polynomial remainder','barycentric_squared_distance_identity':'zero expanded polynomial','fan_radius_completion':'zero expanded polynomial','scope':'symbolic kernel identities; geometry hypotheses supplied by analytic documents'}
(P/'gluing_kernel_control.json').write_text(json.dumps(out,indent=2));print(out)
