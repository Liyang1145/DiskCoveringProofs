"""Exact algebra behind universal separation-axis stationary reduction."""
import sympy as s
from pathlib import Path
import json
x,y,d=s.symbols('x y d',real=True);a1,a2,b1,b2,c1,c2=s.symbols('a1 a2 beta1 beta2 c1 c2',real=True)
u=y-d/2;v=y+d/2;q1=x*x+u*u;q2=x*x+v*v;l1=s.sqrt(q1);l2=s.sqrt(q2)
# Differentiate angles by their exact generic differential, avoid branch assumptions.
gx=d/2+(2*b1+2*b2-c1/l1-c2/l2)*x+a1*u/q1-a2*v/q2
gy=(2*b1-c1/l1)*u+(2*b2-c2/l2)*v-a1*x/q1+a2*x/q2
cur=2*(b1+b2)-x*x*(c1/l1**3+c2/l2**3)+2*x*(a1*u/q1**2-a2*v/q2**2)
assert s.simplify(s.diff(gy,y)-cur)==0
assert s.simplify(s.diff(gx,y)-s.diff(gy,x))==0
Gx=(d/2+2*(b1+b2)*x)*q1*q2-x*(c1*l1*q2+c2*l2*q1)+a1*u*q2-a2*v*q1
Gy=(2*b1*u+2*b2*v)*q1*q2-c1*u*l1*q2-c2*v*l2*q1-a1*x*q2+a2*x*q1
assert s.simplify(Gx-gx*q1*q2)==0 and s.simplify(Gy-gy*q1*q2)==0
C=2*(b1+b2)*q1*q1*q2*q2-x*x*(c1*l1*q2*q2+c2*l2*q1*q1)+2*x*(a1*u*q2*q2-a2*v*q1*q1)
assert s.simplify(C-cur*(q1*q2)**2)==0
out={'mixed_derivatives_agree':True,'curvature_identity':True,'pole_cleared_equations':True,'scope':'algebraic identities, not stationary exclusion'}
Path(__file__).with_name('hub_axis_identity_control.json').write_text(json.dumps(out,indent=2));print(out)
