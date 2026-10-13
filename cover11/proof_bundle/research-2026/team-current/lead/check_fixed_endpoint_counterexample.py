"""Exact algebraic control of fixed-endpoint saturation counterexample; robustness is analytic."""
from pathlib import Path
import json
import sympy as s
P=Path(__file__).parent
r=s.Rational(3,8);q=s.sqrt(55)/8;H=s.Matrix([s.Rational(1,2),0]);c=s.Matrix([q,0]);L=s.Matrix([23*s.sqrt(55)/256,s.Rational(165,256)])
u=c-H;v=L-H;area=s.det(s.Matrix.hstack(u,v));Rc2=s.simplify(u.dot(u)*v.dot(v)*(c-L).dot(c-L)/(4*area**2))
assert s.simplify(Rc2-(s.Rational(71,220)-23*s.sqrt(55)/880))==0
assert 55*92**2>641**2
assert s.simplify(L.dot(L)-q*q)==0
U=s.Matrix([q,r]);assert s.simplify((U-c).dot(U-c)-r*r)==0
assert s.simplify((U-L).dot(U-L)-r*r)==0
out={'r':str(r),'q':str(q),'Rc_squared':str(Rc2),'slack_squared':str(s.simplify(r*r-Rc2)),'area_determinant':str(s.simplify(area)),'strict_slack_integer_control':[55*92**2,641**2],'scope':'exact algebraic base example; strict inward nearby family follows uniform lens confinement and continuity, not sampling'}
(P/'fixed_endpoint_counterexample.json').write_text(json.dumps(out,indent=2));print(out)
