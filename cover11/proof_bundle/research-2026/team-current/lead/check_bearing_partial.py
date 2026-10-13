import sympy as S,json
from fractions import Fraction as F
from pathlib import Path
r,a,w=S.symbols('r a w',real=True);p=S.cos(w)-r*S.cos(a+w);x=-S.sin(w)+r*S.sin(a+w);q=2+r*r-2*r*S.cos(a)-2*p
eta_b=((1-p)*2*S.diff(x,a)+x*2*S.diff(p,a))/q
assert S.trigsimp(S.expand_trig(eta_b-2*r*(r+S.cos(a+w)-S.cos(a))/q))==0
assert S.trigsimp(2*S.diff(q,a)-4*r*(S.sin(a)-S.sin(a+w)))==0
v=F(69,100);ends=[F(5,8)+F(19,25)*v*v-F(943,625)*v,F(5,8)+F(19,25)-F(943,625)];assert all(t<0 for t in ends)
out={'eta_b_identity':True,'q_b_identity':True,'ridge_rational_convex_bounds':[str(t)for t in ends],'scope':'exactidentitiesandglobalridgefeasibilityarithmetic'};Path(__file__).with_name('bearing_partial_control.json').write_text(json.dumps(out,indent=2));print(out)
