"""Exact rational/pi LP witness; no float-feasibility premise."""
from q11_reduced_closure_probe import *
from fractions import Fraction as F
v=[F(float(x/math.pi)).limit_denominator(1000000)for x in lp.x];dot=lambda row:sum((F(int(c))*x for c,x in zip(row,v)),F(0))
assert all(dot(row)==F(float(b/math.pi)).limit_denominator(100)for row,b in zip(eq,rhs))
assert all(dot(row)<=F(float(b/math.pi)).limit_denominator(100)for row,b in zip(ineq,br))
assert v[-1]>0 and all(0<x<1 for x in v[:-1])
out={'status':'exact_rational_pi_coherent_witness','graph_index':58,'q':q,'real_faces':nf,'edges':ne,'epsilon_over_pi':str(v[-1]),'beta_over_pi':list(map(str,v[:ne])),'face_incidence_order':fe,'h_over_pi':list(map(str,v[ne:-1])),'scope':'certifies strict positive-radius existence for every positive anchor assignment, NOT radius caps or cyclicity','equation_checks':len(eq),'inequality_checks':len(ineq),'cut_margin_lower_bound_over_pi':str(v[-1])};(P/'coherent-exact-witness.json').write_text(json.dumps(out,indent=2));print({k:val for k,val in out.items()if k not in ['beta_over_pi','h_over_pi','face_incidence_order']})
