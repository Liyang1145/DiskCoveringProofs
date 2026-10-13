"""Exact polynomial controls for residual closure criterion. No floating tolerances."""
from pathlib import Path
import sympy as S,json
r,e=S.symbols('r e',positive=True)
dx,dy=S.symbols('dx dy',real=True)
cases=[('one',[S.Matrix([r,0])],S.Matrix([1,0])),('opposite',[S.Matrix([r,0]),S.Matrix([-r,0])],S.Matrix([0,1]))]
out=[]
for name,vs,d in cases:
 residuals=[S.expand(2*e*(v.dot(d))+e**2*d.dot(d)) for v in vs]
 assert all(S.ask(S.Q.positive(f)) for f in residuals)
 out.append({'case':name,'residuals':[str(f) for f in residuals]})
# Three normals sum to zero and span R2. Nonnegative dots would all be zero,
# forcing direction zero. So no admissible nonzero direction.
vs=[S.Matrix([r,0]),S.Matrix([-r/2,S.sqrt(3)*r/2]),S.Matrix([-r/2,-S.sqrt(3)*r/2])]
assert sum(vs,S.zeros(2,1))==S.zeros(2,1)
assert S.simplify(S.det(S.Matrix.hstack(vs[0],vs[1])))==S.sqrt(3)*r*r/2
out.append({'case':'three equilateral normals','sum':'exact zero','rank2_minor':str(S.sqrt(3)*r*r/2),'membership':False})
Path(__file__).with_name('r21_membership_control.json').write_text(json.dumps({'scope':'exact symbolic degenerate controls for analytic criterion','cases':out},indent=2))
print('exact controls: outward escape, opposite-normal quadratic escape, surrounded equality trap')
