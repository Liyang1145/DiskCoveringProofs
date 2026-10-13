"""Independent exact matrix implication replay; does not independently recompute geometric derivative enclosures."""
from fractions import Fraction as F
from pathlib import Path
import json,sympy as s
P=Path(__file__).resolve().parent
x=json.loads((P/'local-neighborhood-factored-2e5.json').read_text());H=[[(F(a),F(b))for a,b in row]for row in x['transformed_H_intervals']];n=len(H);assert n==28 and all(len(row)==n for row in H)
bound=F(0)
for i in range(n):
 for j in range(n):
  a,b=H[i][j];assert a<=b;assert max(a,H[j][i][0])<=min(b,H[j][i][1]);d=F(i==j);bound+=max(abs(a-d),abs(b-d))**2
assert bound==F(x['frobenius_error_squared_upper_exact']) and bound<1
W=s.Matrix([[s.Rational(v)for v in row]for row in x['W_exact']]);rank=W.rank();assert rank==28
out={'status':'exact_fraction_matrix_implication_verified','epsilon':x['epsilon'],'bound_exact':str(bound),'bound_display':float(bound),'exact_congruence_rank':rank,'scope':'Verifies saved intervalmatrix implies positive definiteness. Geometry/AD enclosure correctness is separate inherited premise.'};(P/'local-matrix-fraction-replay.json').write_text(json.dumps(out,indent=2));print('exact matrix verified bound',float(bound),'rank',rank)
