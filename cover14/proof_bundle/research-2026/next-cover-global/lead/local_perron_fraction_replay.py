"""Exact weighted row-sum implication, independent of numerical eigenvector proposal."""
from fractions import Fraction as F
from pathlib import Path
import json,sys
import sympy as s
P=Path(__file__).resolve().parent
name=sys.argv[1]if len(sys.argv)>1 else 'local-neighborhood-directional-4e5.json'
x=json.loads((P/name).read_text());H=[[(F(a),F(b))for a,b in row]for row in x['transformed_H_intervals']];n=len(H);assert n==28
v=list(map(F,x['perron_weights']));assert len(v)==n and min(v)>0
errors=[]
for i in range(n):
 row=[]
 for j in range(n):
  a,b=H[i][j];assert a<=b;assert max(a,H[j][i][0])<=min(b,H[j][i][1]);row.append(max(abs(a-F(i==j)),abs(b-F(i==j))))
 errors.append(row)
bound=max(sum(errors[i][j]*v[j]for j in range(n))/v[i]for i in range(n));assert bound==F(x['perron_bound']) and bound<1
# For any real symmetric M in the supplied intervals, |M-I|v<=bound*v.
# Weighted infinity operator bound controls every eigenvalue of M-I; M positive definite.
W=s.Matrix([[s.Rational(t)for t in row]for row in x['W_exact']]);rank=W.rank();assert rank==28
out={'status':'exact_fraction_weighted_matrix_implication_verified','source':name,'epsilon':x['epsilon'],'bound_exact':str(bound),'bound_display':float(bound),'exact_congruence_rank':rank,'scope':'Matrix implication only; analytic KKT and AD geometric interval correctness remain separate inherited premises.'};path=P/(Path(name).stem+'-fraction-replay.json');path.write_text(json.dumps(out,indent=2));print('exact perron matrix verified',float(bound),'rank',rank)
