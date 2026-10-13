"""Direct rational LP-dual angle box, no vertex-list/completeness premise.
Floating LP proposes multipliers; rational residual on simplex is bounded exactly.
"""
import json,hashlib
from pathlib import Path
from fractions import Fraction as Q
import numpy as np
from scipy.optimize import linprog
import q11_chord_flow_fraction_replay as fr
P=Path(__file__).resolve().parent;src=P/'q10-c1366-domain.json';obj=json.loads(src.read_text())['polytope']
def scalar(t):
 a,b,c=map(Q,t);assert b==0 and a==-10*c;return -c
N=[list(map(Q,row[0]))for row in obj['inequalities']];rhs=[scalar(row[1])for row in obj['inequalities']]
assert list(map(Q,obj['equality'][0]))==[1]*10 and scalar(obj['equality'][1])==1
# Explicitly check the simplex nonnegativity assumptions used to bound residual.
assert all(any(n==[Q(int(i==j))for i in range(10)]and b==0 for n,b in zip(N,rhs))for j in range(10))
D=(10*fr.L[0]-2*fr.pi[1],10*fr.L[1]-2*fr.pi[0]);assert D[0]>0
th=list(map(Q,json.loads((P/'q10-adaptive-flow-interval.json').read_text())['theta0']))
ref=[(th[(j+2)%10]+(2*fr.pi[0]if j>=3 else 0),th[(j+2)%10]+(2*fr.pi[1]if j>=3 else 0))for j in range(10)]
mean=(sum(x[0]for x in ref)/10,sum(x[1]for x in ref)/10);target=[(a-mean[1],b-mean[0])for a,b in ref]
rows=[]
for j in range(10):
 c=[Q(9-i,10)-int(i<j)for i in range(10)];certs=[]
 for sign in [1,-1]:
  cc=[sign*x for x in c]
  sol=linprog(-np.array(cc,dtype=float),A_ub=-np.array(N,dtype=float),b_ub=-np.array(rhs,dtype=float),A_eq=np.ones((1,10)),b_eq=[1],bounds=[(None,None)]*10,method='highs');assert sol.success
  y=[min(Q(0),Q(format(v,'.16g')))for v in sol.ineqlin.marginals];lam=-Q(format(sol.eqlin.marginals[0],'.16g'))
  residual=[cc[i]-sum(y[k]*N[k][i]for k in range(len(N)))-lam for i in range(10)]
  bound=sum(a*b for a,b in zip(y,rhs))+lam+max(residual)
  # y<=0 and N*x>=rhs imply c*x<=y*rhs+lambda+max(residual), x in simplex.
  certs.append(dict(sign=sign,upper=str(bound),multipliers=[[k,str(v)]for k,v in enumerate(y)if v],lambda_value=str(lam),residual_upper=str(max(residual))))
 slo=-Q(certs[1]['upper']);shi=Q(certs[0]['upper']);prod=[s*d for s in [slo,shi]for d in D];base=[Q(2*j-9,2)*v for v in fr.L]
 lo=min(base)+min(prod)-target[j][1];hi=max(base)+max(prod)-target[j][0];assert -Q(1,200)<lo<=hi<Q(1,200)
 rows.append(dict(production_anchor=j,literal_anchor=(j+2)%10,delta_lower=str(lo),delta_upper=str(hi),dual=certs))
out=dict(status='exact_halfspace_dual_angle_box_no_vertices',domain_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),epsilon='1/200',rows=rows,scope='Every x satisfying stored128halfspaces andsumx1; novertexlistcompleteness used. Necessityofhalfspaces inheritedseparately.')
(P/'q10-halfspace-angle-dual.json').write_text(json.dumps(out,indent=2));print('maxabs',max(float(max(abs(Q(r['delta_lower'])),abs(Q(r['delta_upper']))))for r in rows),'certificates',2*len(rows))
