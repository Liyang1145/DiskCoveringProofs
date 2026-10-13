"""Rigorous convex-quadratic upper by component secants + rational LP residual.
If l<=h<=u, h²<=(l+u)h-lu. Sum affine majorants, maximize over exact DBM.
For Ay<=b,y simplex,lambda>=0: f0+c.y <= f0+lambda.b+max(c-A^Tlambda).
No false unconstrained convex quadratic dual.
"""
from cosine_dbm_pilot import *
def bound(db):
 c=[iv.mpf(0) for _ in range(9)];f0=iv.mpf(0);box=iv.mpf(0)
 for k in range(8):
  i=(k-2)%9;constant=(i-6)*L-(ROOT_ANGLES[i]-ROOT_ANGLES[6]);tt=iv.mpf([lo(I(-db[i][6])),hi(I(db[6][i]))]);hh=constant-D*tt
  # mp endpoints carry more bits than iv, but convert exact binary mp tuples via mp rational.
  def frac(v):
   s,m,e,b=v._mpf_;return (-1 if s else 1)*F(int(m))*F(2)**int(e)
  l,u=frac(lo(hh)),frac(hi(hh));s=l+u
  box+=hh**2;f0+=I(s)*constant-I(l*u)
  for j in range(min(i,6),max(i,6)):c[j]+=(-1 if i>6 else 1)*I(s)*D
 A,b=domain_rows(db);cn=np.array([float((lo(v)+hi(v))/2) for v in c]);r=linprog(-cn,A_ub=np.array(A,dtype=float),b_ub=np.array(b,dtype=float),A_eq=np.ones((1,9)),b_eq=[1],bounds=[(0,None)]*9,method='highs');assert r.success
 lam=[F(max(0,round(-x*1e12)),10**12) for x in r.ineqlin.marginals];res=[c[k]-I(sum(lam[j]*A[j][k] for j in range(len(A)))) for k in range(9)]
 ub=hi(f0+I(sum(x*y for x,y in zip(lam,b)))+iv.mpf(max(hi(x) for x in res)))
 return {'upper':str(ub),'box_upper':str(hi(box)),'certified_C919':bool(iv.mpf(ub)<=I(F(191,25000))**2),'lambda':[str(x) for x in lam]}
if __name__=='__main__':
 d=json.loads((P/'cosine_dbm_cuts.json').read_text());rows=[]
 for n in d['nodes']:
  if n['status']=='open':rows.append({'node':n['id'],**bound([[F(x) for x in r] for r in n['db']])})
 (P/'dbm_norm_secant.json').write_text(json.dumps(rows,indent=2));print('cells',len(rows),'certified',sum(x['certified_C919'] for x in rows),'min norm',min(float(x['upper'])**.5 for x in rows))
