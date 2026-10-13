"""Independent Fraction interval replay of affine-flow Hessian; no producerarithmetic imported."""
import json,math,hashlib
from fractions import Fraction as Q
from pathlib import Path
P=Path(__file__).resolve().parent;src=P/'q10-adaptive-flow-interval.json';a=json.loads(src.read_text());jet=json.loads((P/'q10-adaptive-flow-jet.json').read_text());raw=json.loads((P/'fixed-anchor-convex-probe.json').read_text())['runs'][0]
cat=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][879]['faces'];sm=[7,5,1,8,0,4,6,2,9,3,13,11,12,10];am=[(j+2)%10 for j in range(10)]
assert {tuple(sorted(sm[i]for i in f))for f in cat}=={tuple(sorted(f))for f in raw['faces']}
assert all({sm[j],sm[(j+1)%10]}==set(raw['owners'][am[j]])for j in range(10))
faces=[raw['faces'][i]for i in[0,2,3,5,6,8,9,11]];owners=raw['owners'];ids=[i for i in range(22)if i not in[8,9]];edges=[]
for f,vs in enumerate(faces):
 for v in vs:edges.append((v,14+f,None))
for j,vs in enumerate(owners):
 for v in vs:edges.append((v,None,j))
core=[(k,e)for k,e in enumerate(edges)if e[0]not in[8,9]];assert [k for k,e in core]==jet['edges']and len(core)==40
z=[[Q(x)for x in p]for p in a['flow']];T=[[[Q(x)for x in rr]for rr in e]for e in a['jet']];V=[[Q(x)for x in rr]for rr in a['V']];eps=Q(a['epsilon']);kap=Q(a['kappa']);U=Q('.33173203427623414');th=list(map(Q,a['theta0']))
for v in ids:
 for k in range(2):
  for j in range(-1,10):
   assert sum((int(e[0]==v)-int(e[1]==v))*(z[l][k]if j<0 else T[l][k][j])for l,(_,e)in enumerate(core))==0
assert all(sum(V[i][j]for i in range(10))==0 for j in range(9))
# Prove basisrank9 byexact elimination first9rows.
M=[rr[:]for rr in V[:9]]
for j in range(9):
 k=next(k for k in range(j,9)if M[k][j]);M[j],M[k]=M[k],M[j];q=M[j][j];M[j]=[x/q for x in M[j]]
 for k in range(j+1,9):
  q=M[k][j];M[k]=[x-q*y for x,y in zip(M[k],M[j])]
S=10**55
def rd(a,b):return(Q(a.numerator*S//a.denominator,S),Q(-((-b.numerator*S)//b.denominator),S))
def pt(x):x=Q(x);return(x,x)
def add(x,y):return rd(x[0]+y[0],x[1]+y[1])
def neg(x):return(-x[1],-x[0])
def sub(x,y):return add(x,neg(y))
def mul(x,y):v=[a*b for a in x for b in y];return rd(min(v),max(v))
def div(x,y):assert y[0]>0;return mul(x,(1/y[1],1/y[0]))
def sqrt(x):
 assert x[0]>0;k=math.isqrt(x[0].numerator*S*S//x[0].denominator);h=math.isqrt(x[1].numerator*S*S//x[1].denominator)+1;return(Q(k,S),Q(h,S))
def summ(xs):
 r=pt(0)
 for x in xs:r=add(r,x)
 return r
# Independent direct Taylor, rationalangle |t|<4, no producertrig helper.
def trig(t):
 assert abs(t)<4
 co=sum((-1)**k*t**(2*k)/math.factorial(2*k)for k in range(80));si=sum((-1)**k*t**(2*k+1)/math.factorial(2*k+1)for k in range(80));ec=abs(t)**160/math.factorial(160);es=abs(t)**161/math.factorial(161)
 return [rd(co-ec,co+ec),rd(si-es,si+es)]
Ac=[trig(t)for t in th];A=[[add(x,(-eps,eps))for x in aa]for aa in Ac]
Z=[[add(pt(z[e][k]),(-eps*sum(map(abs,T[e][k])),eps*sum(map(abs,T[e][k]))))for k in range(2)]for e in range(40)]
TV=[[[sum(T[e][k][l]*V[l][i]for l in range(10))for i in range(9)]for k in range(2)]for e in range(40)]
H=[[pt(-kap*sum(V[l][i]*V[l][j]for l in range(10)))for j in range(9)]for i in range(9)];f0=pt(0);grad=[pt(0)for _ in range(10)]
for e,(_,edge)in enumerate(core):
 zz=Z[e];n=sqrt(summ(mul(x,x)for x in zz));n3=mul(mul(n,n),n);cross=[sub(mul(zz[0],pt(TV[e][1][i])),mul(zz[1],pt(TV[e][0][i])))for i in range(9)]
 for i in range(9):
  for j in range(9):H[i][j]=sub(H[i][j],div(mul(pt(U),mul(cross[i],cross[j])),n3))
 n0=sqrt(pt(sum(x*x for x in z[e])));f0=sub(f0,mul(pt(U),n0))
 for j in range(10):grad[j]=sub(grad[j],div(pt(U*sum(z[e][k]*T[e][k][j]for k in range(2))),n0))
 anchor=edge[2]
 if anchor is not None:
  d2=summ(mul(A[anchor][k],zz[k])for k in range(2));der=[A[anchor][1],neg(A[anchor][0])];mix=[summ(mul(der[k],pt(TV[e][k][i]))for k in range(2))for i in range(9)]
  for i in range(9):
   for j in range(9):H[i][j]=add(H[i][j],summ([mul(pt(V[anchor][i]*V[anchor][j]),d2),mul(pt(V[anchor][i]),mix[j]),mul(pt(V[anchor][j]),mix[i])]))
  f0=sub(f0,summ(mul(Ac[anchor][k],pt(z[e][k]))for k in range(2)))
  for j in range(10):grad[j]=sub(grad[j],summ(mul(Ac[anchor][k],pt(T[e][k][j]))for k in range(2)))
  grad[anchor]=add(grad[anchor],sub(mul(Ac[anchor][1],pt(z[e][0])),mul(Ac[anchor][0],pt(z[e][1]))))
b=max(sum(max(abs(lo-int(i==j)),abs(hi-int(i==j)))for j,(lo,hi)in enumerate(rr))for i,rr in enumerate(H));assert b<1
out=dict(status='independent_fraction_hessian_replay',source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),epsilon=str(eps),kappa=str(kap),row_bound=str(b),row_bound_display=float(b),f0=list(map(str,f0)),gradient=[list(map(str,x))for x in grad],edges_verified=len(core),exactbalance=True,exactbasisrank=9,disclosure='IndependentdecimaldirectedFractionarithmetic andtrigTaylor; readsproducerrepairedrationalflow/jet/basis, rebuildsincidencesfromliteralgraph. Hessianformulaanalyticcrossproductshared, notindependenttheorem.')
(P/'q10-adaptive-flow-fraction-audit.json').write_text(json.dumps(out,indent=2));print(out['status'],float(b),list(map(float,f0)))
