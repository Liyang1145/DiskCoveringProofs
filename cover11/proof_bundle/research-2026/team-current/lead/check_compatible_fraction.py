"""Independent exact rational control for the compatible-position certificate.
math.acos only proposes a tangent point; all validity checks use Fraction series bounds.
"""
from fractions import Fraction as Q
from math import factorial,comb,acos
from pathlib import Path
import json
P=Path(__file__).parent;R=Q(19,50);R2=R*R;DEN=10**15;N=16384;h=Q(22,7*N);plo=Q(314159,100000);phi=Q(22,7)
def down(x):return Q(x.numerator*DEN//x.denominator,DEN)
def up(x):return -down(-x)
def sin_bounds(x):
 assert 0<=x<=phi
 t=x;s=t
 for j in range(1,13):t=-t*x*x/((2*j)*(2*j+1));s+=t
 e=x**27/factorial(27);return down(s-e),up(s+e)
def cos_bounds(x):
 assert 0<=x<=phi
 t=Q(1);s=t
 for j in range(1,14):t=-t*x*x/((2*j-1)*(2*j));s+=t
 e=x**28/factorial(28);return down(s-e),up(s+e)
def asin_up(x,m=14):
 assert 0<=x<1
 return up(sum(Q(comb(2*n,n),4**n*(2*n+1))*x**(2*n+1) for n in range(m))+x**(2*m+1)/(1-x*x))
row=next(j for j in json.loads((P/'edge_compatible_dual.json').read_text()) if j['start']==7 and j['span']==3)
z=[Q(f'{v:.10f}') for v in row['z']];faces=row['faces'];edges=row['edges'];nf=len(faces)
core=[8,0,2,3,4,5,6,7];expected=[(0,1,2)]+[(9,core[k],core[k+1]) for k in range(3)]+[(10,core[k],core[(k+1)%8]) for k in range(3,8)]+[(9,10,8),(9,10,3)]
assert sorted(tuple(sorted(f)) for f in faces)==sorted(tuple(sorted(f)) for f in expected)
assert sorted(tuple(e) for e in edges)==sorted({tuple(sorted((f[k],f[(k+1)%3]))) for f in expected for k in range(3)})
mu=z[:11];nu=z[11:11+nf];lam,eta=z[-2:];assert lam>=0 and eta>=0
coef=sum(mu[:9])+2*sum(mu[9:])+sum(nu)-2*lam-2*eta
ub=coef*(plo if coef<0 else phi)+2*eta*asin_up(2*R,70)
for i,j in edges:
 adj=[(t,next(k for k in f if k not in (i,j))) for t,f in enumerate(faces) if i in f and j in f]
 t,k=adj[0];p=-nu[t]-mu[k]
 if len(adj)==2:t,k=adj[1];q=-nu[t]-mu[k]
 else:q=mu[i]+mu[j]
 c=(p+q)/2
 if c<=-R2:diag=Q(0)
 elif c>=R2:diag=c*phi
 else:
  t=Q(f'{acos(float(-c/R2)):.12f}');assert 0<=t<=plo;_,su=sin_bounds(t);cl,cu=cos_bounds(t)
  # concavity on [0,pi]: tangent + coarse bound on tangent slope error
  der=max(abs(R2*cl+c),abs(R2*cu+c));diag=R2*su+c*t+der*phi
 ub+=max(Q(0),p*(phi if p>=0 else plo),q*(phi if q>=0 else plo),diag)
mx=[Q(-1000)]*9
for k in range(N+1):
 a=h*k;_,su=sin_bounds(a);_,ssu=sin_bounds(a/2);v=min(R,R*max(Q(1,2),ssu));w=2*asin_up(v);sinlo,_=sin_bounds(w);F=R2*su/2+(w-sinlo)/2
 for i in range(9):mx[i]=max(mx[i],F+(lam+(eta if i>=3 else 0))*w-mu[i]*a)
# |W'| <= R/sqrt(1-R²)<.412; |F'|<=1.5R² on [0,22/7].
assert R2<Q(412,1000)**2*(1-R2)
for i in range(9):ub+=mx[i]+(3*R2/2+Q(412,1000)*(lam+(eta if i>=3 else 0))+abs(mu[i]))*h
assert ub<plo, float(ub)
coarse=Q((ub.numerator*10**6+ub.denominator-1)//ub.denominator,10**6)
res={'upper_rational':str(coarse),'upper_exact':str(ub),'pi_lower':'3.14159','strict':True,'N':N,'method':'exact Fraction series + analytic concave support tangent'}
(P/'compatible_position_fraction.json').write_text(json.dumps(res,indent=2));print('Fraction certified',str(coarse),' < 3.14159',flush=True)
