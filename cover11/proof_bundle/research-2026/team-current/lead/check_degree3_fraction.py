"""Independent rational certificate: no mpmath, scipy, numerical pi or transcendental calls.
Uses elementary power series with rigorous tails and rational Lipschitz grid error.
"""
from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
import json
P=Path(__file__).parent;R=Q(19,50);R2=R*R;N=1024;h=Q(22,7*N);DEN=10**12
# 3.14159<pi<22/7 are elementary rational pi bounds.
plo=Q(314159,100000);phi=Q(22,7)
def down(x):return Q(x.numerator*DEN//x.denominator,DEN)
def up(x):return -down(-x)
def sin_bounds(x):
 assert 0<=x<=phi
 t=x;s=t
 for j in range(1,13):
  t=-t*x*x/((2*j)*(2*j+1));s+=t
 err=x**27/factorial(27)
 return down(s-err),up(s+err)
def asin_upper(x):
 assert 0<=x<=R
 # positive series c_n x^(2n+1), c_n<=1, tail <=x^(2m+1)/(1-x²)
 m=14
 s=sum(Q(comb(2*n,n),4**n*(2*n+1))*x**(2*n+1) for n in range(m))
 return up(s+x**(2*m+1)/(1-x*x))
grid=[]
for k in range(N+1):
 a=k*h;sl,su=sin_bounds(a);_,halfup=sin_bounds(a/2)
 v=min(R,R*max(Q(1,2),halfup))
 wu=2*asin_upper(v)
 sinwl,_=sin_bounds(wu)
 fu=R2*su/2+(wu-sinwl)/2
 grid.append((a,su,wu,fu))
J=json.loads((P/'area_repaired_dual.json').read_text());out=[]
for row in J:
 mu=[Q(f'{x:.8f}') for x in row['z'][:11]];lam=Q(f'{row["z"][11]:.8f}');assert lam>=0
 core=list(range(9));
 if row['q']:core.remove(1)
 u,v=row['edge'];assert core[(core.index(u)+1)%len(core)]==v
 edges=[(i,(i+1)%9) for i in range(9)]
 if row['q']:edges.append((0,2))
 edges += [(9,u),(9,v),(9,10)]+[(10,i) for i in core]
 c=2*(sum(mu)-lam);ub=c*(plo if c<0 else phi)
 for i,j in edges:
  b=mu[i]+mu[j]
  ub+=max(R2*su-b*a for a,su,wu,fu in grid)+(R2+abs(b))*h
 for i in range(9):
  ub+=max(fu+lam*wu-mu[i]*a for a,su,wu,fu in grid)+(1+lam+abs(mu[i]))*h
 assert ub<plo
 coarse=Q((ub.numerator*10000+ub.denominator-1)//ub.denominator,10000)
 out.append({'q':row['q'],'edge':[u,v],'upper_rational':str(coarse),'upper_exact':str(ub),'below_pi_lower':str(plo),'passed':True})
 print('FRACTION PASS',row['q'],[u,v],str(coarse),flush=True)
(P/'degree3_fraction_control.json').write_text(json.dumps({'N':N,'method':'rational Taylor/asin positive series + independent grid','results':out},indent=2))
