"""Independent rational certificate: no mpmath, scipy, numerical pi or transcendental calls.
Uses elementary power series with rigorous tails and rational Lipschitz grid error.
"""
from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
import json
P=Path(__file__).parent;R=Q(19,50);R2=R*R;N=8192;h=Q(22,7*N);DEN=10**12
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
def asin_upper(x, m=14):
 assert 0<=x<1
 # positive series c_n x^(2n+1), c_n<=1, tail <=x^(2m+1)/(1-x²)
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
J=[j for j in json.loads((P/'area_triple_dual.json').read_text()) if j['span']==2];out=[]
assert sorted(j['start'] for j in J)==[0,1,2,3]
Bup=asin_upper(2*R,70)
core=[0,2,3,4,5,6,7,8]
for row in J:
 cc=core[row['start']:]+core[:row['start']]
 assert row['hub9_rings']==sorted(cc[:3])
 assert row['hub10_rings']==sorted([*cc[2:],cc[0]])
 mu=[Q(f'{x:.8f}') for x in row['z'][:11]];lam=Q(f'{row["z"][11]:.8f}');assert lam>=0
 eta=Q(f'{row["z"][12]:.8f}');assert eta>=0
 edges=[(i,(i+1)%9) for i in range(9)]+[(0,2),(9,10)]+[(9,i) for i in row['hub9_rings']]+[(10,i) for i in row['hub10_rings']]
 c=2*(sum(mu)-lam-eta);ub=c*(plo if c<0 else phi)+2*eta*Bup
 for i,j in edges:
  b=mu[i]+mu[j]
  ub+=max(R2*su-b*a for a,su,wu,fu in grid)+(R2+abs(b))*h
 for i in range(9):
  ub+=max(fu+(lam+(eta if i>=3 else 0))*wu-mu[i]*a for a,su,wu,fu in grid)+(1+lam+(eta if i>=3 else 0)+abs(mu[i]))*h
 assert ub<plo
 coarse=Q((ub.numerator*10000+ub.denominator-1)//ub.denominator,10000)
 out.append({'q':1,'start':row['start'],'span':2,'upper_rational':str(coarse),'upper_exact':str(ub),'below_pi_lower':str(plo),'passed':True})
 print('FRACTION PASS',1,row['start'],str(coarse),flush=True)
(P/'degree4_triple_fraction_control.json').write_text(json.dumps({'N':N,'method':'rational Taylor/asin positive series + independent grid','results':out},indent=2))
