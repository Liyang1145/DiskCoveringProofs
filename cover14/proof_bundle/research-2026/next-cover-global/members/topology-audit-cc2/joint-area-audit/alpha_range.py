from mpmath import mp, mpf, sin, cos, sqrt, asin, acos, diff, pi, atan2
import random
mp.dps=40
U=mpf('0.33173203427623414')
# In a normalized cover, a site c with |c|>1-rho that owns a boundary arc: the arc endpoints are at
# distance <= rho from c.  Max view angle alpha at c between two points x,y on S^1 with |x-c|,|y-c|<=rho.
def max_alpha(cnorm, rho):
    # optimize: x,y on S^1 with |x-c|<=rho; maximize angle xcy
    # for |c|=d: points of S^1 within rho of c = arc centred at direction of c of half-angle beta
    d=cnorm
    val=(1+d*d-rho*rho)/(2*d)
    if val<-1: return pi, 0.0
    if val>1: return mpf(0), mpf(0)
    beta=acos(val)   # half-angle of the allowed arc about direction of c
    # angle at c between the two extreme points (angles -beta and +beta)
    p1=(cos(-beta),sin(-beta)); p2=(cos(beta),sin(beta)); cc=(d,0)
    import math
    v1=(p1[0]-d,p1[1]); v2=(p2[0]-d,p2[1])
    n1=sqrt(v1[0]**2+v1[1]**2); n2=sqrt(v2[0]**2+v2[1]**2)
    cosa=(v1[0]*v2[0]+v1[1]*v2[1])/(n1*n2)
    return acos(max(-1,min(1,cosa))), beta
def Fpp(t,r):
    return diff(lambda s: r*r*sin(s)*cos(s)+(2*asin(r*sin(s))-sin(2*asin(r*sin(s))))/2, t, 2)
print('site norm d  -> max possible alpha (rho=U)   [half-angle beta], and F\'\'(alpha/2)')
for d in ('0.4','0.5','0.55','0.60','0.65','0.668','0.70','0.80','0.90'):
    dm=mpf(d)
    if dm+U<1: 
        print('  d=%s : inactive (cannot own arc)'%d); continue
    a,beta=max_alpha(dm,U)
    t=a/2
    print('  d=%s : alpha=%.4f (beta=%.4f)  F\'\'(t=%.4f)=%s'%(d,float(a),float(beta),float(t), mp.nstr(Fpp(t,U),8) if t<pi else 'n/a'))
print()
print('concavity threshold in t (r=U): solve F\'\'=0')
lo,hi=mpf('1.0'),mpf('2.0')
for _ in range(60):
    mid=(lo+hi)/2
    if Fpp(mid,U)>0: hi=mid
    else: lo=mid
print('  t* =',mp.nstr(lo,10),' -> alpha* =',mp.nstr(2*lo,10))
