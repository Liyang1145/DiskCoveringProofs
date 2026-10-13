from mpmath import mp, mpf, sin, cos, sqrt, asin, acos, diff, pi
mp.dps=40
U=mpf('0.33173203427623414')
def max_alpha(d,rho):
    val=(1+d*d-rho*rho)/(2*d)
    val=max(mpf(-1),min(mpf(1),val))
    beta=acos(val)
    cc=(d,mpf(0)); p1=(cos(-beta),sin(-beta)); p2=(cos(beta),sin(beta))
    v1=(p1[0]-d,p1[1]); v2=(p2[0]-d,p2[1])
    n1=sqrt(v1[0]**2+v1[1]**2); n2=sqrt(v2[0]**2+v2[1]**2)
    cosa=(v1[0]*v2[0]+v1[1]*v2[1])/(n1*n2)
    return acos(max(mpf(-1),min(mpf(1),cosa)))
def Fpp(t,r):
    return diff(lambda s: r*r*sin(s)*cos(s)+(2*asin(r*sin(s))-sin(2*asin(r*sin(s))))/2, t, 2)
best=(mpf(0),None)
d=1-U
while d<=1:
    a=max_alpha(d,U)
    if a>best[0]: best=(a,d)
    d+=mpf('0.001')
print('max alpha over active site norms d in [1-U,1]: alpha_max =',mp.nstr(best[0],10),' at d =',mp.nstr(best[1],6))
print('  alpha* (concavity threshold at r=U) = 3.465591532')
print('  F\'\' at t=alpha_max/2:', mp.nstr(Fpp(best[0]/2,U),10))
# also F'' over the whole feasible t-range
worst=(mpf('-1e9'),None)
t=mpf(0)
while t<=best[0]/2:
    v=Fpp(t,U)
    if v>worst[0]: worst=(v,t)
    t+=mpf('0.001')
print('max F\'\' on [0, alpha_max/2] =',mp.nstr(worst[0],10),'at t=',mp.nstr(worst[1],6))
# and max alpha for a few other rho
for rho in ('0.30','0.25','0.20','0.4'):
    rr=mpf(rho); b=(mpf(0),None); d=1-rr
    while d<=1:
        a=max_alpha(d,rr)
        if a>b[0]: b=(a,d)
        d+=mpf('0.001')
    thr_lo,thr_hi=mpf('1.0'),mpf('2.0')
    for _ in range(50):
        mid=(thr_lo+thr_hi)/2
        if Fpp(mid,rr)>0: thr_hi=mid
        else: thr_lo=mid
    print('rho=%s: alpha_max=%s (d=%s), 2*t*=%s  concave on feasible range: %s'%(rho,mp.nstr(b[0],8),mp.nstr(b[1],5),mp.nstr(2*thr_lo,8), b[0]<=2*thr_lo))
