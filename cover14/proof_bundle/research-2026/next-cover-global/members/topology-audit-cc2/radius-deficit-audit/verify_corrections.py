from mpmath import mp, mpf, sin, cos, tan, sqrt, asin, acos, pi, atan
mp.dps=40
U=mpf('0.33173203427623414')
# (2) paired facet area: triangle O_f O_g P and O_f O_g Q, each = (1/2) Rf Rg sin beta
#     so the PAIR = Rf Rg sin beta (not 2).
for (Rf,Rg,l) in ((U,U,mpf('0.5')),(U,mpf('0.6')*U,mpf('0.5')),(mpf('0.8')*U,mpf('0.5')*U,mpf('0.3'))):
    hf=sqrt(Rf*Rf-(l/2)**2); hg=sqrt(Rg*Rg-(l/2)**2)
    Of=(l/2,hf); Og=(l/2,-hg); P=(mpf(0),mpf(0))
    cross=abs((Of[0]-P[0])*(Og[1]-P[1])-(Of[1]-P[1])*(Og[0]-P[0]))
    area_tri=cross/2
    gf=asin((l/2)/Rf); gg=asin((l/2)/Rg); beta=pi-gf-gg
    print('Rf=%s Rg=%s l=%s: angle(O_f P O_g)=%s  beta=%s  area(tri)=%s  (1/2)RfRg sinb=%s  RfRg sinb=%s'%(
        mp.nstr(Rf,6),mp.nstr(Rg,6),mp.nstr(l,3),mp.nstr(atan(hf/(l/2))+atan(hg/(l/2)),8),
        mp.nstr(beta,8), mp.nstr(area_tri,8), mp.nstr(Rf*Rg*sin(beta)/2,8), mp.nstr(Rf*Rg*sin(beta),8)))
print()
# (3) the correct chain: tau = |tan Delta| tan(beta/2); tan(b/2)=(1-cos b)/sin b
#     => tau sin b = |tan Delta|(1-cos b) >= |Delta|(1-cos b)   [uses |tan D|>=|D|]
import random; random.seed(2)
bad=0; worst=mpf('-1e9')
for _ in range(200000):
    b=mpf(random.uniform(1e-5,float(pi)-1e-5))
    tau=mpf(random.uniform(0,1))
    Delta=atan(tau/tan(b/2))     # from tau=|tanD|tan(b/2)
    lhs=tau*sin(b); rhs=(1-cos(b))*abs(Delta)
    if lhs<rhs-mpf('1e-30'): bad+=1
    worst=max(worst,rhs-lhs)
print('chain tau sinb >= (1-cos b)|Delta|: violations',bad,' worst(rhs-lhs)',mp.nstr(worst,6))
# (4) beta -> pi: |Delta| < (pi-beta)/2 -> 0, so RHS -> 0
for b in (pi-mpf('1e-2'),pi-mpf('1e-4'),pi-mpf('1e-6')):
    print('  beta=pi-%s: (pi-beta)/2=%s  (1-cos b)=%s  (1-cosb)|Delta| max=%s'%(
        mp.nstr(pi-b,3), mp.nstr((pi-b)/2,6), mp.nstr(1-cos(b),6), mp.nstr((1-cos(b))*(pi-b)/2,6)))
