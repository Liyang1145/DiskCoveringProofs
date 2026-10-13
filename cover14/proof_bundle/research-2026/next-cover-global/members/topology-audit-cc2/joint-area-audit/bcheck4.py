from mpmath import mp, mpf, sin, cos, sqrt, asin, diff
mp.dps=40
def f(t,r):
    w=sqrt(1-(r*sin(t))**2)
    return r*cos(t)/w
for (r0,t0) in ((mpf('0.3'),mpf('1.0')),(mpf('0.33173203427623414'),mpf('0.5')),(mpf('0.9'),mpf('0.8'))):
    print('r',r0,'t',t0)
    for h in ('1e-4','1e-6','1e-8','1e-10','1e-12','1e-14'):
        hh=mpf(h)
        d=(f(t0+hh,r0)-2*f(t0,r0)+f(t0-hh,r0))/hh**2
        print('   h=%s  f\'\'= %s'%(h, mp.nstr(d,12)))
    print('   mpmath.diff f\'\'= %s'%mp.nstr(diff(lambda t: f(t,r0), t0, 2),12))
