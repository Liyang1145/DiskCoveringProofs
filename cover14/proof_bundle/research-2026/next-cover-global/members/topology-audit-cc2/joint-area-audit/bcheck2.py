from mpmath import mp, mpf, sin, cos, sqrt, asin
mp.dps=60
def bp(t,r):
    w=sqrt(1-(r*sin(t))**2)
    return r*cos(t)/w
def w(t,r): return sqrt(1-(r*sin(t))**2)
for (r0,t0) in ((mpf('0.33173203427623414'), mpf('0.5')), (mpf('0.3'), mpf('1.0')), (mpf('0.9'), mpf('0.8'))):
    h=mpf('1e-15')
    d2=(bp(t0+h,r0)-bp(t0-h,r0))/(2*h)
    h2=mpf('1e-22')
    d2b=(bp(t0+h2,r0)-bp(t0-h2,r0))/(2*h2)
    mine = r0**2*cos(t0)**2/w(t0,r0)**3 - r0*sin(t0)/w(t0,r0)
    lead = -r0*(1-r0**2)*sin(t0)/(2*w(t0,r0)**3)
    alt = (r0**2*cos(t0)**2 - r0*sin(t0)*w(t0,r0))/w(t0,r0)**3
    print('r=%s t=%s'%(mp.nstr(r0,8),mp.nstr(t0,4)))
    print('   FD_h1e-15 =',mp.nstr(d2,12))
    print('   FD_h1e-22 =',mp.nstr(d2b,12))
    print('   mine      =',mp.nstr(mine,12))
    print('   alt       =',mp.nstr(alt,12))
    print('   lead      =',mp.nstr(lead,12))
