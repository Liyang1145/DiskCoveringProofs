from mpmath import mp, mpf, sin, cos, sqrt, asin, diff
mp.dps=50
def b(t,r):
    return 2*asin(r*sin(t))
def w(t,r): return sqrt(1-(r*sin(t))**2)
for (r0,t0) in ((mpf('0.33173203427623414'), mpf('0.5')), (mpf('0.3'), mpf('1.0')), (mpf('0.9'), mpf('0.8'))):
    d2=diff(lambda t: b(t,r0), t0, 2)
    mine = r0**2*cos(t0)**2/w(t0,r0)**3 - r0*sin(t0)/w(t0,r0)
    lead = -r0*(1-r0**2)*sin(t0)/(2*w(t0,r0)**3)
    print('r=%s t=%s'%(r0,t0))
    print('   numeric second derivative =',mp.nstr(d2,15))
    print('   my formula                =',mp.nstr(mine,15))
    print('   lead formula              =',mp.nstr(lead,15))
