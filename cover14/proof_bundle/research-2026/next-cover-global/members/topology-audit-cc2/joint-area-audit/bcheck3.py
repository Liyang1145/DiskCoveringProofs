from mpmath import mp, mpf, sin, cos, sqrt, asin, pi
mp.dps=60
def b(t,r): return 2*asin(r*sin(t))
def bp_formula(t,r): return 2*r*cos(t)/sqrt(1-(r*sin(t))**2)
for (r0,t0) in ((mpf('0.33173203427623414'), mpf('0.5')), (mpf('0.3'), mpf('1.0'))):
    h=mpf('1e-20')
    fd_bp=(b(t0+h,r0)-b(t0-h,r0))/(2*h)
    print('r',mp.nstr(r0,6),'t',mp.nstr(t0,3),' FD_bp',mp.nstr(fd_bp,12),' formula',mp.nstr(bp_formula(t0,r0),12))
