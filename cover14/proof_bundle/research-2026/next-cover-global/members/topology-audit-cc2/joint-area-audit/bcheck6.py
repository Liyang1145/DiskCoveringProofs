from mpmath import mp, mpf, sin, cos, sqrt, asin, diff, atan, sqrt as sq
mp.dps=40
def b(t,r): return 2*asin(r*sin(t))
def my_bpp(t,r):
    w=sq(1-(r*sin(t))**2)
    return 2*(r**2*cos(t)**2/w**3 - r*sin(t)/w*(1 if False else 1))  # placeholder replaced below
def my_bpp2(t,r):
    # b' = 2 r cos t / w  ->  b'' = 2 d/dt[ r cos t / w ]
    w=sq(1-(r*sin(t))**2)
    f1 = r*cos(t)/w
    f1p = -r*sin(t)/w + r**3*sin(t)*cos(t)**2/w**3      # derivative of r cos t / w by quotient rule
    return 2*f1p
for (r0,t0) in ((mpf('0.33173203427623414'),mpf('0.5')),(mpf('0.3'),mpf('1.0')),(mpf('0.9'),mpf('0.8'))):
    d2=diff(lambda t: b(t,r0), t0, 2)
    print('r=%s t=%s  mpmath b\'\'=%s   my_bpp2=%s'%(mp.nstr(r0,8),mp.nstr(t0,4),mp.nstr(d2,12),mp.nstr(my_bpp2(t0,r0),12)))
