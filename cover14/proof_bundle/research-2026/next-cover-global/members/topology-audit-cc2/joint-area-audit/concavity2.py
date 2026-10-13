from mpmath import mp, mpf, sin, cos, sqrt, asin, diff, pi
mp.dps=50
U=mpf('0.33173203427623414')
def F(t,r,mu=0):
    b=2*asin(r*sin(t))
    return r*r*sin(t)*cos(t) + (b-sin(b))/2 + mu*b     # NOTE: r^2 sin(alpha)/2 with alpha=2t -> r^2 sin(2t)/2 = r^2 sin t cos t
def F_with_alpha(al,r,mu=0):
    b=2*asin(r*sin(al/2))
    return r*r*sin(al)/2 + (b-sin(b))/2 + mu*b
# check equivalence
print('equiv check:', mp.nstr(F(0.5,U),12), mp.nstr(F_with_alpha(1.0,U),12))
worst=(-1e9,None)
for i in range(1,200):
    t=pi*mpf(i)/200
    d2=diff(lambda s: F(s,U,mpf(0)), t, 2)
    if d2>worst[0]: worst=(d2,t)
print('max F\'\' over t in (0,pi) at r=U (mpmath adaptive):',mp.nstr(worst[0],10),'at t=',mp.nstr(worst[1],6))
# and F'' at the specific t=2.5557
for t in ('2.5557','1.0','2.0','2.5','3.0'):
    d2=diff(lambda s: F(s,U,mpf(0)), mpf(t), 2)
    print('  t=%s  F\'\'=%s'%(t,mp.nstr(d2,10)))
