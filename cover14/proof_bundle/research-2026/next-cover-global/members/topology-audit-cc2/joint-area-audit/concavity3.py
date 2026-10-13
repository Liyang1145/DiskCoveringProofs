from mpmath import mp, mpf, sin, cos, sqrt, asin, diff, pi
mp.dps=50
U=mpf('0.33173203427623414')
def F(t,r,mu=0):
    b=2*asin(r*sin(t))
    return r*r*sin(t)*cos(t) + (b-sin(b))/2 + mu*b
def Fpp_lead_chain(t,r,mu=0):
    # lead's chain: -r^2 sin t cos t  +  r^3 sin t cos^2 t / w  +  (z^2+mu) b''
    # NOTE: written in t (alpha=2t).  lead's own text uses alpha; here I test the structure
    w=sqrt(1-(r*sin(t))**2); z=r*sin(t)
    bpp=(r*r*cos(t)**2 - r*sin(t)*w)/w**3      # (1/2) b''
    term1=-r*r*sin(t)*cos(t)
    term2=r**3*sin(t)*cos(t)**2/w
    term3=(z*z+mu)*bpp*1  # careful: b'' full = 2*bpp
    return term1+term2+term3
def Fpp_true(t,r,mu=0):
    return diff(lambda s: F(s,r,mu), t, 2)
print('FORMAT: (t, r) true Fpp vs lead-chain candidate')
for r in (U, mpf('0.5'), mpf('0.9'), mpf('0.99')):
    worst=(-1e9,None)
    for i in range(1,400):
        t=pi*mpf(i)/400
        v=Fpp_true(t,r)
        if v>worst[0]: worst=(v,t)
    print('r=%-10s  max true Fpp = %-12s at t=%s   concave=%s'%(mp.nstr(r,6),mp.nstr(worst[0],8),mp.nstr(worst[1],5),worst[0]<=0))
# where does concavity fail for r=U?
lo,hi=mpf('0'),pi
print('Fpp at sample t for r=U:', [(mp.nstr(t,5), mp.nstr(Fpp_true(t,U),7)) for t in (0.5,1.0,1.5,1.9,2.0,2.2,2.5,2.8,3.0)])
