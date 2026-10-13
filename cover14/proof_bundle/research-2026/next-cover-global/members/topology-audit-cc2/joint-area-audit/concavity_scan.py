from mpmath import mp, mpf, sin, cos, sqrt, asin
mp.dps=40
def Fpp(t,r,mu):
    w=sqrt(1-(r*sin(t))**2)
    bpp=(r*r*cos(t)**2 - r*sin(t)*w)/w**3      # correct b''/2
    Fpp = -r*r*sin(t)*cos(t) + (r*r*sin(t)**2+mu)*2*bpp + 2*r*r*r*sin(t)*cos(t)**2/w
    return Fpp
U=mpf('0.33173203427623414')
# scan r for the concavity threshold: max over t in [0,pi] of F'' (mu=0)
def maxFpp(r):
    best=mpf('-1e9'); arg=None
    for i in range(0,2001):
        t=mp.pi*mpf(i)/2000
        v=Fpp(t,r,mpf(0))
        if v>best: best=v; arg=t
    return best,arg
for r in (U, mpf('0.34'), mpf('0.35'), mpf('0.36'), mpf('0.4'), mpf('0.45'), mpf('0.5'), mpf('0.6'), mpf('0.9'), mpf(1)):
    bf,at=maxFpp(r)
    print('r=%-24s max F\'\' (mu=0) = %-14s at t=%s  concave=%s'%(mp.nstr(r,8),mp.nstr(bf,8),mp.nstr(at,5),bf<=0))
# bisect the threshold
lo,hi=mpf('0.33'),mpf('0.40')
for _ in range(40):
    mid=(lo+hi)/2
    if maxFpp(mid)[0]>0: hi=mid
    else: lo=mid
print('concavity threshold r* between',mp.nstr(lo,10),'and',mp.nstr(hi,10))
print('U/sqrt(1+U^2)=',mp.nstr(U/sqrt(1+U**2),10),'  1/sqrt2=',mp.nstr(1/sqrt(2),10))
for mu in (mpf(1),mpf(5),mpf(20)):
    print('mu=%s: max F\'\' at r=U = %s (concave=%s)'%(mu,mp.nstr(maxFpp(U)[0],8),mp.nstr(maxFpp(U)[0]+ (min(0,0)),8),maxFpp(U)[0]<=0))
