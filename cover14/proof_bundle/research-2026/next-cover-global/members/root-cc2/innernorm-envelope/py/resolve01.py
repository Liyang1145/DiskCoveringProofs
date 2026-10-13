import mpmath as mp
mp.mp.dps=50
r=mp.mpf("0.33173203427623414"); s=mp.sqrt(1-r*r); u=mp.asin(r)
a=lambda x: x-mp.acos(s*mp.cos(x))+u
b=lambda x: 2*mp.asin(r*mp.sin(x/2))

def alpha_direct(d,b,h):
    H=mp.cos(h); v=mp.sin(h)
    uvec=(d, v-b); wvec=(d,-v-b)
    nu=mp.sqrt(uvec[0]**2+uvec[1]**2); nw=mp.sqrt(wvec[0]**2+wvec[1]**2)
    cs=(uvec[0]*wvec[0]+uvec[1]*wvec[1])/(nu*nw)
    return mp.acos(max(mp.mpf(-1),min(mp.mpf(1),cs))), nu, nw, H, v

def amin_grid(th, N=2000, M=800):
    h=th/2; H=mp.cos(h); v=mp.sin(h)
    dmax=mp.sqrt(r*r-v*v); best=None
    for i in range(1,N+1):
        d=dmax*mp.mpf(i)/N
        w=mp.sqrt(max(mp.mpf(0),r*r-d*d))
        blo=max(mp.mpf(0),v-w); bhi=w-v
        if bhi<blo: continue
        Q=2*H*d+v*v-r*r
        bN=mp.sqrt(Q-d*d) if Q-d*d>0 else mp.mpf(0)
        bm=min(bhi,bN)
        if bm<blo: continue
        for j in range(0,M+1):
            bb=blo+(bm-blo)*mp.mpf(j)/M
            al,nu,nw,H2,v2=alpha_direct(d,bb,h)
            if best is None or al<best[0]: best=(al,d,bb,nu,nw)
    return best

for tv in ["0.2","0.3","0.5"]:
    th=mp.mpf(tv); best=amin_grid(th)
    al,d,bb,nu,nw=best
    print("theta=%s : min alpha=%-14s at (d,b)=(%.6f,%.6f) endpoint dists=(%s,%s) r=%s"
          % (tv, mp.nstr(al,12), float(d), float(bb), mp.nstr(nu,10), mp.nstr(nw,10), mp.nstr(r,10)))
    print("     a(alpha)=%s  b(alpha)=%s   alpha_a(theta)=%s alpha_b(theta)=%s"
          % (mp.nstr(a(al),12), mp.nstr(b(al),12),
             mp.nstr(mp.mpf("nan") if a(al)>th else al,6), mp.nstr(mp.mpf("nan") if b(al)>th else al,6)))
    # which of a,b equals theta at this alpha?
    print("     check theta vs a(alpha),b(alpha): theta-a=%s theta-b=%s"
          % (mp.nstr(th-a(al),8), mp.nstr(th-b(al),8)))
