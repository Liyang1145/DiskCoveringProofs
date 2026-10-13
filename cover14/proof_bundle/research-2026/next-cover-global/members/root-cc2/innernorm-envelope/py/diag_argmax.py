import mpmath as mp
mp.mp.dps=30
r=mp.mpf("0.33173203427623414"); s=mp.sqrt(1-r*r); u=mp.asin(r)
# reproduce the scan entry for bin alpha ~ 0.049 (theta ~ 0.084): find the argmax
def alpha_of(d,b,H,v):
    dot=d*d+b*b-v*v; cr=2*d*v
    if dot>0: return mp.atan(cr/dot)
    return mp.pi+mp.atan(cr/dot) if dot<0 else mp.pi/2
best=None
NH=700
for i in range(1,NH+1):
    h=u*mp.mpf(i)/NH; v=mp.sin(h); H=mp.cos(h)
    D=mp.sqrt(max(mp.mpf(0),r*r-v*v)); lo=max(mp.mpf(0),H-s)
    if D<=lo: continue
    for k in range(0,141):
        d=lo+(D-lo)*mp.mpf(k)/140
        if d<=0: continue
        w=mp.sqrt(max(mp.mpf(0),r*r-d*d)); bhi=w-v
        if bhi<0: continue
        Q=2*H*d+v*v-r*r
        bN=mp.sqrt(Q-d*d) if Q-d*d>0 else mp.mpf(0)
        bm=min(bhi,bN)
        if bm<0: continue
        for j in range(0,21):
            b=bm*mp.mpf(j)/20
            al=alpha_of(d,b,H,v)
            if abs(al-mp.mpf("0.0490874"))<mp.pi/64:
                if best is None or 2*h>best[0]: best=(2*h,d,b,h,al,v,H)
if best:
    th,d,b,h,al,v,H=best
    print("argmax: theta=%s alpha=%s" % (mp.nstr(th,10), mp.nstr(al,10)))
    print("  h=%s v=%s H=%s d=%s b=%s" % (h,v,H,d,b))
    c=(H-d,b); xp=(H,v); xm=(H,-v)
    print("  |c|=%s  s=%s   (legal: %s)" % (mp.nstr(mp.sqrt(c[0]**2+c[1]**2),10), mp.nstr(s,10), mp.sqrt(c[0]**2+c[1]**2)<=s))
    print("  |c-x+|=%s  r=%s (legal: %s)" % (mp.nstr(mp.sqrt((c[0]-xp[0])**2+(c[1]-xp[1])**2),10), mp.nstr(r,10), mp.sqrt((c[0]-xp[0])**2+(c[1]-xp[1])**2)<=r))
    print("  |c-x-|=%s  r=%s (legal: %s)" % (mp.nstr(mp.sqrt((c[0]-xm[0])**2+(c[1]-xm[1])**2),10), mp.nstr(r,10), mp.sqrt((c[0]-xm[0])**2+(c[1]-xm[1])**2)<=r))
    print("  check arc: midpoint of arc should be within r of c?  midpoint=(1,0): dist=%s" % mp.nstr(mp.sqrt((c[0]-1)**2+c[1]**2),10))
    print("  max over the arc of |arc point - c| (sample):")
    mx=mp.mpf(0)
    for t in range(0,401):
        ang=-h+2*h*mp.mpf(t)/400
        p=(mp.cos(ang),mp.sin(ang))
        dd=mp.sqrt((c[0]-p[0])**2+(c[1]-p[1])**2)
        mx=max(mx,dd)
    print("     max=%s  r=%s  covered=%s" % (mp.nstr(mx,10),mp.nstr(r,10),mx<=r+mp.mpf("1e-12")))
