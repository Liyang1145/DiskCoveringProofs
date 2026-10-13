import mpmath as mp
mp.mp.dps=40
r=mp.mpf("0.33173203427623414"); s=mp.sqrt(1-r*r); u=mp.asin(r)
A=lambda x: x-mp.acos(s*mp.cos(x))+u
B=lambda x: 2*mp.asin(r*mp.sin(x/2))
def alpha_direct(d,b,h):
    H=mp.cos(h); v=mp.sin(h)
    uu=(d,v-b); ww=(d,-v-b)
    dot=uu[0]*ww[0]+uu[1]*ww[1]; cr=abs(uu[0]*ww[1]-uu[1]*ww[0])
    return mp.atan2(cr,dot)
# theta_max(alpha) by brute force over h, exactly matching alpha
print("alpha   theta_max(brute)  A(alpha)   B(alpha)   min(A,B)  matches")
for av in ["0.2","0.5","0.92034","1.0","1.3","1.683454"]:
    al=mp.mpf(av); best=None
    NH=400
    for i in range(1,NH+1):
        h=u*mp.mpf(i)/NH; v=mp.sin(h); H=mp.cos(h)
        dmax=mp.sqrt(max(mp.mpf(0),r*r-v*v))
        if dmax<=0: continue
        for k in range(1,120):
            d=dmax*mp.mpf(k)/120
            w=mp.sqrt(max(mp.mpf(0),r*r-d*d))
            blo=max(mp.mpf(0),v-w); bhi=w-v
            if bhi<blo: continue
            Q=2*H*d+v*v-r*r
            bN=mp.sqrt(Q-d*d) if Q-d*d>0 else mp.mpf(0)
            bm=min(bhi,bN)
            if bm<blo: continue
            for j in range(0,25):
                b=blo+(bm-blo)*mp.mpf(j)/25
                al2=alpha_direct(d,b,h)
                if abs(al2-al)<mp.mpf("5e-3"):
                    if best is None or h>best[0]: best=(h,d,b)
    if best is None:
        print("%-8s none" % av); continue
    th=2*best[0]
    print("%-8s %-16s %-10s %-10s %-10s %s" % (av, mp.nstr(th,10), mp.nstr(A(al),8), mp.nstr(B(al),8), mp.nstr(min(A(al),B(al)),8), abs(th-min(A(al),B(al)))<mp.mpf("0.02")))
