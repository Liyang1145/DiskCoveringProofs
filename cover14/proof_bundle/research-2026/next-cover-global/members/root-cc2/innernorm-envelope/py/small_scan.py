import mpmath as mp
mp.mp.dps=20
r=mp.mpf("0.33173203427623414"); s=mp.sqrt(1-r*r); u=mp.asin(r)
A=lambda x: x-mp.acos(s*mp.cos(x))+u
B=lambda x: 2*mp.asin(r*mp.sin(x/2))
def alpha_of(d,b,H,v):
    uu=(d,v-b); ww=(d,-v-b)
    return mp.atan2(abs(uu[0]*ww[1]-uu[1]*ww[0]), uu[0]*ww[0]+uu[1]*ww[1])
# finer scan, moderate size
Nbin=24; bins={}
NH=120
for i in range(1,NH+1):
    h=u*mp.mpf(i)/NH; v=mp.sin(h); H=mp.cos(h); th=2*h
    D=mp.sqrt(max(mp.mpf(0),r*r-v*v)); lo=max(mp.mpf(0),H-s)
    if D<=lo: continue
    for k in range(0,61):
        d=lo+(D-lo)*mp.mpf(k)/60
        if d<=0: continue
        w=mp.sqrt(max(mp.mpf(0),r*r-d*d)); bhi=w-v
        if bhi<0: continue
        Q=2*H*d+v*v-r*r
        bN=mp.sqrt(Q-d*d) if Q-d*d>0 else mp.mpf(0)
        bm=min(bhi,bN)
        if bm<0: continue
        for j in range(0,11):
            b=bm*mp.mpf(j)/10
            al=alpha_of(d,b,H,v)
            ib=min(Nbin-1,int(float(al)*Nbin/mp.pi))
            if ib not in bins or th>bins[ib][0]: bins[ib]=(th,d,b)
print("alpha_bin  theta_max    max(A,B)   th-max(A,B)")
for ib in sorted(bins):
    al=mp.pi*(mp.mpf(ib)+mp.mpf("0.5"))/Nbin; th=bins[ib][0]
    print("%-10s %-12s %-10s %s"%(mp.nstr(al,5),mp.nstr(th,8),mp.nstr(max(A(al),B(al)),8),mp.nstr(th-max(A(al),B(al)),5)))

