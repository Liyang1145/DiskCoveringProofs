import mpmath as mp
mp.mp.dps=25
r=mp.mpf("0.33173203427623414"); s=mp.sqrt(1-r*r); u=mp.asin(r)
A=lambda x: x-mp.acos(s*mp.cos(x))+u
B=lambda x: 2*mp.asin(r*mp.sin(x/2))
def alpha_of(d,b,H,v):
    uu=(d,v-b); ww=(d,-v-b)
    return mp.atan2(abs(uu[0]*ww[1]-uu[1]*ww[0]), uu[0]*ww[0]+uu[1]*ww[1])
# find the scan's argmax in bin 0 (alpha ~ 0.0654) and verify it directly
Nbin=24; NH=120; best=None
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
            if int(float(al)*Nbin/mp.pi)==0:
                if best is None or th>best[0]: best=(th,d,b,h,al)
th,d,b,h,al=best
print("argmax bin0: theta=%s alpha=%s h=%s d=%s b=%s"%(mp.nstr(th,10),mp.nstr(al,10),mp.nstr(h,10),mp.nstr(d,10),mp.nstr(b,10)))
v=mp.sin(h); H=mp.cos(h); c=(H-d,b)
xp=(H,v); xm=(H,-v)
print("c=(%s,%s) |c|=%s s=%s"%(mp.nstr(c[0],10),mp.nstr(c[1],10),mp.nstr(mp.sqrt(c[0]**2+c[1]**2),10),mp.nstr(s,10)))
print("|c-x+|=%s |c-x-|=%s r=%s"%(mp.nstr(mp.sqrt((c[0]-xp[0])**2+(c[1]-xp[1])**2),10),mp.nstr(mp.sqrt((c[0]-xm[0])**2+(c[1]-xm[1])**2),10),mp.nstr(r,10)))
print("A(alpha)=%s B(alpha)=%s theta=%s"%(mp.nstr(A(al),10),mp.nstr(B(al),10),mp.nstr(th,10)))
print("violates A? %s   violates B? %s"%(th>A(al),th>B(al)))
# maximum distance from c over the arc [-h,h]
mx=mp.mpf(0)
for t in range(0,201):
    ang=-h+2*h*mp.mpf(t)/200
    p=(mp.cos(ang),mp.sin(ang))
    dd=mp.sqrt((c[0]-p[0])**2+(c[1]-p[1])**2)
    mx=max(mx,dd)
print("max arc distance from c = %s  (must be <= r=%s): covered=%s"%(mp.nstr(mx,12),mp.nstr(r,12),mx<=r+mp.mpf("1e-15")))
