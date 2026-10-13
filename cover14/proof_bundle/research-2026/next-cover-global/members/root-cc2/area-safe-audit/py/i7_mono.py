import mpmath as mp
mp.mp.dps=40
h=lambda L: mp.sin(L)/L
prev=None; root=None
N=4000; hi=mp.pi
for k in range(1,N+1):
    L=hi*mp.mpf(k)/N
    g=L*mp.cos(L)-mp.sin(L)
    if prev is not None and prev[1]>0>g:
        root=(prev[0],L); break
    prev=(L,g)
print("sign change interval:",[mp.nstr(x,8) for x in root])
a,b=root
for _ in range(200):
    m=(a+b)/2
    if (a*mp.cos(a)-mp.sin(a))*(m*mp.cos(m)-mp.sin(m))<=0: b=m
    else: a=m
c=(a+b)/2
print("critical L* =",mp.nstr(c,14),"  rho* = sin(L*/2) =",mp.nstr(mp.sin(c/2),14))
print("h(L*) =",mp.nstr(h(c),14))
print("h(0.67627797) =",mp.nstr(h(mp.mpf("0.67627797")),12))
print("h(2.5) =",mp.nstr(h(mp.mpf("2.5")),12),"  h(3.0) =",mp.nstr(h(mp.mpf("3.0")),12))
print("L_our = 2asin(0.3317320) =",mp.nstr(2*mp.asin(mp.mpf("0.3317320342762341")),10)," <= pi/3 =",mp.nstr(mp.pi/3,10))
