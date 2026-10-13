import mpmath as mp
mp.mp.dps=25
r=mp.mpf("0.33173203427623414"); s=mp.sqrt(1-r*r)
h=mp.mpf("0.15"); H=mp.cos(h); v=mp.sin(h); th=2*h
D=mp.sqrt(r*r-v*v)
print("h=%s theta=%s H=%s v=%s D=%s"%(h,th,H,v,D))
for (d,b,label) in [(D,mp.mpf(0),"b=0,d=D"),(mp.mpf("0.296166"),mp.mpf(0),"grid")]:
    c=(H-d,b); xp=(H,v); xm=(H,-v)
    uu=(xp[0]-c[0],xp[1]-c[1]); ww=(xm[0]-c[0],xm[1]-c[1])
    dot=uu[0]*ww[0]+uu[1]*ww[1]; cr=abs(uu[0]*ww[1]-uu[1]*ww[0])
    al=mp.atan2(cr,dot)
    print()
    print("case %s: c=(%s,%s)"%(label,mp.nstr(c[0],10),mp.nstr(c[1],10)))
    print("  u = x+ - c = (%s, %s)"%(mp.nstr(uu[0],10),mp.nstr(uu[1],10)))
    print("  w = x- - c = (%s, %s)"%(mp.nstr(ww[0],10),mp.nstr(ww[1],10)))
    print("  u.w = %s   (d^2+b^2-v^2 = %s)"%(mp.nstr(dot,12),mp.nstr(d*d+b*b-v*v,12)))
    print("  |uxw| = %s  (2dv = %s)"%(mp.nstr(cr,12),mp.nstr(2*d*v,12)))
    print("  alpha = atan2 = %s"%(mp.nstr(al,12)))
    print("  |c| = %s  (s=%s)"%(mp.nstr(mp.sqrt(c[0]**2+c[1]**2),12),mp.nstr(s,12)))
    print("  |c-x+|=%s  |c-x-|=%s  (r=%s)"%(mp.nstr(mp.sqrt(uu[0]**2+uu[1]**2),12),mp.nstr(mp.sqrt(ww[0]**2+ww[1]**2),12),mp.nstr(r,12)))
    A=al-mp.acos(s*mp.cos(al))+mp.asin(r); B=2*mp.asin(r*mp.sin(al/2))
    print("  A(alpha)=%s  B(alpha)=%s  theta=%s"%(mp.nstr(A,12),mp.nstr(B,12),mp.nstr(th,12)))
    print("  theta<=A? %s   theta<=B? %s"%(th<=A,th<=B))
