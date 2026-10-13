import mpmath as mp
mp.mp.dps=40
r=mp.mpf("0.33173203427623414"); s=mp.sqrt(1-r*r); u=mp.asin(r)
A=lambda x: x-mp.acos(s*mp.cos(x))+u
B=lambda x: 2*mp.asin(r*mp.sin(x/2))

# exact candidates for fixed alpha: find h such that a legal config has angle alpha,
# and both branches' extremizer configurations
# Branch 1 (both endpoint distances r): d=D(h)=sqrt(r^2-sin^2 h), b=0.
#   Its angle depends on h; for a given alpha solve h.
def ang_sym(h):
    v=mp.sin(h); D=mp.sqrt(r*r-v*v)
    if D<=0: return mp.mpf(0)
    # b=0,d=D: u=(D,v), w=(D,-v)
    return mp.atan2(2*D*v, D*D-v*v)
# Branch 2 (one endpoint r, |c|=s): d=d*, b=b*
def ang_asym(h):
    v=mp.sin(h); H=mp.cos(h)
    d=r*(r*H-s*v); b=s*(r*H-s*v)
    if d<=0 or b<0: return None
    return mp.atan2(2*d*v, d*d+b*b-v*v)
print("h      theta=2h   alpha_symcfg  alpha_asymcfg")
for hv in ["0.02","0.05","0.1","0.15","0.2","0.25","0.3","0.33"]:
    h=mp.mpf(hv)
    print("%-6s %-9s %-13s %s" % (hv, mp.nstr(2*h,8), mp.nstr(ang_sym(h),10), mp.nstr(ang_asym(h),10) if ang_asym(h) is not None else "n/a"))
print()
print("Now: for each alpha, the largest theta with a legal config of angle alpha")
print("  found by solving the two branch curves (which are exactly the two candidate")
print("  extremizers), comparing to A(alpha), B(alpha):")
def invert(f, target, lo=mp.mpf("1e-9"), hi=mp.pi, key=None):
    # solve f(h)=target by bisection where f is monotone
    pass
# branch1: alpha as function of h from ang_sym; invert
def inv_ang(f, al):
    lo,hi=mp.mpf("1e-9"),u
    flo=f(lo)
    for _ in range(300):
        m=(lo+hi)/2; fm=f(m)
        if (flo<al) == (fm<al): lo=m; flo=fm
        else: hi=m
    return (lo+hi)/2
for av in ["0.2","0.5","1.0","1.3","1.683454"]:
    al=mp.mpf(av)
    h1=inv_ang(ang_sym, al); h2=inv_ang(ang_asym, al)
    print("  alpha=%-9s branch1 theta=%s  branch2 theta=%s   A(alpha)=%s B(alpha)=%s"
          % (av, mp.nstr(2*h1,10), mp.nstr(2*h2,10), mp.nstr(A(al),10), mp.nstr(B(al),10)))
