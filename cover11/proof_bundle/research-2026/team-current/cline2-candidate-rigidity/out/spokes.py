import json, io, math, itertools
from fractions import Fraction as F
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
S=10**17
Qf=[[int(a) for a in b] for b in D['centers_scaled_1e17']]
C=[[x/S,y/S] for x,y in Qf]
R=0.379983853119838709048518179573429853811597902801556119905389
R2=R*R
rings=[1,3,4,5,6,7,8,9,10]; h0,h2=0,2
ang=sorted([(math.atan2(C[i][1],C[i][0])%(2*math.pi),i) for i in rings])
order=[i for a,i in ang]
print('ring order',order)
# exact spoke point: two circles radius R about c_i,c_j meet at radius 1 from origin
def spoke_exact(i,j):
    ci=Qf[i]; cj=Qf[j]
    # solve |p|^2=S^2 (origin-squared = S^2 in scaled units), |p-ci|^2=R^2 S^2, |p-cj|^2=R^2 S^2
    # subtract eqs -> linear in p
    # |p|^2 - 2p.ci + |ci|^2 - R^2 S^2 = 0 ; |p|^2 - 2p.cj + |cj|^2 - R^2 S^2 = 0
    # subtract: -2p.(ci-cj) + |ci|^2-|cj|^2 = 0
    # and: |p|^2 = S^2
    ax=2*(ci[0]-cj[0]); ay=2*(ci[1]-cj[1]); b=(ci[0]**2+ci[1]**2)-(cj[0]**2+cj[1]**2)
    # ax*px+ay*py = b   -> line
    # parametrize: direction (-ay,ax)
    import math as m
    nrm=m.hypot(ax,ay)
    # foot of perpendicular from origin
    t=b/(nrm*nrm)
    fx=ax*t; fy=ay*t
    # remaining: |p|^2=S^2 with p=f+s*(-ay,ax)/nrm
    L2=(S*S)-(fx*fx+fy*fy)
    if L2<0: return None
    s=m.sqrt(L2)/nrm
    out=[]
    for sg in (1,-1):
        out.append((fx+sg*s*(-ay), fy+sg*s*ax))
    return out
print()
print('=== exact spoke points (boundary points at distance exactly R from both ring centers) ===')
table=[]
for k in range(9):
    i=order[k]; j=order[(k+1)%9]
    ps=spoke_exact(i,j)
    if ps is None: print(i,j,'no intersection'); continue
    # pick the one on the boundary arc between the two centers
    ai=math.atan2(C[i][1],C[i][0])%(2*math.pi); aj=math.atan2(C[j][1],C[j][0])%(2*math.pi)
    if aj<ai: aj+=2*math.pi
    best=None
    for p in ps:
        th=math.atan2(p[1],p[0])%(2*math.pi)
        if th<ai-1e-9: th+=2*math.pi
        if ai-1e-9<=th<=aj+1e-9: best=p
    if best is None:
        # choose closer in angle
        best=min(ps,key=lambda p: abs((math.atan2(p[1],p[0])%(2*math.pi))-0.5*(ai+aj)))
    px,py=best
    ds=sorted([(math.hypot(px-C[t][0],py-C[t][1]),t) for t in range(11)])
    table.append((i,j,(px,py),ds[:3]))
    print('spoke(%2d,%2d) p=(%+.15f,%+.15f) |p|=%.17f  d_i=%.17f([%d]) d_j=%.17f([%d])  3rd=%s'%(
        i,j,px,py,math.hypot(px,py),ds[0][0],ds[0][1],ds[1][0],ds[1][1],(round(ds[2][0],12),ds[2][1])))
print()
print('R =',R)
