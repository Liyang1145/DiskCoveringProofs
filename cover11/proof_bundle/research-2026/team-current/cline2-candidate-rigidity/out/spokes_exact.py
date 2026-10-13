import json, io, math
from fractions import Fraction as F
from decimal import Decimal, getcontext
getcontext().prec=60
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
S=F(10)**17
Qf=[[F(int(a)) for a in b] for b in D['centers_scaled_1e17']]
Rlo=Decimal(D['certified_interval']['lo']); Rhi=Decimal(D['certified_interval']['hi'])
def dec(q): return Decimal(q.numerator)/Decimal(q.denominator)
rings=[1,3,4,5,6,7,8,9,10]; h0,h2=0,2
ang=sorted([(math.atan2(float(Qf[i][1]),float(Qf[i][0]))%(2*math.pi),i) for i in rings])
order=[i for a,i in ang]
def spoke_exact(i,j):
    ci=Qf[i]; cj=Qf[j]
    ax=2*(ci[0]-cj[0]); ay=2*(ci[1]-cj[1]); b=(ci[0]**2+ci[1]**2)-(cj[0]**2+cj[1]**2)
    nrm2=ax*ax+ay*ay
    t=b/nrm2
    fx=ax*t; fy=ay*t
    L2=S*S-(fx*fx+fy*fy)
    if L2<=0: return None
    s=dec(L2).sqrt()/dec(nrm2).sqrt()
    nrm=dec(nrm2).sqrt()
    return [ (fx+sg*s*(-ay)/nrm*dec(nrm), fy+sg*s*ax/nrm*dec(nrm)) for sg in (1,-1)] if False else [
        (dec(fx)+sg*s*(-dec(ay))/nrm, dec(fy)+sg*s*dec(ax)/nrm) for sg in (1,-1)]
print('=== exact spoke points & their exact distances (Decimal 60 digits) ===')
res=[]
for k in range(9):
    i=order[k]; j=order[(k+1)%9]
    ps=spoke_exact(i,j)
    ai=float(ang[k][0]); aj=float(ang[(k+1)%9][0])
    if aj<ai: aj+=2*math.pi
    def angdeg(p): 
        th=math.degrees(math.atan2(float(p[1]),float(p[0])))%360
        return th
    cand=[]
    for p in ps:
        th=math.atan2(float(p[1]),float(p[0]))%(2*math.pi)
        if th<ai-2e-4: th+=2*math.pi
        cand.append((abs(th-(ai+aj)/2) if ai-2e-4<=th<=aj+2e-4 else 9e9, p, th))
    cand.sort(key=lambda z:z[0])
    _,p,th=cand[0]
    ds=[]
    for t in range(11):
        d2=(p[0]-dec(Qf[t][0]))**2+(p[1]-dec(Qf[t][1]))**2
        ds.append((d2.sqrt(),t))
    ds.sort()
    res.append((i,j,p,ds))
    print('spoke(%2d,%2d) angle=%.6f deg  |p|=%.50f'%(i,j,math.degrees(th),abs(complex(float(p[0]),float(p[1])))))
    for d,t in ds[:3]:
        print('       d[%2d]  = %.50f   %s'%(t,d, 'R' if abs(d-dec(Rlo))<Decimal('1e-45') else ''))
print()
print('Rlo =',Rlo)
print('Rhi =',Rhi)
print()
print('=== boundary intersection points on dD: distance exact = R? ===')
for i,j,p,ds in res:
    print('(%2d,%2d) d0-d_R = %.3e   nearest disk=%d'%(i,j,float(ds[0][0]-dec(Rlo)),ds[0][1]))
