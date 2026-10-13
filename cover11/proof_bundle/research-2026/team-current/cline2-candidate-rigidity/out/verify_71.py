import json,io,math
from mpmath import mp,mpf,sqrt,atan2,pi,nstr,acos
mp.dps=50
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
S=mpf(10)**17
C=[(mpf(int(a))/S,mpf(int(b))/S) for a,b in D['centers_scaled_1e17']]
lo=mpf(D['certified_interval']['lo'])
ORDER=[5,7,1,8,6,4,9,10,3]
# double precision replication of the (7,1) boundary bisector tight point
import math as M
C8=[[int(a)/1e17,int(b)/1e17] for a,b in D['centers_scaled_1e17']]
i,j=7,1
ax,ay=C8[i][0]-C8[j][0],C8[i][1]-C8[j][1]
Cc=((C8[i][0]**2+C8[i][1]**2)-(C8[j][0]**2+C8[j][1]**2))/2
dd=ax*ax+ay*ay
A0=(Cc*ax/dd, Cc*ay/dd)
rem=1-(A0[0]**2+A0[1]**2); s=M.sqrt(rem)/M.sqrt(dd)
cands=[(A0[0]+s*(-ay),A0[1]+s*ax),(A0[0]-s*(-ay),A0[1]-s*ax)]
for p in cands:
    th=M.degrees(M.atan2(p[1],p[0]))%360
    d7=M.hypot(p[0]-C8[7][0],p[1]-C8[7][1]); d1=M.hypot(p[0]-C8[1][0],p[1]-C8[1][1])
    print('double branch: th=%.6f deg |p|=%.17f  d7=%.17f d1=%.17f'%(th,M.hypot(*p),d7,d1))
lp,mp_=cands[0],cands[1]
th0=M.degrees(M.atan2(lp[1],lp[0]))%360
# mpmath version starting from the double approximations
for name,p in (('A',lp),('B',mp_)):
    p=(mpf(repr(p[0])),mpf(repr(p[1])))
    d7=sqrt((p[0]-C[7][0])**2+(p[1]-C[7][1])**2); d1=sqrt((p[0]-C[1][0])**2+(p[1]-C[1][1])**2)
    print('%s: |p|=%.20f  d7-lo=%s  d1-lo=%s'%(name,float(sqrt(p[0]**2+p[1]**2)),nstr(d7-lo,6),nstr(d1-lo,6)))
# also: the true tight point at 67.694 deg (60 digits) -- solve exactly
# |p|=1 and |p-c7|=|p-c1| ->  p = A0 +- s*perp  with exact rationals
from fractions import Fraction as F
num=[[int(a) for a in b] for b in D['centers_scaled_1e17']]
N=mpf(10)**34
axF=F((num[7][0]-num[1][0]),1); ayF=F((num[7][1]-num[1][1]),1)
CcF=(F(num[7][0]**2+num[7][1]**2)-F(num[1][0]**2+num[1][1]**2))/2
ddF=axF**2+ayF**2
A0F=(CcF*axF/ddF, CcF*ayF/ddF)
lhs=(F(10)**34-(A0F[0]**2+A0F[1]**2))
sF=mpf(lhs.numerator)/mpf(lhs.denominator)
remF=mpf(1)- (mpf(A0F[0].numerator)/mpf(A0F[0].denominator))**2-(mpf(A0F[1].numerator)/mpf(A0F[1].denominator))**2
sc=sqrt(remF)/sqrt(mpf(ddF.numerator)/mpf(ddF.denominator))
P0=(mpf(A0F[0].numerator)/mpf(A0F[0].denominator), mpf(A0F[1].numerator)/mpf(A0F[1].denominator))
two=[(P0[0]+sc*(-mpf(ayF.numerator)/mpf(ayF.denominator)),P0[1]+sc*mpf(axF.numerator)/mpf(axF.denominator)),
     (P0[0]-sc*(-mpf(ayF.numerator)/mpf(ayF.denominator)),P0[1]-sc*mpf(axF.numerator)/mpf(axF.denominator))]
print()
print('exact-rational bisector branch points for (7,1):')
for p in two:
    pn=(p[0]/mpf(10)**17, p[1]/mpf(10)**17)
    d7=sqrt((pn[0]-C[7][0])**2+(pn[1]-C[7][1])**2)
    print('   p=(%.15f,%.15f) |p|=%.30f  d7=%.30f  d7-lo=%s'%(float(pn[0]),float(pn[1]),float(sqrt(pn[0]**2+pn[1]**2)),float(d7),nstr(d7-lo,8)))
