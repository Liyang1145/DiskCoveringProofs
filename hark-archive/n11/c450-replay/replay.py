"""Exact-rational (fractions.Fraction) replay of C450GroupedPacketKernel.Valid and of the
structural side conditions (leaf/packet binding, radial chain, cell_join tree, Qcell tiling,
source_eq) for every emitted C450 SourceK segment. Independent of Lean; transcription of
the WIP definitions (Interval/Core, C450QuadraticBounds, C450GroupedGeometry, C450GroupedAmplitude,
C450GroupedAnalytic, IntervalsHigh(Lag), Interval/Trig.piLo)."""
import json,sys
from fractions import Fraction as F
from math import factorial
D=json.load(open(sys.argv[1]))
def Q(x): return F(x)
piLo=F(314159265358979323846,10**20)
def mul(A,B):
    ps=[A[0]*B[0],A[0]*B[1],A[1]*B[0],A[1]*B[1]]; return (min(ps),max(ps))
def add(A,B): return (A[0]+B[0],A[1]+B[1])
def ofRat(q): return (q,q)
def quadQ(B,C,x): return x**2+2*B*x+C
def minimumQ(lo,hi,B,C):
    v=min(hi,max(lo,-B)); return v**2+2*B*v+C
def clipUnit(I): return (max(F(-1),I[0]),min(F(1),I[1]))
def sinTQ(m,q): return sum(F((-1)**k)*q**(2*k+1)/factorial(2*k+1) for k in range(m))
def cosTQ(m,q): return sum(F((-1)**k)*q**(2*k)/factorial(2*k) for k in range(m))
def sinLo(q): return sinTQ(14,q)-abs(q)**29/factorial(29)
def sinHi(q): return sinTQ(14,q)+abs(q)**29/factorial(29)
def cosHi(q): return cosTQ(14,q)+abs(q)**28/factorial(28)
def p2Q(x): return 2*x**2-1
def p3Q(x): return 4*x**3-3*x
def range2Q(I): lo,hi=I; return (p2Q(min(hi,max(lo,F(0)))),max(p2Q(lo),p2Q(hi)))
def range3Q(I):
    lo,hi=I
    l= F(-1) if (lo<=F(1,2) and F(1,2)<=hi) else min(p3Q(lo),p3Q(hi))
    u= F(1) if (lo<=F(-1,2) and F(-1,2)<=hi) else max(p3Q(lo),p3Q(hi))
    return (l,u)
def squareThird(I): return ((4*I[0]**2-1)/3,(4*I[1]**2-1)/3)
def amp(a1,a2,a3,Z,V):
    return add(add(mul(ofRat(a1),V),mul(ofRat(a2),mul(Z,range2Q(V)))),mul(ofRat(a3),mul(squareThird(Z),range3Q(V))))
def sineProductUpper(p,t): return p*(sinHi(t) if p>=0 else sinLo(t))
def arcUpper(a,p,t): return a*t+sineProductUpper(p,t)
R=F(19,50)
def valid(s,p):
    eLo,eHi,a0,a1,a2,a3,b0,b1,b2,b3=s
    lo,hi,qLo,qHi,ellLo,ellHi,vLo,vHi,zLo,zHi,qt,qb,p0,p1=p
    Lr=(ellLo,ellHi); Qr=(qLo,qHi); Z=(zLo,zHi); V=(vLo,vHi)
    CB=(min(F(1),ellLo/(2*R)),min(F(1),ellHi/(2*R)))
    raw=mul(add(mul(Lr,Qr),(eLo,eHi)),(1/hi if hi else F(0),1/lo if lo else F(0)))
    cl=clipUnit(raw)
    cap=piLo*(a0+b0)/10
    up=arcUpper(a0,p0,qt)+arcUpper(b0,p1,qb)
    checks=dict(
      e_nonneg=0<=eLo, e_upper=eHi<=F(7,50), lower=F(31,50)<=lo, ordered=lo<=hi, upper=hi<=F(69,50),
      q_lower=-1<=qLo, q_upper=qHi<=1, ell_lower=eHi<=ellLo, ell_ordered=ellLo<=ellHi,
      ell_numeric0=quadQ(ellLo*qHi,ellLo**2,eLo)<=lo**2, ell_numeric1=quadQ(ellLo*qHi,ellLo**2,eHi)<=lo**2,
      ell_numeric_upper=hi**2<=minimumQ(eLo,eHi,ellHi*qLo,ellHi**2),
      z_numeric_lower=0<=minimumQ(lo,hi,-zLo,1-R**2),
      z_numeric0=quadQ(-zHi,1-R**2,lo)<=0, z_numeric1=quadQ(-zHi,1-R**2,hi)<=0,
      v_contains=(vLo<=cl[0] and cl[1]<=vHi), v_lower=-1<=vLo, v_upper=vHi<=1, z_nonneg=0<=zLo,
      cb_nonneg=0<=CB[0], qt_nonneg=0<=qt, qb_nonneg=0<=qb, t_cos=cosHi(qt)<=zLo, b_cos=cosHi(qb)<=CB[0],
      amplitude0=amp(a1,a2,a3,Z,V)[1]<=p0, amplitude1=amp(b1,b2,b3,CB,Qr)[1]<=p1,
      scalar0=abs(p0)<=a0, scalar1=abs(p1)<=b0, total_pos=0<a0+b0, numeric=up<cap)
    return [k for k,v in checks.items() if not v], cap-up
rep={}
allS=[[F(x) for x in s] for s in D['c450Segs']]
for k,v in sorted(D['segs'].items(),key=lambda t:int(t[0])):
    k=int(k); s=[F(x) for x in v['seg']]; issues=[]
    if allS[k-1]!=s: issues.append('source_eq')
    a=s; 
    if not abs(a[3])+abs(a[4])+abs(a[5])<=a[2]: issues.append('nn0')
    if not abs(a[7])+abs(a[8])+abs(a[9])<=a[6]: issues.append('nn1')
    qs=[]; npk=0; nfail=0; minslack=None
    for ci,c in enumerate(v['cells']):
        q=tuple(F(x) for x in c['q']); qs.append(q)
        pk=[[F(x) for x in p] for p in c['packets']]; npk+=len(pk)
        if c['nvalid']!=len(pk): issues.append(f'C{ci+1}:nvalid {c["nvalid"]}/{len(pk)}')
        if c['bound'] is None: issues.append(f'C{ci+1}:bound-missing')
        for i,p in enumerate(pk):
            f,sl=valid(s,p)
            if f: nfail+=1; issues.append(f'C{ci+1}:packet{i}:'+','.join(f))
            minslack=sl if minslack is None or sl<minslack else minslack
            lf=c['leaves'].get(str(i))
            if (p[2],p[3])!=q: issues.append(f'C{ci+1}:packet{i}:Q!=Qcell')
            if lf is None or (F(lf[0]),F(lf[1]))!=(p[0],p[1]): issues.append(f'C{ci+1}:leaf{i}:lohi')
        # radial chain
        if pk[0][0]!=F(31,50) or pk[-1][1]!=F(69,50): issues.append(f'C{ci+1}:chain-ends')
        for i in range(len(pk)-1):
            if pk[i][1]!=pk[i+1][0]: issues.append(f'C{ci+1}:gap{i}')
        # tree: every node's stated (lo,hi) equals (lo of left child, hi of right child)
        iv={f'leaf{i}':(pk[i][0],pk[i][1]) for i in range(len(pk))}
        for name,lohi,l,r in c['nodes']:
            if l not in iv or r not in iv: issues.append(f'C{ci+1}:{name}:child-undef'); continue
            if iv[l][1]!=iv[r][0] or (iv[l][0],iv[r][1])!=(F(lohi[0]),F(lohi[1])): issues.append(f'C{ci+1}:{name}:join')
            iv[name]=(F(lohi[0]),F(lohi[1]))
        if c['bound'] and iv.get(c['bound'])!=(F(31,50),F(69,50)): issues.append(f'C{ci+1}:bound-range')
    qs_ok = qs[0][0]==-1 and qs[-1][1]==1 and all(qs[i][1]==qs[i+1][0] for i in range(31)) and all(a<=b for a,b in qs)
    if not qs_ok: issues.append('Qcell tiling')
    rep[k]=dict(packets=npk,failed_packets=nfail,issues=issues[:40],n_issues=len(issues),min_numeric_slack=float(minslack))
    print(k,npk,'fail',nfail,'issues',len(issues),issues[:3],'minslack %.3e'%float(minslack),flush=True)
json.dump(rep,open(sys.argv[2],'w'),indent=1)
