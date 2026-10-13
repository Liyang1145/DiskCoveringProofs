import json, io, math
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
C=[[int(a)/1e17,int(b)/1e17] for a,b in D['centers_scaled_1e17']]
R=0.3799838531198387090485181795734298538115979028573
rings=[1,3,4,5,6,7,8,9,10]
ang=[(math.atan2(C[i][1],C[i][0])%(2*math.pi),i) for i in rings]
ang.sort()
order=[i for a,i in ang]
print('angular order (deg):',[ (i,round(math.degrees(a),6)) for a,i in ang])
print()
mids=[]
for k in range(9):
    a=ang[k][0]; b=ang[(k+1)%9][0]
    if k==8: b+=2*math.pi
    m=(a+b)/2
    p=(math.cos(m),math.sin(m))
    ds=sorted([(math.hypot(p[0]-C[t][0],p[1]-C[t][1]),t) for t in range(11)])
    mids.append((order[k],order[(k+1)%9],m,ds[0],ds[1],ds[2]))
print('=== boundary arc midpoints (on dD) ===')
for i,j,m,d0,d1,d2 in mids:
    tag='TIGHT' if abs(d0[0]-R)<2e-15 else ('covered by %d'%d0[1] if d0[0]<R-1e-15 else 'LOOSE %.3e'%(d0[0]-R))
    print('pair(%2d,%2d) midang=%+9.5fdeg  nearest=%.17f (#%d)  next=%.6f (#%d)  %s'%(i,j,math.degrees(m%(2*math.pi))-360 if m>2*math.pi else math.degrees(m),d0[0],d0[1],d1[0],d1[1],tag))
print()
print('=== Voronoi vertices (exact covering-radius critical pts), sorted ===')
import itertools
from fractions import Fraction as F
S=10**17
CF=[(F(x,S),F(y,S)) for x,y in [[int(a) for a in b] for b in D['centers_scaled_1e17']]]
def circum(i,j,k):
    ax,ay=CF[i]; bx,by=CF[j]; cx,cy=CF[k]
    d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    if d==0: return None
    ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
    uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
    return (ux,uy)
rows=[]
for tri in itertools.combinations(range(11),3):
    v=circum(*tri)
    if v is None or v[0]**2+v[1]**2>1: continue
    ds=sorted([((v[0]-CF[t][0])**2+(v[1]-CF[t][1])**2,t) for t in range(11)])
    rows.append((float(ds[0][0]),float(v[0]),float(v[1]),tri,ds[0][1]))
rows.sort(reverse=True)
seen=set()
for R2,x,y,tri,act in rows[:12]:
    key=(round(x,12),round(y,12))
    if key in seen: continue
    seen.add(key)
    print('R=%.17f v=(%+.15f,%+.15f) gen=%s'%(math.sqrt(R2),x,y,tri))
