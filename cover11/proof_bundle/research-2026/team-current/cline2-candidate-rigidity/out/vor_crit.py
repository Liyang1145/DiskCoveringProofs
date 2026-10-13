import json, io, math, itertools
p=r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json'
D=json.load(io.open(p,encoding='utf-8-sig'))
Q=[[int(a) for a in b] for b in D['centers_scaled_1e17']]
S=10**17
from fractions import Fraction as F
C=[(F(x,S),F(y,S)) for x,y in Q]
n=11
def F2(i,j):
    dx=C[j][0]-C[i][0]; dy=C[j][1]-C[i][1]; return dx*dx+dy*dy
# Voronoi vertex of triple (i,j,k): circumcenter of the 3 points, exact
def circum(i,j,k):
    ax,ay=C[i]; bx,by=C[j]; cx,cy=C[k]
    d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    if d==0: return None
    ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
    uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
    return (ux,uy)
print("=== exact Voronoi vertices of all C(11,3)=165 triples that are inside D, with exact active set ===")
rows=[]
for tri in itertools.combinations(range(n),3):
    v=circum(*tri)
    if v is None: continue
    if v[0]*v[0]+v[1]*v[1] > 1: continue
    ds=[(F2(*sorted((i,t))),t) for t in range(n) for i in [0] ] # placeholder
    ds=[ ( (v[0]-C[t][0])**2+(v[1]-C[t][1])**2, t) for t in range(n)]
    ds.sort()
    R2=ds[0][0]
    act=[t for d,t in ds if d==R2]
    rows.append((R2,v,tuple(tri),tuple(act),ds[:4]))
rows.sort(key=lambda z:-z[0])
print('total triples-inside:',len(rows))
for R2,v,tri,act,nt in rows[:18]:
    print('R2=%.20f R=%.17f  v=(%.15f,%.15f) gen=%s active=%s'%(float(R2),math.sqrt(float(R2)),float(v[0]),float(v[1]),tri,act))
print()
print("=== radius R and r^2 for reference ===")
print('R_cert=0.3799838531198387090485   R^2=%.20f'%(0.3799838531198387090485**2))
