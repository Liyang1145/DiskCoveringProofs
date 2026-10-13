"""Independent exact replay: fixed rational ring centers and rational perturbed hubs.
Uses oriented quadratic radical and rational squared circumradius, no member imports.
"""
from fractions import Fraction as F
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
raw=json.loads((ROOT/'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
C=[tuple(F(int(t),10**17) for t in row) for row in raw['centers_scaled_1e17']]
r=F(19,50); A=(F(2653,10**7),F(2729979,10**7)); B=(F(-241,1250000),F(-1494489,10**7))
C[2]=A;C[0]=B
add=lambda a,b:tuple(x+y for x,y in zip(a,b))
sub=lambda a,b:tuple(x-y for x,y in zip(a,b))
mul=lambda t,a:tuple(t*x for x in a)
dot=lambda a,b:sum(x*y for x,y in zip(a,b))
cross=lambda a,b:a[0]*b[1]-a[1]*b[0]
n2=lambda a:dot(a,a)
def sign(x):return int(x>0)-int(x<0)
def rad_sign(u,v,q):
    # sign(u+v sqrt(q)), exact q>=0
    assert q>=0
    if q==0 or v==0:return sign(u)
    if u==0:return sign(v)
    if sign(u)==sign(v):return sign(u)
    return sign(u)*sign(u*u-v*v*q)
assert [rad_sign(*map(F,z)) for z in [(2,-1,1),(1,-2,1),(-2,1,1),(-1,2,1),(1,-1,1)]]==[1,-1,-1,1,0]
pairsA=[(5,7),(7,1),(1,8),(8,6)]
pairsB=[(6,4),(4,9),(9,10),(10,3),(3,5)]
records=[]
for h,pairs in [(A,pairsA),(B,pairsB)]:
    for i,j in pairs:
        a,b=C[i],C[j];d=sub(b,a);m=mul(F(1,2),add(a,b));J=(-d[1],d[0]);q=r*r/n2(d)-F(1,4)
        assert q>0
        s=-sign(dot(m,J));assert s!=0
        u=n2(sub(h,m))+q*n2(d)-r*r
        v=-2*s*dot(sub(h,m),J)
        ps=rad_sign(u,v,q);assert ps<0
        # Independent fan-circle route, all squared and rational
        cr=cross(sub(a,h),sub(b,h));assert cr!=0
        rc2=n2(sub(a,h))*n2(sub(b,h))*n2(d)/(4*cr*cr)
        assert rc2<r*r
        records.append({'pair':[i,j],'pin_sign':ps,'fan_radius2_gap':str(r*r-rc2)})
a,b,c=A,C[5],B
u,v=sub(b,a),sub(c,a);det=cross(u,v)
w,z=(n2(b)-n2(a))/2,(n2(c)-n2(a))/2
p=((w*v[1]-u[1]*z)/det,(u[0]*z-w*v[0])/det)
gaps=[n2(sub(p,c))-r*r for c in C]
assert n2(p)<1 and min(gaps)>F(3,10**6)
assert n2(A)<(1-r)**2 and n2(B)<(1-r)**2
# Canonical norm and positive arc widths preserved from original certified rings.
assert all((1-r)**2<n2(C[i])<1-r*r for i in range(11) if i not in [0,2])
res={'r':str(r),'A':list(map(str,A)),'B':list(map(str,B)),'p':list(map(str,p)), 'unit_disk_gap':str(1-n2(p)), 'squared_uncovered_gaps':list(map(str,gaps)), 'pin_fan_checks':records,'min_uncovered_gap_float_diagnostic':float(min(gaps)), 'all_exact_assertions':True}
out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(res,indent=2),encoding='utf8')
print('Exact 9 pin + 9 fan constraints positive; all11 distances at rational p strictly exceed r; min squared gap ~',float(min(gaps)))
