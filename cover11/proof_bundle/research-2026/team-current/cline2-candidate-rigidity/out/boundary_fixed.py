import json, io, math
from mpmath import mp, mpf, sqrt, atan2, pi, nstr, cos, sin
mp.dps=40
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
S=mpf(10)**17
C=[(mpf(int(a))/S,mpf(int(b))/S) for a,b in D['centers_scaled_1e17']]
RINGS=[1,3,4,5,6,7,8,9,10]
def bisect_pts(i,j):
    dx=C[j][0]-C[i][0]; dy=C[j][1]-C[i][1]; dd=dx*dx+dy*dy
    Cc=((C[j][0]**2+C[j][1]**2)-(C[i][0]**2+C[i][1]**2))/2
    t=Cc/dd
    mx=C[i][0]+t*dx; my=C[i][1]+t*dy
    rem=1-(mx*mx+my*my)
    if rem<=0: return None
    s=sqrt(rem); L=sqrt(dd)
    return [(mx+s*(-dy)/L,my+s*dx/L),(mx-s*(-dy)/L,my-s*dx/L)]
rows=[]
for i in range(11):
    for j in range(i+1,11):
        ps=bisect_pts(i,j)
        if ps is None: continue
        for p in ps:
            ds=sorted([(sqrt((p[0]-c[0])**2+(p[1]-c[1])**2),k) for k,c in enumerate(C)])
            rows.append((ds[0][0],(i,j),p,ds[:3]))
rows.sort(reverse=True)
print('CORRECT boundary bisector points (sign fixed), sorted:')
tight=[]
for v,pair,p,ds in rows:
    if v<0.3799: continue
    two=sorted([pair[0],pair[1]])==sorted([ds[0][1],ds[1][1]])
    print('  %.30f pair=%s p=(%+.15f,%+.15f) two-nearest=%s d=%s'%(float(v),pair,float(p[0]),float(p[1]),two,['%.15f'%float(x) for x,k in ds]))
    if v>mpf('0.3799838531198387'): tight.append((pair,p,v,two))
print()
print('number with v > 0.3799838531198387:',len(tight), [t[0] for t in tight])
print('all two-nearest & tight:', all(t[3] for t in tight))
print()
print('max over the boundary = %.30f'%float(max(x[0] for x in rows)))
print('certified lo          = %s'%D['certified_interval']['lo'][:34])
