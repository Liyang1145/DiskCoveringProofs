import json, io, math, itertools, sys
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
C=[[int(a)/1e17,int(b)/1e17] for a,b in D['centers_scaled_1e17']]
n=11
r=0.37998385311983869
r2=r*r
def d2(p,i):
    dx=p[0]-C[i][0]; dy=p[1]-C[i][1]; return dx*dx+dy*dy
# all pairwise circle intersections inside D
pts=[]
for i,j in itertools.combinations(range(n),2):
    ci,cj=C[i],C[j]
    dx=cj[0]-ci[0]; dy=cj[1]-ci[1]
    d=math.hypot(dx,dy)
    if d<1e-15: continue
    if d>2*r: continue
    a=d/2; h=math.sqrt(max(0.0,r2-a*a))
    mx=(ci[0]+cj[0])/2; my=(ci[1]+cj[1])/2
    ux,uy=dx/d,dy/d
    for s in (1,-1):
        px=mx - s*h*uy; py=my + s*h*ux
        if px*px+py*py<=1.0:
            pts.append((px,py,i,j))
print('candidate critical pts inside D:',len(pts))
# for each, compute squared distance to each center and find the tight ones (<= r2+tol)
res=[]
for px,py,i,j in pts:
    ds=sorted([(d2((px,py),k),k) for k in range(n)])
    m=ds[0][0]
    # "radius deficit": how deep below r2   => nonnegative means covered
    res.append((m-r2,px,py,i,j,[ (k,math.sqrt(v)) for v,k in ds[:4]]))
res.sort()
print('--- worst 25 (m-r2 negative = UNCOVERED) ---')
for m,px,py,i,j,top in res[:25]:
    print('def=%+.3e  p=(%.17f,%.17f) pair=(%d,%d) nearest=%s'%(m,px,py,i,j,[(k,'%.17f'%v) for k,v in top]))
print()
print('count uncovered:',sum(1 for x in res if x[0]<-1e-15))
print('--- the "exact tie" pts: nearest two equal within 1e-12 rel ---')
for m,px,py,i,j,top in res:
    if abs(top[0][1]-top[1][1])<1e-12:
        print('def=%+.3e p=(%.17f,%.17f) pair=(%d,%d) nearest=%s'%(m,px,py,i,j,[(k,'%.17f'%v) for k,v in top]))
