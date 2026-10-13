import json, io, math, itertools
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
C=[[int(a)/1e17,int(b)/1e17] for a,b in D['centers_scaled_1e17']]
print("authoritative interval:", D['certified_interval']['lo'], D['certified_interval']['hi'])
rs=[0.37998385311983869, 0.3799838531198387090485181795734298538115979028, 0.379983853119838709048518179573429853811597902857]
n=11
def d2(p,i):
    return (p[0]-C[i][0])**2+(p[1]-C[i][1])**2
pts=[]
for i,j in itertools.combinations(range(n),2):
    ci,cj=C[i],C[j]; dx=cj[0]-ci[0]; dy=cj[1]-ci[1]; d=math.hypot(dx,dy)
    for r in rs:
        if d>2*r: continue
        a=d/2; h=math.sqrt(max(0.0,r*r-a*a)); mx=(ci[0]+cj[0])/2; my=(ci[1]+cj[1])/2; ux,uy=dx/d,dy/d
        for s in (1,-1):
            px=mx-s*h*uy; py=my+s*h*ux
            if px*px+py*py<=1.0: pts.append((px,py,i,j,r))
print('pts',len(pts), 'unique', len(set((round(p[0],14),round(p[1],14)) for p in pts)))
# for each, compute m = min_i |p-c_i|^2  -> the covering radius must satisfy r^2>=m at every such pt
worst={}
for px,py,i,j,r in pts:
    m=min(d2((px,py),k) for k in range(n))
    key=(round(px,13),round(py,13))
    val=(math.sqrt(m),px,py,i,j)
    if key not in worst or val[0]>worst[key][0]: worst[key]=val
vals=sorted(worst.values(), reverse=True)
print('--- top 14 critical points by needed radius (min_i|p-c_i|) ---')
for v,px,py,i,j in vals[:14]:
    ds=sorted([(math.sqrt(d2((px,py),k)),k) for k in range(n)])
    print('need=%.17f  p=(%.15f,%.15f) gen=(%d,%d) near=%s'%(v,px,py,i,j,[(k,'%.12f'%d) for d,k in ds[:4]]))
