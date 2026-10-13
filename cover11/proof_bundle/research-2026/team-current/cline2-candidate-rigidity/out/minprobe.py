import numpy as np, math, itertools, json, io, time
from scipy.optimize import minimize
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
C=np.array([[int(a)/1e17 for a in b] for b in D['centers_scaled_1e17']])
R0=float(D['certified_interval']['lo'])
RINGS=[1,3,4,5,6,7,8,9,10]
def critvals(x):
    C=[(x[2*i],x[2*i+1]) for i in range(11)]
    vals=[]
    for tri in itertools.combinations(range(11),3):
        A,B,Cc=C[tri[0]],C[tri[1]],C[tri[2]]
        d1=B[0]-A[0];d2=B[1]-A[1];e1=Cc[0]-A[0];e2=Cc[1]-A[1]
        den=d1*e2-d2*e1
        if abs(den)<1e-16: continue
        bx=((B[0]**2+B[1]**2)-(A[0]**2+A[1]**2))/2; by=((Cc[0]**2+Cc[1]**2)-(A[0]**2+A[1]**2))/2
        ux=(bx*e2-by*d2)/den; uy=(d1*by-e1*bx)/den
        if ux*ux+uy*uy>1: continue
        d=min(math.hypot(ux-c[0],uy-c[1]) for c in C)
        vals.append(d)
    for k in range(9):
        i=k%9
        pass
    return vals
def gamma(x):
    C=[(x[2*i],x[2*i+1]) for i in range(11)]
    best=0.0
    for tri in itertools.combinations(range(11),3):
        A,B,Cc=C[tri[0]],C[tri[1]],C[tri[2]]
        d1=B[0]-A[0];d2=B[1]-A[1];e1=Cc[0]-A[0];e2=Cc[1]-A[1]
        den=d1*e2-d2*e1
        if abs(den)<1e-16: continue
        bx=((B[0]**2+B[1]**2)-(A[0]**2+A[1]**2))/2; by=((Cc[0]**2+Cc[1]**2)-(A[0]**2+A[1]**2))/2
        ux=(bx*e2-by*d2)/den; uy=(d1*by-e1*bx)/den
        if ux*ux+uy*uy>1: continue
        d=min(math.hypot(ux-c[0],uy-c[1]) for c in C)
        if d>best: best=d
    # boundary scan: dense sample + local refine (calibration)
    ang=sorted([(math.atan2(C[i][1],C[i][0])%(2*math.pi),i) for i in RINGS])
    order=[i for a,i in ang]
    for k in range(9):
        i=order[k]; j=order[(k+1)%9]
        A,B=C[i],C[j]
        dx=B[0]-A[0];dy=B[1]-A[1];L2=dx*dx+dy*dy
        t=((B[0]**2+B[1]**2)-(A[0]**2+A[1]**2))/(2*L2)
        fx=A[0]+t*dx; fy=A[1]+t*dy
        rem=1-(fx*fx+fy*fy)
        if rem<=0: continue
        for sg in (1,-1):
            px=fx+sg*math.sqrt(rem)*(-dy)/math.sqrt(L2); py=fy+sg*math.sqrt(rem)*dx/math.sqrt(L2)
            d=min(math.hypot(px-c[0],py-c[1]) for c in C)
            if d>best: best=d
    return best
x0=np.array([v for c in C for v in c])
print('double-precision gamma at the saved object:', '%.17f'%gamma(x0))
print('certified lo / hi:', D['certified_interval']['lo'][:30], D['certified_interval']['hi'][:30])
# Constrained minimisation: minimize gamma over the 22 coordinates with NO other constraints
print()
print('unconstrained local minimisation of the covering radius (SLSQP/Nelder-Mead, multi-start):')
best=(gamma(x0),x0.copy())
rng=np.random.default_rng(7)
t0=time.time()
for trial in range(8):
    x=x0.copy() if trial==0 else x0+rng.normal(0,0.02 if trial<4 else 0.05,22)
    o=minimize(gamma,x,method='Nelder-Mead',options={'maxiter':20000,'xatol':1e-14,'fatol':1e-16})
    g=gamma(o.x)
    print('  trial %d: gamma=%.17f  (start %.17f)  nfev=%d'%(trial,g,gamma(x),o.nfev))
    if g<best[0]: best=(g,o.x.copy())
print('best gamma found: %.17f'%best[0])
print('difference from R0  : %+.3e'%(best[0]-R0))
np.save('out/bestmin.npy',best[1])
