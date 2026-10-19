import numpy as np, math, json
from proto import *
from scipy.optimize import minimize
A=np.linspace(0,math.pi,181); U=np.linspace(0,1,81)
a,u,v=np.meshgrid(A,U,U,indexing='ij')
res={}
for i in range(9):
    c=coef(i); o=obj(c,a,u,v)
    idx=np.argsort(o.ravel())[-30:]
    best=-9
    for j in idx:
        k=np.unravel_index(j,o.shape); x0=[A[k[0]],U[k[1]],U[k[2]]]
        r=minimize(lambda x:-obj(c,x[0],x[1],x[2]),x0,bounds=[(0,math.pi),(0,1),(0,1)],method='L-BFGS-B',options=dict(ftol=1e-15,gtol=1e-12))
        if -r.fun>best: best=-r.fun; bx=r.x
    res[i]=(best,list(bx)); print(i,best,bx)
print(sum(r[0] for r in res.values()))
json.dump(res,open('maxes_q0m2.json','w'))
