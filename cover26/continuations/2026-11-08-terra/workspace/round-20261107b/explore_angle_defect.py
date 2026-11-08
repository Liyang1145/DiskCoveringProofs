"""Numerical proposals for a global triangle-angle defect lemma."""
import math
from scipy.optimize import differential_evolution
A=3*math.sqrt(3)/4;d=math.pi/3;h=.2
def huber(x):
    x=abs(x)
    return x*x if x<=h else 2*h*x-h*h
def ratio(z):
    a=z[0]*math.pi;b=a+z[1]*(math.pi-3*a)/2;c=math.pi-a-b
    ds=[a-d,b-d,c-d]
    penalty=sum(map(huber,ds))
    if penalty<1e-14:return math.sqrt(3)/2
    loss=A-2*math.sin(a)*math.sin(b)*math.sin(c)
    return loss/penalty
for seed in range(4):
    ans=differential_evolution(ratio,[(0,1/3-1e-6),(0,1)],seed=seed,tol=1e-10)
    print('minimum ratio proposal',ans.fun,ans.x.tolist(),flush=True)
for b in range(14,21):
    beta=math.pi-2*math.pi/b
    T=50-b;inner=26-b
    # Dynamic program over all interior degrees and boundary corner counts.
    values={0:(0,[])}
    for tag,n,total in [('boundary',b,beta),('interior',inner,2*math.pi)]:
        for _ in range(n):
            nxt={}
            for paid,(cost,indices) in values.items():
                for k in range(1 if tag=='boundary' else 3,27):
                    if paid+k>3*T:continue
                    newcost=cost+.8*k*huber(total/k-d)
                    if paid+k not in nxt or newcost<nxt[paid+k][0]:
                        nxt[paid+k]=(newcost,indices+[(tag,k)])
            values=nxt
    best=values.get(3*T)
    print('b',b,'regular-polygon angle loss proposal',best,flush=True)
