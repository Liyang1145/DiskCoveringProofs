"""Numerical proposals for additive shape penalties on disjoint face groups."""
import math,json
from scipy.optimize import differential_evolution
import numpy as np

d=math.pi/3;A=3*math.sqrt(3)/4;U=.230001;K=.8
def H(x):
    x=abs(x);return x*x if x<=.2 else .4*x-.04

def group_max(group,shift):
    target=[d+shift,d+shift,d-2*shift] if group==1 else [d-shift,d-shift,d+2*shift]
    def objective(z):
        gamma=math.pi*z[0];alpha=(math.pi-gamma)*z[1];beta=math.pi-alpha-gamma;R=z[2]
        sa,sb,sg=map(math.sin,[alpha,beta,gamma]);area=2*R*R*sa*sb*sg
        switch=lambda x:R*x*math.sqrt(max(0,1-R*R*x*x))
        area+=switch(sg) if group==1 else switch(sa)+switch(sb)
        return -(area+K*sum(H(x-y) for x,y in zip([alpha,beta,gamma],target)))
    ans=differential_evolution(objective,[(1e-8,1-1e-8),(1e-8,1-1e-8),(1e-8,1)],seed=1,tol=1e-8,maxiter=400)
    return -ans.fun

def corner_dp(b,shift):
    T=50-b;D=3*T;B=3*b;beta=math.pi-2*math.pi/b
    dp=np.full((D+1,B+1),np.inf);dp[0,0]=0
    for i in range(26):
        boundary=i<b;nxt=np.full_like(dp,np.inf)
        for n in range(1 if boundary else 3,25 if boundary else 26):
            for h in range(2 if boundary else 0,min(2*n if boundary else n,B)+1):
                mean=(beta if boundary else 2*math.pi)/n-d-shift*((6 if boundary else 0)-2*h)/n
                cost=K*n*H(mean)
                nxt[n:,h:]=np.minimum(nxt[n:,h:],dp[:D+1-n,:B+1-h]+cost)
        dp=nxt
    return float(dp[D,B])

for shift in np.linspace(0,.10,11):
    m1,m2=[group_max(k,float(shift)) for k in [1,2]]
    loss=min(A+.5-m1,(A+1-m2)/2)
    out={'shift':float(shift),'one_group_max_proposal':m1,'two_group_max_proposal':m2,'uniform_edge_defect':loss}
    for b in [15,16,17]:
        s=math.sin(math.pi/b);g=math.pi/b-s*math.cos(math.pi/b)+s*math.sqrt(U*U-s*s)
        gap=((50-b)*A*U*U+b*U*U/2+b*g-math.pi)/(U*U)
        shape=corner_dp(b,shift)
        out[str(b)]={'penalty':shape,'net_area':(gap-shape-b*loss)*U*U}
    print(json.dumps(out),flush=True)
