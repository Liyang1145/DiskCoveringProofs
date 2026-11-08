"""Diagnostic only: regular boundary angles are not an arbitrary-cover premise."""
import math,json
import numpy as np
from scipy.optimize import differential_evolution
import explore_degree_capacity as E

def huber(x):
    x=abs(x)
    return x*x if x<=.2 else .4*x-.04

def dynamic(b,boundary,interior):
    budget=150-2*b
    dp=np.full(budget+1,-np.inf);dp[0]=0
    for i in range(26):
        values=boundary if i<b else interior
        nxt=np.full_like(dp,-np.inf)
        for degree in range(2 if i<b else 3,26):
            nxt[degree:]=np.maximum(nxt[degree:],dp[:-degree]+values[degree])
        dp=nxt
    return float(dp[budget])

for b in range(15,20):
    d=math.pi/b;s=math.sin(d);r=E.U
    G=d-s*math.cos(d)+s*math.sqrt(r*r-s*s)
    area_gap=(50-b)*3*math.sqrt(3)/4*r*r+b*r*r/2+b*G-math.pi
    beta=math.pi-2*d
    cb=np.array([0,0]+[.8*(k-1)*huber(beta/(k-1)-math.pi/3) for k in range(2,26)])
    ci=np.array([0,0,0]+[.8*k*huber(2*math.pi/k-math.pi/3) for k in range(3,26)])
    def fn(x):
        weight,slope=x
        boundary=weight*E.coefficients(slope)-(1-weight)*r*r*cb
        interior=weight*E.interior-(1-weight)*r*r*ci
        return dynamic(b,boundary,interior)+weight*slope+(1-weight)*area_gap
    ans=differential_evolution(fn,[(0,1),(-9,-1)],seed=1,tol=1e-6,maxiter=100)
    print(json.dumps({'b':b,'U':r,'weight':ans.x[0],'slope':ans.x[1],
                      'optimistic_regular_joint_upper':ans.fun}),flush=True)
