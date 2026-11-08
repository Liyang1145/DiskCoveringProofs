"""Numerical proposals for unrestricted degree/arc-area capacity bounds."""
import math,sys,json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize_scalar

U=float(sys.argv[1]) if len(sys.argv)>1 else .230001
GRID=16384
s=np.linspace(0,math.asin(U)/math.pi,GRID+1)
beta=np.arcsin(np.clip(np.sin(math.pi*s)/U,0,1))
P={}
for degree in range(2,26):
    regular=U*U*(degree+1)*math.sin(2*math.pi/(degree+1))/2
    special=U*U/2*(np.sin(2*beta)+degree*np.sin((2*math.pi-2*beta)/degree))
    use=(2*np.sin(math.pi*s)>U)&(beta>=math.pi/(degree+1))
    P[degree]=np.where(use,special,regular)-np.sin(2*math.pi*s)/2
interior=np.array([0,0,0]+[U*U*k*math.sin(2*math.pi/k)/2 for k in range(3,26)])

def coefficients(slope):
    return np.array([0,0]+[float(np.max(P[d]-slope*s)) for d in range(2,26)])

def dynamic(b,coeff,trace=False):
    budget=150-2*b
    dp=np.full(budget+1,-np.inf);dp[0]=0
    parents=[]
    for i in range(26):
        values=coeff if i<b else interior
        nxt=np.full_like(dp,-np.inf);par=np.full(budget+1,-1,dtype=int)
        for degree in range(2 if i<b else 3,26):
            row=dp[:-degree]+values[degree]
            better=row>nxt[degree:]
            nxt[degree:][better]=row[better]
            par[degree:][better]=degree
        dp=nxt
        if trace:parents.append(par)
    profile=[]
    if trace:
        k=budget
        for par in reversed(parents):
            degree=int(par[k]);profile.append(degree);k-=degree
        profile.reverse()
    return float(dp[budget]),profile

if __name__=='__main__':
    results=[]
    for b in map(int,sys.argv[2:] or list(map(str,range(14,21)))):
        fn=lambda slope:dynamic(b,coefficients(slope))[0]+slope
        ans=minimize_scalar(fn,bounds=(-10,-1),method='bounded',options={'xatol':1e-9})
        total,profile=dynamic(b,coefficients(ans.x),True)
        row={'U':U,'b':b,'slope':ans.x,'total_upper_proposal':total+ans.x,
             'boundary_degrees':profile[:b],'interior_degrees':profile[b:]}
        print(json.dumps(row),flush=True);results.append(row)
    (Path(__file__).resolve().parent/'degree-capacity-proposals.json').write_text(json.dumps(results,indent=2))
