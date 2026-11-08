"""Numerical cyclic relaxation. Ideal-center restriction makes this diagnostic only."""
import math,json,sys
from pathlib import Path
from itertools import product
import numpy as np
from scipy.optimize import linprog,minimize_scalar

U=float(sys.argv[1]) if len(sys.argv)>1 else .230001
B=int(sys.argv[2]) if len(sys.argv)>2 else 16
MIN_INNER_H=int(sys.argv[3]) if len(sys.argv)>3 else 0
SHIFT=.04;K=.8;d=math.pi/3;A=3*math.sqrt(3)/4
CAP1=1.7644;CAP2=2.225
EDGE=min(A+.5-CAP1,(A+1-CAP2)/2)
mean=math.pi/B;beta=math.pi-2*mean
def huber(x):
    x=abs(x);return x*x if x<=.2 else .4*x-.04

labels=[]
for n in range(1,25):
    for h in range(2,min(2*n,3*B)+1):
        residual=(beta-n*d-SHIFT*(6-2*h))/n
        price=max(-.32,min(.32,2*K*residual))
        if n!=3:price=.32 if residual>0 else -.32
        else:price=round(price/.025)*.025
        constant=price*math.pi-price*(n*d+SHIFT*(6-2*h))-n*price*price/(4*K)
        labels.append((n,h,price,constant))
prices=sorted(set(row[2] for row in labels));P=len(prices)
price_index={p:i for i,p in enumerate(prices)}
triples=list(product(range(P),repeat=3));NT=len(triples);NY=len(labels)
inner=[(n,h,K*n*huber(2*math.pi/n-d+2*SHIFT*h/n))
       for n in range(3,26) for h in range(min(n,3*B)+1)]
NI=len(inner);NV=NT+NY+NI
# Stationary pair flow, price population, boundary/interior counts, corner and incidence budgets.
NR=P*P+P+4
eq=np.zeros((NR,NV));rhs=np.zeros(NR)
for j,(a,b,c) in enumerate(triples):
    eq[a*P+b,j]+=1;eq[b*P+c,j]-=1
    eq[P*P+b,j]-=1
for j,(n,h,p,c) in enumerate(labels,NT):
    eq[P*P+price_index[p],j]=1
    eq[-4,j]=1;eq[-2,j]=n;eq[-1,j]=h
for j,(n,h,c) in enumerate(inner,NT+NY):
    eq[-3,j]=1;eq[-2,j]=n;eq[-1,j]=h
rhs[-4:]=[B,26-B,3*(50-B),3*B]
inequality=np.zeros((1,NV))
inequality[0,NT+NY:]=[-row[1] for row in inner]

angle=np.linspace(0,math.asin(U),8193);sine=np.sin(angle)
G=angle-sine*np.cos(angle)+sine*np.sqrt(np.maximum(0,U*U-sine*sine))
sm=math.sin(mean);hm=math.sqrt(U*U-sm*sm)
gm=mean-sm*math.cos(mean)+sm*hm
slope=2*sm*sm+math.cos(mean)*(U*U-2*sm*sm)/hm
J=(gm+slope*(angle-mean)-G)/(U*U)
theta=np.arcsin(np.clip(sine/U,0,1))-angle
def optimize(lagrange,keep=False):
    c=np.zeros(NV)
    for j,(a,b,z) in enumerate(triples):
        c[j]=np.min(J+(lagrange-2*prices[b])*angle-lagrange*mean
                    +(prices[a]+prices[z]-2*prices[b])*theta/2)
    c[NT:NT+NY]=[row[3] for row in labels]
    c[NT+NY:]=[row[2] for row in inner]
    ans=linprog(c,A_eq=eq,b_eq=rhs,A_ub=inequality,b_ub=[-MIN_INNER_H],bounds=(0,None),method='highs')
    if not ans.success:raise RuntimeError(ans.message)
    return (ans,c) if keep else float(ans.fun)
ans=minimize_scalar(lambda z:-optimize(z),bounds=(-5,5),method='bounded',options={'xatol':1e-5})
lp,c=optimize(ans.x,True)
base=(50-B)*A+B/2+B*gm/(U*U)-math.pi/(U*U)
out={'U':U,'B':B,'minimum_inner_boundary_incidence':MIN_INNER_H,'prices':prices,'lagrange':ans.x,'cyclic_ideal_penalty':lp.fun,
     'uniform_edge_loss':B*EDGE,'required_total_loss':base,
     'optimistic_net_area':(base-B*EDGE-lp.fun)*U*U,
     'boundary_labels':[(labels[i],float(lp.x[NT+i])) for i in range(NY) if lp.x[NT+i]>1e-7],
     'interior_labels':[(inner[i],float(lp.x[NT+NY+i])) for i in range(NI) if lp.x[NT+NY+i]>1e-7],
     'triples':[(tuple(prices[v] for v in triples[i]),float(lp.x[i])) for i in range(NT) if lp.x[i]>1e-7]}
print(json.dumps(out,indent=2))
(Path(__file__).resolve().parent/('cyclic-ideal-proposal-B'+str(B)+'.json')).write_text(json.dumps(out,indent=2))
