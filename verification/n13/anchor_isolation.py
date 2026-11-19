# SPDX-License-Identifier: MIT
"""Independent rational isolation of the n13 candidate in anchor norm <=1/8."""
import hashlib
import importlib.util
import json
from fractions import Fraction as F
from pathlib import Path
import sys
from collections import Counter

HERE=Path(__file__).resolve().parent
_spec=importlib.util.spec_from_file_location("n16_bareiss",HERE.parent/"n16"/"anchor_isolation.py")
_psd=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_psd)
positive_bareiss=_psd.positive_bareiss
sys.path.insert(0,str(HERE.parents[1]/"tools"))
from check_native_n13_root import ACTIVE, DIGEST, isolate, require

GPS=62
Q=10**15
NU=F(49,2500)
C=F(19,10000)
EPS=F(2,Q)


def proof(path=HERE/"candidate_midpoint.json"):
    raw=Path(path).read_bytes()
    require(hashlib.sha256(raw).hexdigest()==DIGEST,"unpinned n13 candidate")
    data=json.loads(raw)
    x=isolate(data)
    rho=F(int(data["rho_num"]),int(data["rho_den"]))
    xq=[round(z*Q) for z in x]
    require(all(abs(F(v,Q)-z)+rho<EPS for v,z in zip(xq,x)),
            "root box outside rounding envelope")
    edges=([(i,10+(i+k)%10) for i in range(10) for k in range(2)]+
           [(23+j,10+i) for j,face in enumerate(ACTIVE) for i in face])
    require(len(edges)==47,"contact rod count")
    degree=max(Counter(v for e in edges for v in e).values())
    w,mu=xq[63:110],xq[110:119]
    require(all(F(0)<F(v,Q)-EPS and F(v,Q)+EPS<F(1,10) for v in w),
            "strictly positive weights")
    require(all(-NU<F(v,Q)-EPS and F(v,Q)+EPS<0 for v in mu),
            "anchor multiplier range")
    pt=[(Q,0)]+list(zip(xq[:GPS:2],xq[1:GPS:2]))
    M=[[0]*GPS for _ in range(GPS)]
    A=[]
    for (i,j),weight in zip(edges,w):
        row={}
        for k in range(2):
            t=2*(pt[i][k]-pt[j][k])
            a,b=2*(i-1)+k,2*(j-1)+k
            if i:
                row[a]=t
                M[a][a]+=weight
            if j:
                row[b]=-t
                M[b][b]+=weight
            if i and j:
                M[a][b]-=weight
                M[b][a]-=weight
        A.append((row,weight))
    for i,mult in enumerate(mu):
        a,b=2*i,2*i+1
        M[a][a]+=mult
        M[b][b]+=mult
        A.append(({a:2*pt[i+1][0],b:2*pt[i+1][1]},int(NU*Q)))
    require(sum(v*v for row,_ in A for v in row.values())<81*Q**2,
            "geometric Jacobian Frobenius cap")
    da, dm, dw=236*EPS,(2*degree+1)*EPS,EPS/4
    require(47*4*4**2+9*2*2**2<236**2,"Frobenius error estimate")
    err=dm+148*(F(1,100)*(18+da)*da+dw*(9+da)**2)
    require(err<F(1,10**9),"matrix perturbation too large")
    H=[[v*Q**3 for v in row] for row in M]
    for row,scale in A:
        for i,a in row.items():
            for j,b in row.items():
                H[i][j]+=148*scale**2*a*b
    for i in range(GPS):
        H[i][i]-=Q**4//10**9
        if i<18:
            H[i][i]-=int(C*Q**4)
    count=positive_bareiss(H)
    require(C>296*NU**2*F(1,8)**2,"local radius too large")
    return {"n":13,"status":"candidate_neighborhood_only",
            "anchor_distance_bound":"1/8","positive_leading_determinants":count,
            "positive_rods":len(w),"matrix_error_upper":"1/1000000000"}


if __name__=="__main__":
    print(json.dumps(proof(*sys.argv[1:2]),indent=2))
