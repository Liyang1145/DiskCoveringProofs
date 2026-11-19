# SPDX-License-Identifier: MIT
"""Native exact positivity check for the n17 candidate anchor neighborhood."""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
import sys
from collections import Counter

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"tools"))
from check_native_n17_root import ACTIVE, DIGEST, G, isolate, require

GPS = G
Q = 10**15
NU = F(11,1000)
C = F(17,10000)
K = 600
LOCAL_RADIUS = F(27,250)
EPS = F(2,Q)


def positive_bareiss(M):
    """Successive leading principal determinants by symmetric Bareiss."""
    M=[row[:] for row in M]
    past=1
    for k in range(len(M)):
        piv=M[k][k]
        require(piv>0,f"nonpositive leading determinant {k+1}")
        for i in range(k+1,len(M)):
            for j in range(i,len(M)):
                z,rem=divmod(piv*M[i][j]-M[i][k]*M[k][j],past)
                require(rem==0,"nonexact Bareiss division")
                M[i][j]=M[j][i]=z
        past=piv
    return len(M)


def proof(path):
    raw=Path(path).read_bytes()
    require(hashlib.sha256(raw).hexdigest()==DIGEST,"unpinned candidate")
    x=isolate(json.loads(raw))
    rho=F(1,10**80)
    rounded=[round(z*Q) for z in x]
    require(all(abs(F(v,Q)-a)+rho<EPS for v,a in zip(rounded,x)),
            "root box outside rational perturbation envelope")
    edges=([(i,12+(i+k)%12) for k in range(2) for i in range(12)]+
           [(29+j,12+i) for j,face in enumerate(ACTIVE) for i in face])
    require(len(edges)==63,"rod count")
    degree=max(Counter(v for e in edges for v in e).values())
    W=rounded[GPS+1:GPS+1+len(edges)]
    mu=rounded[GPS+1+len(edges):]
    require(len(mu)==11,"unit-circle multiplier count")
    require(all(F(0)<F(v,Q)-EPS and F(v,Q)+EPS<F(1,10) for v in W),
            "positive short-rod weights")
    require(all(-NU<F(v,Q)-EPS and F(v,Q)+EPS<0 for v in mu),
            "multipliers outside proved negative range")
    pt=[(Q,0)]+list(zip(rounded[:GPS:2],rounded[1:GPS:2]))
    M=[[0]*GPS for _ in range(GPS)]
    A=[]
    for (i,j),w in zip(edges,W):
        row={}
        for k in range(2):
            s=2*(pt[i][k]-pt[j][k])
            a,b=2*(i-1)+k,2*(j-1)+k
            if i:
                row[a]=s
                M[a][a]+=w
            if j:
                row[b]=-s
                M[b][b]+=w
            if i and j:
                M[a][b]-=w
                M[b][a]-=w
        A.append((row,w))
    for i,v in enumerate(mu):
        a,b=2*i,2*i+1
        M[a][a]+=v
        M[b][b]+=v
        A.append(({a:2*pt[i+1][0],b:2*pt[i+1][1]},int(NU*Q)))
    require(sum(v*v for row,_ in A for v in row.values())<100*Q*Q,
            "geometric Jacobian Frobenius cap")
    da,dm,dw=400*EPS,(2*degree+1)*EPS,EPS/4
    err=dm+K*(F(1,100)*(20+da)*da+dw*(10+da)**2)
    require(err<F(1,10**8),"operator norm perturbation too large")
    H=[[v*Q**3 for v in row] for row in M]
    for row,w in A:
        for i,a in row.items():
            for j,b in row.items():
                H[i][j]+=K*w*w*a*b
    for i in range(GPS):
        H[i][i]-=Q**4//10**8
        if i<22:
            H[i][i]-=int(C*Q**4)
    count=positive_bareiss(H)
    require(C>2*K*NU**2*LOCAL_RADIUS**2,"local exclusion neighborhood scale")
    return {"n":17,"status":"candidate_neighborhood_only",
            "anchor_distance_bound":str(LOCAL_RADIUS),"positive_leading_determinants":count,
            "positive_rods":len(edges),"matrix_error_upper":"1/100000000"}


if __name__=="__main__":
    print(json.dumps(proof(sys.argv[1]),indent=2))
