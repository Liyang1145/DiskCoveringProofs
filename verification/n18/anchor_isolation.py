# SPDX-License-Identifier: MIT
"""Independent exact positive-matrix certificate for the n18 candidate graph."""
import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"tools"))
from diskcover_n18_algebraic import EDGES, SHA, require, root_certificate

DIM = 90
ANCHOR_DIM = 22
SCALE = 10**15
E = Q(2,SCALE)
NU = Q(7,625)
COEFF = 400
ANCHOR_SHIFT = Q(69,50_000)
BUFFER = Q(1,10**8)
RHO = Q(1,10**80)
ANCHOR_RADIUS = Q(7,60)


def positive_bareiss(matrix):
    """Sylvester's criterion via fraction-free exact elimination."""
    H = [row[:] for row in matrix]
    n = len(H)
    require(all(len(row)==n for row in H), "matrix must be square")
    require(all(H[i][j]==H[j][i] for i in range(n) for j in range(i)),
            "matrix must be symmetric")
    previous=1
    for k in range(n):
        pivot=H[k][k]
        require(pivot>0, f"nonpositive leading determinant {k+1}")
        for i in range(k+1,n):
            for j in range(i,n):
                top=pivot*H[i][j]-H[i][k]*H[k][j]
                x,r=divmod(top,previous)
                require(r==0,"nonexact fraction-free division")
                H[i][j]=H[j][i]=x
        previous=pivot
    return n


def construct_matrix(x, q, anchor_shift=ANCHOR_SHIFT):
    # Strict rational envelope encloses the whole isolated radius-10^-80 box.
    rational=[Q(v,q) for v in x]
    rounded=[round(v*SCALE) for v in rational]
    require(all(abs(Q(z,SCALE)-a)+RHO<E for z,a in zip(rounded,rational)),
            "insufficient coordinate envelope")
    weights=rounded[91:163]
    multipliers=rounded[163:174]
    require(len(weights)==len(EDGES)==72 and len(multipliers)==11,"size mismatch")
    require(all(0<Q(w,SCALE)-E and Q(w,SCALE)+E<Q(1,10) for w in weights),
            "rod weight outside (0,1/10)")
    require(all(-NU<Q(m,SCALE)-E and Q(m,SCALE)+E<0 for m in multipliers),
            "anchor multiplier outside (-nu,0)")

    coordinates=[(SCALE,0)]+list(zip(rounded[:DIM:2],rounded[1:DIM:2]))
    M=[[0]*DIM for _ in range(DIM)]
    A=[]
    for (u,v),w in zip(EDGES,weights):
        row={}
        for c in (0,1):
            i,j=2*(u-1)+c,2*(v-1)+c
            d=2*(coordinates[u][c]-coordinates[v][c])
            if u:
                row[i]=d
                M[i][i]+=w
            if v:
                row[j]=-d
                M[j][j]+=w
            if u and v:
                M[i][j]-=w
                M[j][i]-=w
        A.append((row,w))
    anchor_wt=NU*SCALE
    require(anchor_wt.denominator==1,"anchor weight not integral on common scale")
    for j,m in enumerate(multipliers):
        i=2*j
        M[i][i]+=m
        M[i+1][i+1]+=m
        a,b=coordinates[j+1]
        A.append(({i:2*a,i+1:2*b},int(anchor_wt)))
    require(sum(z*z for row,_ in A for z in row.values())<100*SCALE*SCALE,
            "Jacobian Frobenius norm cap")
    require(all(Q(w,SCALE)**2<Q(1,100) for _,w in A),
            "rounded diagonal weight norm cap")

    degree=max(Counter(u for edge in EDGES for u in edge).values())
    # Frobenius error exact bound: 4 slots per rod, 2 per circle row.
    require(72*4*16+11*2*4<500**2,"Jacobian perturbation coefficient too small")
    da,dm,dw=500*E,(2*degree+1)*E,E/4
    err=dm+COEFF*(Q(1,100)*(20+da)*da+dw*(10+da)**2)
    require(err<BUFFER,"operator perturbation would consume buffer")

    unit=SCALE**4
    H=[[c*SCALE**3 for c in row] for row in M]
    for row,w in A:
        for i,a in row.items():
            for j,b in row.items():
                H[i][j]+=COEFF*w*w*a*b
    shift=anchor_shift*unit
    pad=BUFFER*unit
    require(shift.denominator==pad.denominator==1,"noninteger matrix buffer/shift")
    for i in range(DIM):
        H[i][i]-=int(pad)+(int(shift) if i<ANCHOR_DIM else 0)
    return H,degree,err


def run(path, negative_controls=False):
    raw=Path(path).read_bytes()
    require(hashlib.sha256(raw).hexdigest()==SHA,"candidate digest mismatch")
    x,q,root_checks=root_certificate(json.loads(raw))
    require(80 in root_checks,"no tight root isolation")
    H,degree,err=construct_matrix(x,q)
    pivots=positive_bareiss(H)
    require(ANCHOR_SHIFT>2*COEFF*NU**2*ANCHOR_RADIUS**2,"insufficient anchor shift")
    report=dict(n=18,status="candidate_active_rod_graph_anchor_neighborhood_only",
                anchor_distance_bound=str(ANCHOR_RADIUS),positive_leading_determinants=pivots,
                exact_positive_contact_weights=len(EDGES),max_degree=degree,
                root_input_sha256=SHA,operator_perturbation_upper=str(err),
                buffered_matrix_sha256=hashlib.sha256(json.dumps(H,separators=(",",":")).encode()).hexdigest())
    if negative_controls:
        bad=[row[:] for row in H]
        bad[0][0]=-abs(bad[0][0])
        try:
            positive_bareiss(bad)
        except ArithmeticError as exc:
            require("leading determinant 1" in str(exc),"unexpected damaged matrix rejection")
        else:
            raise ArithmeticError("damaged matrix incorrectly accepted")
        report["negative_controls_rejected"]=1
    return report


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("candidate")
    p.add_argument("--negative-controls", action="store_true")
    a=p.parse_args()
    print(json.dumps(run(a.candidate,a.negative_controls),indent=2))
