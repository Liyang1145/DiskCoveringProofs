"""Exact n25 D8 stress orbit audit and homothetic-family optimum, NOT global optimum."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import hashlib
import importlib.util
import json
import sys

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("n25_exact_field",ROOT/"n25_algebraic_upper.py")
Q=importlib.util.module_from_spec(spec);sys.modules[spec.name]=Q;spec.loader.exec_module(Q)
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def solve_affine(rows,nvar):
    matrix=[[Q.asq(x) for x in row] for row in rows]
    pivotcols=[];row=0
    for col in range(nvar):
        pick=next((i for i in range(row,len(matrix)) if matrix[i][col].sign()),None)
        if pick is None:
            continue
        matrix[row],matrix[pick]=matrix[pick],matrix[row]
        p=matrix[row][col]
        matrix[row]=[v/p for v in matrix[row]]
        for i in range(len(matrix)):
            if i!=row and matrix[i][col].sign():
                multiple=matrix[i][col]
                matrix[i]=[a-multiple*b for a,b in zip(matrix[i],matrix[row])]
        pivotcols.append(col);row+=1
    for r in matrix[row:]:
        assert all(not v.sign() for v in r[:-1]) and not r[-1].sign()
    free=[j for j in range(nvar) if j not in pivotcols]
    def evaluate(parameters):
        x=[Q.Q2(0) for _ in range(nvar)]
        for j,v in zip(free,parameters):
            x[j]=Q.asq(v)
        for i,col in enumerate(pivotcols):
            x[col]=matrix[i][-1]-sum((matrix[i][j]*x[j] for j in free),Q.Q2(0))
        return x
    return free,evaluate,len(pivotcols)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=ROOT/"evidence/n25-core-analysis")
    args=parser.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    path=ROOT/"evidence/n25-algebraic-upper-round2/geometry.json"
    d=json.loads(path.read_text())
    points=[[Q.Q2(*v) for v in p] for p in d["anchors"]+d["centers"]+d["witnesses"]]
    centers=points[16:41]
    faces=d["faces"]
    ed=[(i,16+i) for i in range(16)]+[(i,16+(i+1)%16) for i in range(16)]
    ed += [(41+k,16+v) for k,face in enumerate(faces) for v in face]
    assert len(points)==73 and len(ed)==128
    lookup={tuple(p):i for i,p in enumerate(points)}
    assert len(lookup)==len(points),"Coincident witnesses need explicit combinatorial map"
    rot=[lookup[tuple(Q.rotate(p,1))] for p in points]
    reflect=[lookup[(p[0],-p[1])] for p in points]
    assert sorted(rot)==sorted(reflect)==list(range(73))
    edgeindex={frozenset(e):k for k,e in enumerate(ed)}
    parent=list(range(len(ed)))
    def find(k):
        while parent[k]!=k:
            parent[k]=parent[parent[k]];k=parent[k]
        return k
    for permutation in (rot,reflect):
        for k,(u,v) in enumerate(ed):
            other=edgeindex[frozenset((permutation[u],permutation[v]))]
            a,b=find(k),find(other)
            if a!=b:
                parent[b]=a
    ids={k:i for i,k in enumerate(sorted({find(j) for j in range(len(ed))}))}
    orbit=[ids[find(k)] for k in range(len(ed))]
    count=len(ids)
    assert count==9
    rows=[]
    for node in range(73):
        for axis in (0,1):
            row=[Q.Q2(0) for _ in range(count+2)]
            for k,(u,v) in enumerate(ed):
                if node==u:
                    row[orbit[k]]+=points[u][axis]-points[v][axis]
                elif node==v:
                    row[orbit[k]]+=points[v][axis]-points[u][axis]
            if node<16:
                row[count]=points[node][axis]
            rows.append(row)
    normalization=[Q.Q2(orbit.count(j)) for j in range(count)]+[Q.Q2(0),Q.Q2(1)]
    rows.append(normalization)
    free,evaluator,rank=solve_affine(rows,count+1)
    print("D8-invariant stress linear system rank",rank,"free columns",free,flush=True)
    assert len(free)<=1
    chosen=None
    for k in range(1,100):
        parameter=F(k,10000)
        value=evaluator([parameter] if free else [])
        if all(w.sign()>0 and (Q.Q2(F(1,10))-w).sign()>0 for w in value[:count]) and value[count].sign()<0:
            chosen=(parameter if free else None),value
            break
    assert chosen is not None
    parameter,value=chosen
    for row in rows:
        residual=sum((a*b for a,b in zip(row[:-1],value)),Q.Q2(0))-row[-1]
        assert residual.sign()==0
    stress={"verified":True,"N":25,"B":16,"positive_rods":128,
            "edge_orbit_count":count,"orbit_multiplicities":[orbit.count(j) for j in range(count)],
            "D8_invariant_stress_free_dimension":len(free),"orbit_stationarity_rank":rank,
            "chosen_free_parameter":str(parameter),"edge_orbit":orbit,
            "exact_weights_Qsqrt2":[v.dump() for v in value[:count]],"exact_common_circle_multiplier":value[count].dump(),
            "all_node_forces_zero":True,"weights_sum_exactly_one":True,
            "geometry_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
            "global_optimality_proved":False,"source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (args.output/"stress-verified.json").write_text(json.dumps(stress,indent=2),encoding="utf8")
    # Scale parameter lambda>=0 multiplies every center of the explicit construction.
    # For shrink lambda<=1, fixed source q0 has minimum distance >=r* to all centers.
    q=points[0]
    minima=[]
    for j,c in enumerate(centers):
        a=Q.A2*Q.dot(c,c)
        b=Q.A2*Q.dot(q,c)
        if not a.sign() or b.sign()<=0:
            minimum=Q.Q2(1);branch="endpoint-zero"
        elif (b-a).sign()>=0:
            minimum=1+a-2*b;branch="endpoint-one"
        else:
            minimum=1-b*b/a;branch="interior-vertex"
        assert (minimum-Q.R2).sign()>=0
        minima.append({"center":j,"branch":branch,"distance_squared_minimum":minimum.dump()})
    # For enlargement, scaled first central circumcenter has distance lambda*r*
    # to its three sites and >= that to every other site, inside D if lambda*r*<=1.
    witness=points[41] # first face (origin,I0,I1)
    for c in centers:
        assert (Q.A2*Q.dot(Q.sub(witness,c),Q.sub(witness,c))-Q.R2).sign()>=0
    assert Q.A2*Q.dot(witness,witness)==Q.R2
    assert (Q.A2/Q.R2-Q.Q2(F(9,4))).sign()>0 # min nonzero center norm / r*>3/2
    assert (Q.Q2(F(1,4))-Q.R2).sign()>0 # r*<1/2
    # If lambda*r*>1, every nonzero center norm >3/2.
    # Any target point at norm1/2 is >1 away from those centers, and distance1/2 from origin.
    family={"verified":True,"statement":"Within all nonnegative common homotheties of the specified 25 centers, minimum covering radius is exactly 1/(sqrt6+sqrt3)",
            "shrinking_interval":"0<=lambda<=1","shrink_anchor":0,"shrink_squared_minima":minima,
            "enlargement_witness":41,"very_large_scale_test_point_radius":"1/2",
            "symmetry_assumption_scope":"specified homothetic D8 family only; not arbitrary 25 centers",
            "global_optimality_proved":False,"geometry_sha256":stress["geometry_sha256"],
            "source_sha256":stress["source_sha256"]}
    (args.output/"homothetic-family-optimum-verified.json").write_text(json.dumps(family,indent=2),encoding="utf8")
    print("N25 EXACT positive D8 stress PASS: 9 rod orbits, invariant-system rank",rank,
          "free dimension",len(free),flush=True)
    print("N25 EXACT optimum within homothetic construction family PASS; unrestricted optimum still OPEN",flush=True)


if __name__=="__main__":
    main()
