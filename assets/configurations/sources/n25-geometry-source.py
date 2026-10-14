"""Exact n25 construction in Q(sqrt(2)), with a common scale a=sqrt((2-sqrt2)/3).

No floating point acceptance and no claim of unrestricted global optimality.
All 25 centers, 16 anchors, 32 common-point witnesses and full disk complex checked.
"""
from pathlib import Path
from fractions import Fraction as F
from dataclasses import dataclass
from collections import Counter,defaultdict
from decimal import Decimal,localcontext
import argparse
import hashlib
import json

ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


@dataclass(frozen=True)
class Q2:
    a:F
    b:F=F(0)
    def __post_init__(self):
        object.__setattr__(self,"a",F(self.a))
        object.__setattr__(self,"b",F(self.b))
    def __add__(self,v):
        v=asq(v)
        return Q2(self.a+v.a,self.b+v.b)
    __radd__=__add__
    def __neg__(self):
        return Q2(-self.a,-self.b)
    def __sub__(self,v):
        return self+-asq(v)
    def __rsub__(self,v):
        return asq(v)+-self
    def __mul__(self,v):
        v=asq(v)
        return Q2(self.a*v.a+2*self.b*v.b,self.a*v.b+self.b*v.a)
    __rmul__=__mul__
    def __truediv__(self,v):
        v=asq(v)
        den=v.a*v.a-2*v.b*v.b
        assert den!=0
        return self*Q2(v.a/den,-v.b/den)
    def __rtruediv__(self,v):
        return asq(v)/self
    def sign(self):
        if not self.a:
            return (self.b>0)-(self.b<0)
        if not self.b:
            return (self.a>0)-(self.a<0)
        if self.a>0 and self.b>0:
            return 1
        if self.a<0 and self.b<0:
            return -1
        comparison=self.a*self.a-2*self.b*self.b
        assert comparison!=0 # sqrt2 irrational; nonzero rational coefficients
        sign=(comparison>0)-(comparison<0)
        return sign if self.a>0 else -sign
    def dump(self):
        return [str(self.a),str(self.b)]


def asq(v):
    return v if isinstance(v,Q2) else Q2(v)


S=Q2(0,1)
A2=(2-S)/3
R2=1-2*S/3


def add(p,q):
    return [x+y for x,y in zip(p,q)]


def sub(p,q):
    return [x-y for x,y in zip(p,q)]


def dot(p,q):
    return sum((x*y for x,y in zip(p,q)),Q2(0))


def cross(p,q):
    return p[0]*q[1]-p[1]*q[0]


def rotate(p,k):
    for _ in range(k%8):
        p=[S*(p[0]-p[1])/2,S*(p[0]+p[1])/2]
    return p


def circumcenter(a,b,c):
    u=[2*v for v in sub(b,a)]
    v=[2*w for w in sub(c,a)]
    h,k=dot(b,b)-dot(a,a),dot(c,c)-dot(a,a)
    det=cross(u,v)
    assert det.sign()!=0
    return [(h*v[1]-u[1]*k)/det,(u[0]*k-h*v[0])/det]


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=ROOT/"evidence/n25-algebraic-upper")
    args=parser.parse_args()
    output=args.output
    assert not output.exists()
    output.mkdir(parents=True)
    unit=[rotate([Q2(1),Q2(0)],j) for j in range(8)]
    centers=[]
    anchors=[]
    qp=[(3+S)/2,Q2(F(1,2))]
    qm=[qp[0],-qp[1]]
    for j in range(8):
        centers += [[2*x for x in unit[j]],add(unit[j],unit[(j+1)%8])]
        anchors += [rotate(qp,j),rotate(qm,j+1)]
    centers += [[Q2(0),Q2(0)]]+unit
    faces=[]
    for j in range(8):
        k=(j+1)%8
        faces += [(16,17+j,17+k),(17+j,2*j,2*j+1),
                  (17+j,2*j+1,17+k),(17+k,2*j+1,2*k)]
    faces=[tuple(sorted(f)) for f in faces]
    assert len(centers)==25 and len(anchors)==16 and len(set(faces))==32
    assert A2.sign()>0 and R2.sign()>0
    assert ((9+6*S)*R2-1).sign()==0 # r=1/(sqrt6+sqrt3)
    assert R2==1/(9+6*S)
    witnesses=[]
    for face in faces:
        vertices=[centers[v] for v in face]
        w=circumcenter(*vertices)
        for c in vertices:
            assert (A2*dot(sub(w,c),sub(w,c))-R2).sign()==0
        witnesses.append(w)
    for i,q in enumerate(anchors):
        assert (A2*dot(q,q)-1).sign()==0
        for c in (centers[i],centers[(i+1)%16]):
            assert (A2*dot(sub(q,c),sub(q,c))-R2).sign()==0
        prev=anchors[(i-1)%16]
        assert cross(prev,q).sign()>0 and dot(prev,q).sign()>0
        assert cross(prev,centers[i]).sign()>0 and cross(centers[i],q).sign()>0
        for d in range(25):
            delta=A2*dot(sub(q,centers[d]),sub(q,centers[d]))-R2
            assert delta.sign()>=0
    # Exact quadrant pattern plus positive adjacent cross/dot gives one winding.
    quadrants=[(1,1)]*4+[(-1,1)]*4+[(-1,-1)]*4+[(1,-1)]*4
    assert [(q[0].sign(),q[1].sign()) for q in anchors]==quadrants
    points=anchors+centers
    triangles=[]
    for i in range(16):
        triangles += [((i-1)%16,i,16+i),(i,16+(i+1)%16,16+i)]
    triangles += [tuple(16+j for j in fa) for fa in faces]
    edgecounts=Counter()
    directed=Counter()
    link=defaultdict(list)
    oriented=[]
    for a,b,c in triangles:
        sign=cross(sub(points[b],points[a]),sub(points[c],points[a])).sign()
        assert sign!=0
        if sign<0:
            b,c=c,b
        assert cross(sub(points[b],points[a]),sub(points[c],points[a])).sign()>0
        oriented.append([a,b,c])
        for u,v,w in ((a,b,c),(b,c,a),(c,a,b)):
            edgecounts[tuple(sorted((u,v)))]+=1
            directed[u,v]+=1
            link[u].append((v,w))
    assert len(triangles)==64 and len(edgecounts)==104
    assert 41-104+64==1
    boundary={tuple(sorted((i,(i+1)%16))) for i in range(16)}
    adjacency=defaultdict(set)
    for (a,b),count in edgecounts.items():
        assert count==(1 if (a,b) in boundary else 2)
        if (a,b) not in boundary:
            assert directed[a,b]==directed[b,a]==1
        adjacency[a].add(b)
        adjacency[b].add(a)
    for i in range(16):
        assert directed[i,(i+1)%16]==1 and directed[(i+1)%16,i]==0
    reached,todo={0},[0]
    while todo:
        for v in adjacency[todo.pop()]:
            if v not in reached:
                reached.add(v);todo.append(v)
    assert reached==set(range(41))
    for v,edges in link.items():
        adj=defaultdict(set)
        for a,b in edges:
            adj[a].add(b);adj[b].add(a)
        seen,todo={next(iter(adj))},[next(iter(adj))]
        while todo:
            for node in adj[todo.pop()]:
                if node not in seen:
                    seen.add(node);todo.append(node)
        assert seen==set(adj)
        if v<16:
            assert sorted(a for a,ns in adj.items() if len(ns)==1)==sorted(((v-1)%16,(v+1)%16))
            assert all(len(ns) in (1,2) for ns in adj.values())
        else:
            assert all(len(ns)==2 for ns in adj.values())
    with localcontext() as context:
        context.prec=100
        # Decimal proposes integer endpoints; exact field sign accepts them.
        numerical=Decimal(1)/(Decimal(6).sqrt()+Decimal(3).sqrt())
        scale=10**60
        k=int(numerical*scale)
    assert (R2-F(k,scale)**2).sign()>0
    assert (F(k+1,scale)**2-R2).sign()>0
    def dec(k):
        return str(k//scale)+"."+str(k%scale).zfill(60)
    data={"N":25,"B":16,"coefficient_field":"Q(sqrt(2)); physical points are a times stored coefficients",
          "a_squared":A2.dump(),"r_squared":R2.dump(),
          "centers":[[v.dump() for v in p] for p in centers],
          "anchors":[[v.dump() for v in p] for p in anchors],
          "faces":[list(f) for f in faces],"witnesses":[[v.dump() for v in p] for p in witnesses],
          "upper_triangles":oriented}
    (output/"geometry.json").write_text(json.dumps(data,indent=2),encoding="utf8")
    result={"verified":True,"statement":"The specified 25 equal disks cover the entire closed unit disk with radius 1/(sqrt(6)+sqrt(3))",
            "r_strict_interval":[dec(k),dec(k+1)],
            "radius_isolated_by":"exact quadratic-field squared comparisons; not decimal definition",
            "actual_cover_radius_equals_r":True,"exact_nearest_anchors_checked":16,
            "vertices":41,"edges":104,"triangles":64,"boundary_caps":16,
            "center_faces":32,"exact_active_center_faces":32,
            "geometry_sha256":hashlib.sha256((output/"geometry.json").read_bytes()).hexdigest(),
            "acceptance_source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "global_optimality_proved":False,"uniqueness_of_optimizers_proved":False}
    (output/"VERIFIED.json").write_text(json.dumps(result,indent=2),encoding="utf8")
    print(json.dumps(result,indent=2),flush=True)


if __name__=="__main__":
    main()
