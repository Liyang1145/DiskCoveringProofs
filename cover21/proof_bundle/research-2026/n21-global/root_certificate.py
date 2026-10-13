"""N21 core root discovery and exact contraction/upper verification.

One unweighted interior center is omitted from the root coordinates; a fixed
exact rational copy is used for upper coverage. Global optimality is NOT proved.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter,defaultdict
from math import isqrt
import argparse
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parent
EV = ROOT/"evidence"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def load_system():
    return json.loads((EV/"core-system.json").read_text())


def evaluate(z,data,zero):
    g,m,b = data["G"],len(data["edges"]),data["B"]
    p,c,d = g+1,m+b-1,len(z)
    points = [[zero+1,zero]]+[z[2*j:2*j+2] for j in range(g//2)]
    f,J = [],[[zero for _ in range(d)] for _ in range(d)]
    stationarity = [zero for _ in range(p)]
    stationarity[g] = zero+1
    hessians = []
    for k,(u,v) in enumerate(data["edges"]):
        delta = [points[u][j]-points[v][j] for j in (0,1)]
        gradient = {g:zero-1}
        hessian = {}
        for axis in (0,1):
            for node,sign in ((u,1),(v,-1)):
                if node:
                    j = 2*(node-1)+axis
                    gradient[j] = gradient.get(j,zero)+2*sign*delta[axis]
                    for other,osign in ((u,1),(v,-1)):
                        if other:
                            h = 2*(other-1)+axis
                            hessian[j,h] = hessian.get((j,h),0)+2*sign*osign
        f.append(sum(v*v for v in delta)-z[g])
        for j,value in gradient.items():
            J[k][j] = value
            J[c+j][p+k] = value
            stationarity[j] += z[p+k]*value
        for (j,h),coefficient in hessian.items():
            J[c+j][h] += z[p+k]*coefficient
        hessians.append(hessian)
    for i in range(1,b):
        k = m+i-1
        row = {2*(i-1)+axis:2*points[i][axis] for axis in (0,1)}
        f.append(sum(v*v for v in points[i])-1)
        hessian = {}
        for j,value in row.items():
            J[k][j] = value
            J[c+j][p+k] = value
            stationarity[j] += z[p+k]*value
            J[c+j][j] += 2*z[p+k]
            hessian[j,j] = 2
        hessians.append(hessian)
    assert len(f) == c and c+p == d
    return f+stationarity,J,hessians


def prepare():
    numeric = json.loads((EV/"kkt-numeric.json").read_text())
    proposal = json.loads((EV/"candidate-numeric.json").read_text())
    oldg, b = numeric["geometry_dimension"],numeric["B"]
    degree = Counter(v for edge in numeric["edges"] for v in edge)
    excluded = [j for j in range(oldg//2+1) if not degree[j]]
    assert excluded == [31] and b <= excluded[0] < b+21
    keep = [j for j in range(oldg//2+1) if j not in excluded]
    mapping = {j:i for i,j in enumerate(keep)}
    edges = [[mapping[u],mapping[v]] for u,v in numeric["edges"]]
    g = 2*(len(keep)-1)
    seed = []
    for j in keep[1:]:
        seed.extend(numeric["numeric_seed"][2*(j-1):2*j])
    seed.extend(numeric["numeric_seed"][oldg:])
    center_nodes = [mapping.get(b+i) for i in range(21)]
    fixed = {str(excluded[0]-b):[format(float(v),".17f")
             for v in proposal["points"][excluded[0]-b]]}
    data = {"N":21,"B":b,"G":g,"P":g+1,"D":len(seed),"edges":edges,
            "active_faces":numeric["active_faces"],"all_faces":numeric["all_faces"],
            "center_core_nodes":center_nodes,"fixed_slack_centers":fixed,
            "old_node_to_core":{str(k):v for k,v in mapping.items()},
            "numeric_seed":seed,"numeric_seed_sha256":sha(EV/"kkt-numeric.json"),
            "scope":"active core root only, one unweighted center fixed rationally for upper coverage"}
    assert g == 92 and len(seed) == 173
    (EV/"core-system.json").write_text(json.dumps(data,indent=2),encoding="utf8")
    return data


def generate():
    import mpmath as mp
    mp.mp.dps = 110
    data = prepare()
    z = [mp.mpf(str(v)) for v in data["numeric_seed"]]
    start = time.time()
    for iteration in range(8):
        f,J,_ = evaluate(z,data,mp.mpf(0))
        error = max(abs(v) for v in f)
        print("Newton proposal",iteration,"residual",mp.nstr(error,10),flush=True)
        if error < mp.mpf("1e-100"):
            break
        dz = mp.lu_solve(mp.matrix(J),mp.matrix(f))
        z = [v-d for v,d in zip(z,dz)]
    f,J,_ = evaluate(z,data,mp.mpf(0))
    assert max(abs(v) for v in f) < mp.mpf("1e-95")
    inverse = mp.inverse(mp.matrix(J))
    qx,qy = 10**90,10**80
    certificate = {"dimension":data["D"],"Qx":str(qx),"Qy":str(qy),
                   "xnum":[str(int(mp.nint(v*qx))) for v in z],
                   "Ynum":[[str(int(mp.nint(inverse[i,j]*qy))) for j in range(data["D"])]
                           for i in range(data["D"])],
                   "system_sha256":sha(EV/"core-system.json"),"outer_rho":"1/"+str(10**60),
                   "inner_rho":"1/"+str(10**80),"radius_numeric":mp.nstr(mp.sqrt(z[data["G"]]),100),
                   "scope":"untrusted proposed rational root certificate, accepted only by verify"}
    (EV/"core-root.json").write_text(json.dumps(certificate,separators=(",",":")),encoding="utf8")
    print("Root proposal generated",certificate["radius_numeric"],"seconds",time.time()-start,flush=True)


def verify():
    data = load_system()
    cert = json.loads((EV/"core-root.json").read_text())
    assert cert["system_sha256"] == sha(EV/"core-system.json")
    d,g = data["D"],data["G"]
    z = [F(int(v),int(cert["Qx"])) for v in cert["xnum"]]
    y = [[F(int(v),int(cert["Qy"])) for v in row] for row in cert["Ynum"]]
    assert len(z) == len(y) == d and all(len(row) == d for row in y)
    start = time.time()
    f,J,H = evaluate(z,data,F(0))
    residual = [sum((a*b for a,b in zip(row,f)),F(0)) for row in y]
    columns = [[(k,J[k][j]) for k in range(d) if J[k][j]] for j in range(d)]
    e = [sum(abs(F(int(i==j))-sum((y[i][k]*v for k,v in columns[j]),F(0)))
             for j in range(d)) for i in range(d)]
    drift = [F(0)]*d
    c = len(H)
    for k,h in enumerate(H):
        drift[k] = sum(abs(v) for v in h.values())
        for (j,l),v in h.items():
            drift[c+j] += 2*abs(v)
    budgets = [sum((abs(a)*v for a,v in zip(row,drift)),F(0)) for row in y]
    checks = []
    for radius in (F(1,10**60),F(1,10**80)):
        inclusion = max(abs(r)/radius+ee+radius*bb for r,ee,bb in zip(residual,e,budgets))
        contraction = max(ee+radius*bb for ee,bb in zip(e,budgets))
        assert inclusion < 1 and contraction < 1
        checks.append({"rho":str(radius),"inclusion":str(inclusion),"contraction":str(contraction)})
    small = F(1,10**80)
    m,b = len(data["edges"]),data["B"]
    assert all(0 < v-small < v+small < F(1,10) for v in z[g+1:g+1+m])
    assert all(-F(1,100) < v-small < v+small < 0 for v in z[g+1+m:])
    tlo,thi = z[g]-small,z[g]+small
    scale = 10**60
    k = isqrt(z[g].numerator*scale**2//z[g].denominator)
    lower,upper = F(k,scale),F(k+1,scale)
    assert lower**2 < tlo < thi < upper**2
    def dec(v):
        return str(v//scale)+"."+str(v%scale).zfill(60)
    report = {"verified":True,"dimension":d,"geometry_dimension":g,"B":b,
              "root_sha256":sha(EV/"core-root.json"),"system_sha256":sha(EV/"core-system.json"),
              "boxes":checks,"r_strict_interval":[dec(k),dec(k+1)],
              "minimum_positive_weight":str(min(z[g+1:g+1+m])-small),
              "unweighted_center_count":1,"global_optimality_proved":False,
              "seconds":time.time()-start}
    (EV/"core-root-verified.json").write_text(json.dumps(report,indent=2),encoding="utf8")
    print("EXACT CORE ROOT ISOLATED",report["r_strict_interval"],flush=True)
    return data,z,small


def add(a,b):
    return a[0]+b[0],a[1]+b[1]


def neg(a):
    return -a[1],-a[0]


def sub(a,b):
    return add(a,neg(b))


def mul(a,b):
    vals = [x*y for x in a for y in b]
    return min(vals),max(vals)


def point(v):
    return F(v),F(v)


def vsub(a,b):
    return [sub(x,y) for x,y in zip(a,b)]


def dot(a,b):
    return add(mul(a[0],b[0]),mul(a[1],b[1]))


def cross(a,b):
    return sub(mul(a[0],b[1]),mul(a[1],b[0]))


def upper(data,z,rho):
    b,g = data["B"],data["G"]
    p = [[point(1),point(0)]]+[[(z[2*j]-rho,z[2*j]+rho),(z[2*j+1]-rho,z[2*j+1]+rho)]
                            for j in range(g//2)]
    centers = []
    for j,node in enumerate(data["center_core_nodes"]):
        centers.append(p[node] if node is not None else [point(v) for v in data["fixed_slack_centers"][str(j)]])
    q = p[:b]
    full = q+centers
    active = {tuple(face):j for j,face in enumerate(data["active_faces"])}
    edges = {frozenset(e) for e in data["edges"]}
    for i in range(b):
        node = data["center_core_nodes"][i]
        assert node is not None
        assert frozenset(((i-1)%b,node)) in edges
        assert frozenset((i,node)) in edges
    slack = []
    tlo = z[g]-rho
    # At q0, two root rods are exactly r*, every other center strictly farther.
    assert all(dot(vsub(q[0],centers[j]),vsub(q[0],centers[j]))[0] > z[g]+rho
               for j in range(21) if j not in (0,1))
    for face in data["all_faces"]:
        if tuple(face) in active:
            old_witness = b+21+active[tuple(face)]
            witness = data["old_node_to_core"][str(old_witness)]
            assert all(frozenset((witness,data["center_core_nodes"][v])) in edges for v in face)
        else:
            a,c,d = [[(iv[0]+iv[1])/2 for iv in centers[v]] for v in face]
            row1 = [2*(c[j]-a[j]) for j in (0,1)]
            row2 = [2*(d[j]-a[j]) for j in (0,1)]
            rhs1 = sum(v*v for v in c)-sum(v*v for v in a)
            rhs2 = sum(v*v for v in d)-sum(v*v for v in a)
            determinant = row1[0]*row2[1]-row1[1]*row2[0]
            assert determinant
            w = [(rhs1*row2[1]-rhs2*row1[1])/determinant,
                 (row1[0]*rhs2-row2[0]*rhs1)/determinant]
            w = [F(round(v*10**16),10**16) for v in w]
            iv = [point(v) for v in w]
            margin = min(tlo-dot(vsub(iv,centers[v]),vsub(iv,centers[v]))[1] for v in face)
            assert margin > 0, ("slack common point failed",face,margin)
            slack.append({"face":face,"rational_witness":list(map(str,w)),"margin":str(margin)})
    triangles = []
    for i in range(b):
        triangles.extend([((i-1)%b,i,b+i),(i,b+(i+1)%b,b+i)])
        c = centers[i]
        assert cross(q[(i-1)%b],q[i])[0] > 0 and dot(q[(i-1)%b],q[i])[0] > 0
        assert cross(q[(i-1)%b],c)[0] > 0 and cross(c,q[i])[0] > 0
    triangles.extend(tuple(b+v for v in face) for face in data["all_faces"])
    directed,ec = Counter(),Counter()
    links = defaultdict(list)
    for triangle in triangles:
        a,c,d = triangle
        orientation = cross(vsub(full[c],full[a]),vsub(full[d],full[a]))
        if orientation[1] < 0:
            c,d = d,c
            orientation = cross(vsub(full[c],full[a]),vsub(full[d],full[a]))
        assert orientation[0] > 0, ("triangle orientation",triangle,orientation)
        for u,v,w in ((a,c,d),(c,d,a),(d,a,c)):
            directed[u,v] += 1
            ec[tuple(sorted((u,v)))] += 1
            links[u].append((v,w))
    boundary = {tuple(sorted((i,(i+1)%b))) for i in range(b)}
    assert set(links) == set(range(b+21))
    for edge,multiplicity in ec.items():
        a,c = edge
        assert multiplicity == (1 if edge in boundary else 2)
        if edge not in boundary:
            assert directed[a,c] == directed[c,a] == 1
    for i in range(b):
        assert directed[i,(i+1)%b] == 1 and directed[(i+1)%b,i] == 0
    for v,ledges in links.items():
        adj = defaultdict(set)
        for a,c in ledges:
            adj[a].add(c)
            adj[c].add(a)
        seen,todo = {next(iter(adj))},[next(iter(adj))]
        while todo:
            for node in adj[todo.pop()]:
                if node not in seen:
                    seen.add(node)
                    todo.append(node)
        assert seen == set(adj)
        if v < b:
            assert sorted(k for k,neighbors in adj.items() if len(neighbors)==1) == sorted(((v-1)%b,(v+1)%b))
            assert all(len(neighbors) in (1,2) for neighbors in adj.values())
        else:
            assert all(len(neighbors)==2 for neighbors in adj.values())
    assert len(triangles) == 2*21+b-2 and len(ec) == 3*21+2*b-3
    # Mean angle/order is supplied by exact quadrants: unit vectors and adjacent
    # positive cross/dot do not alone exclude multiple winding.
    import importlib.util
    trigpath = ROOT.parent/"n13-global/independent_checks.py"
    spec = importlib.util.spec_from_file_location("upper21_trig",trigpath)
    extra = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(extra)
    numeric = json.loads((EV/"candidate-numeric.json").read_text())["theta"]
    anchors = [F(format(float(theta/(2*3.141592653589793)),".15f")) for theta in numeric]
    halfwidth = F(1,10**7)
    assert anchors[0] == 0 and all(0 < anchors[i]-halfwidth < anchors[i]+halfwidth < 1 for i in range(1,b))
    assert all(anchors[i]+halfwidth < anchors[i+1]-halfwidth for i in range(b-1))
    for i in range(1,b):
        def unit(t):
            return [(F(lo,extra.S60),F(hi,extra.S60)) for lo,hi in extra.trig(t)]
        assert cross(unit(anchors[i]-halfwidth),q[i])[0] > 0
        assert cross(q[i],unit(anchors[i]+halfwidth))[0] > 0
        assert dot(unit(anchors[i]),q[i])[0] > 0
    report = {"verified":True,"scope":"same isolated core radius attained as an upper bound for 21 disks",
              "vertices":b+21,"edges":len(ec),"triangles":len(triangles),"boundary_caps":b,
              "active_center_faces":len(active),"strict_slack_faces":slack,
              "covering_radius_equals_core_radius":True,"exact_nearest_anchor":0,
              "fixed_slack_centers":data["fixed_slack_centers"],
              "root_sha256":sha(EV/"core-root.json"),"global_optimality_proved":False}
    (EV/"upper-verified.json").write_text(json.dumps(report,indent=2),encoding="utf8")
    print("N21 EXACT SAME-ROOT WHOLE DISK UPPER COVER PASS",len(triangles),"triangles",flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--generate",action="store_true")
    args = parser.parse_args()
    if args.generate:
        generate()
    data,z,rho = verify()
    upper(data,z,rho)


if __name__ == "__main__":
    main()
