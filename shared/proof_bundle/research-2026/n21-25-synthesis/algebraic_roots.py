"""Fresh n22/23/24 core root and entire-disk upper certificates.

Reuses inspected squared-distance evaluation and rational interval operations,
NOT any earlier fixed-n theorem. Reports and mathematical certificates separated.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter,defaultdict
from math import isqrt
import argparse
import hashlib
import importlib.util
import json
import time

ROOT=Path(__file__).resolve().parent
EV=ROOT/"evidence"
source=ROOT.parent/"n21-global/root_certificate.py"
spec=importlib.util.spec_from_file_location("shared_squared_distance",source)
R=importlib.util.module_from_spec(spec);spec.loader.exec_module(R)
evaluate=R.evaluate
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def prepare(n):
    folder=EV/f"n{n}"
    numeric=json.loads((folder/"kkt-numeric.json").read_text())
    proposal=json.loads((folder/"candidate-numeric.json").read_text())
    oldg,b=numeric["G"],numeric["B"]
    degree=Counter(v for edge in numeric["edges"] for v in edge)
    omitted=[j for j in range(oldg//2+1) if not degree[j]]
    assert all(b<=j<b+n for j in omitted)
    keep=[j for j in range(oldg//2+1) if j not in omitted]
    mapping={j:i for i,j in enumerate(keep)}
    seed=[v for j in keep[1:] for v in numeric["numeric_seed"][2*(j-1):2*j]]
    seed+=numeric["numeric_seed"][oldg:]
    g=2*(len(keep)-1)
    fixed={str(j-b):[format(float(v),".17f") for v in proposal["points"][j-b]] for j in omitted}
    data={"N":n,"B":b,"G":g,"P":g+1,"D":len(seed),
          "edges":[[mapping[u],mapping[v]] for u,v in numeric["edges"]],
          "active_faces":numeric["active_faces"],"all_faces":numeric["all_faces"],
          "center_core_nodes":[mapping.get(b+i) for i in range(n)],
          "fixed_slack_centers":fixed,"old_node_to_core":{str(k):v for k,v in mapping.items()},
          "numeric_seed":seed,"proposal_sha256":sha(folder/"candidate-numeric.json"),
          "numeric_kkt_sha256":sha(folder/"kkt-numeric.json")}
    target=folder/"core-system.json"
    assert not target.exists()
    target.write_text(json.dumps(data,indent=2),encoding="utf8")
    return data


def generate(n):
    import mpmath as mp
    mp.mp.dps=110
    folder=EV/f"n{n}"
    data=prepare(n)
    z=[mp.mpf(str(v)) for v in data["numeric_seed"]]
    start=time.time()
    for k in range(9):
        f,J,_=evaluate(z,data,mp.mpf(0))
        residual=max(abs(v) for v in f)
        print("N",n,"NEWTON proposal",k,mp.nstr(residual,8),flush=True)
        if residual<mp.mpf("1e-100"):
            break
        step=mp.lu_solve(mp.matrix(J),mp.matrix(f))
        z=[v-d for v,d in zip(z,step)]
    f,J,_=evaluate(z,data,mp.mpf(0))
    assert max(abs(v) for v in f)<mp.mpf("1e-95")
    inverse=mp.inverse(mp.matrix(J))
    qx,qy=10**90,10**80
    root={"dimension":data["D"],"Qx":str(qx),"Qy":str(qy),
          "xnum":[str(int(mp.nint(v*qx))) for v in z],
          "Ynum":[[str(int(mp.nint(inverse[i,j]*qy))) for j in range(data["D"])] for i in range(data["D"])],
          "system_sha256":sha(folder/"core-system.json"),
          "radius_proposal":mp.nstr(mp.sqrt(z[data["G"]]),100)}
    target=folder/"core-root.json"
    assert not target.exists()
    target.write_text(json.dumps(root,separators=(",",":")),encoding="utf8")
    print("N",n,"root proposed",root["radius_proposal"],"seconds",round(time.time()-start,2),flush=True)


def verify(n,output):
    folder=EV/f"n{n}"
    data=json.loads((folder/"core-system.json").read_text())
    cert=json.loads((folder/"core-root.json").read_text())
    assert cert["system_sha256"]==sha(folder/"core-system.json") and data["N"]==n
    d,g=data["D"],data["G"]
    z=[F(int(v),int(cert["Qx"])) for v in cert["xnum"]]
    y=[[F(int(v),int(cert["Qy"])) for v in row] for row in cert["Ynum"]]
    assert len(z)==len(y)==d and all(len(row)==d for row in y)
    f,J,H=evaluate(z,data,F(0))
    residual=[sum((a*b for a,b in zip(row,f)),F(0)) for row in y]
    columns=[[(k,J[k][j]) for k in range(d) if J[k][j]] for j in range(d)]
    rowbound=[sum(abs(F(int(i==j))-sum((y[i][k]*v for k,v in columns[j]),F(0))) for j in range(d)) for i in range(d)]
    drift=[F(0)]*d
    for k,h in enumerate(H):
        drift[k]=sum(abs(v) for v in h.values())
        for (j,l),v in h.items():
            drift[len(H)+j]+=2*abs(v)
    budgets=[sum((abs(a)*v for a,v in zip(row,drift)),F(0)) for row in y]
    checks=[]
    for rho in (F(1,10**60),F(1,10**80)):
        inclusion=max(abs(r)/rho+ee+rho*bb for r,ee,bb in zip(residual,rowbound,budgets))
        contraction=max(ee+rho*bb for ee,bb in zip(rowbound,budgets))
        assert inclusion<1 and contraction<1
        checks.append({"rho":str(rho),"inclusion":str(inclusion),"contraction":str(contraction)})
    rho=F(1,10**80)
    m=len(data["edges"])
    assert all(0<v-rho<v+rho<F(1,10) for v in z[g+1:g+1+m])
    assert all(-F(1,100)<v-rho<v+rho<0 for v in z[g+1+m:])
    scale=10**60
    k=isqrt(z[g].numerator*scale**2//z[g].denominator)
    assert F(k,scale)**2<z[g]-rho<z[g]+rho<F(k+1,scale)**2
    def dec(v):
        return str(v//scale)+"."+str(v%scale).zfill(60)
    result={"verified":True,"N":n,"D":d,"G":g,"B":data["B"],"M":m,"boxes":checks,
            "r_strict_interval":[dec(k),dec(k+1)],
            "unweighted_center_count":len(data["fixed_slack_centers"]),
            "root_sha256":sha(folder/"core-root.json"),"system_sha256":sha(folder/"core-system.json"),
            "source_sha256":sha(Path(__file__)),"shared_evaluator_sha256":sha(source),
            "global_optimality_proved":False}
    (output/"root-verified.json").write_text(json.dumps(result,indent=2),encoding="utf8")
    print("N",n,"EXACT ROOT PASS",result["r_strict_interval"],flush=True)
    return data,z,rho


def upper(n,data,z,rho,output):
    b,g=data["B"],data["G"]
    p=[[R.point(1),R.point(0)]]+[[(z[2*j]-rho,z[2*j]+rho),(z[2*j+1]-rho,z[2*j+1]+rho)] for j in range(g//2)]
    c=[p[node] if node is not None else [R.point(v) for v in data["fixed_slack_centers"][str(j)]]
       for j,node in enumerate(data["center_core_nodes"])]
    q=p[:b];points=q+c
    edges={frozenset(e) for e in data["edges"]}
    for i,node in enumerate(data["center_core_nodes"][:b]):
        assert node is not None
        assert frozenset((i,node)) in edges and frozenset(((i-1)%b,node)) in edges
        assert R.cross(q[(i-1)%b],q[i])[0]>0 and R.dot(q[(i-1)%b],q[i])[0]>0
        assert R.cross(q[(i-1)%b],c[i])[0]>0 and R.cross(c[i],q[i])[0]>0
    tlo=z[g]-rho
    assert all(R.dot(R.vsub(q[0],c[j]),R.vsub(q[0],c[j]))[0]>z[g]+rho for j in range(n) if j not in (0,1))
    active={tuple(f):j for j,f in enumerate(data["active_faces"])}
    slack=[]
    for face in data["all_faces"]:
        if tuple(face) in active:
            witness=data["old_node_to_core"][str(b+n+active[tuple(face)])]
            assert all(frozenset((witness,data["center_core_nodes"][v])) in edges for v in face)
        else:
            a,d,e=[[(lo+hi)/2 for lo,hi in c[j]] for j in face]
            u,v=[2*(d[k]-a[k]) for k in (0,1)],[2*(e[k]-a[k]) for k in (0,1)]
            h,k=sum(x*x for x in d)-sum(x*x for x in a),sum(x*x for x in e)-sum(x*x for x in a)
            det=u[0]*v[1]-u[1]*v[0]
            assert det
            center=[(h*v[1]-k*u[1])/det,(u[0]*k-v[0]*h)/det]
            center=[F(round(x*10**16),10**16) for x in center]
            iv=[R.point(x) for x in center]
            margin=min(tlo-R.dot(R.vsub(iv,c[j]),R.vsub(iv,c[j]))[1] for j in face)
            assert margin>0,("slack face",n,face)
            slack.append({"face":face,"witness":list(map(str,center)),"margin":str(margin)})
    triangles=[]
    for i in range(b):
        triangles += [((i-1)%b,i,b+i),(i,b+(i+1)%b,b+i)]
    triangles += [tuple(b+j for j in face) for face in data["all_faces"]]
    directed,ec=Counter(),Counter();links=defaultdict(list)
    for a,d,e in triangles:
        orientation=R.cross(R.vsub(points[d],points[a]),R.vsub(points[e],points[a]))
        if orientation[1]<0:
            d,e=e,d;orientation=R.cross(R.vsub(points[d],points[a]),R.vsub(points[e],points[a]))
        assert orientation[0]>0,("triangle orientation",n,(a,d,e))
        for u,v,w in ((a,d,e),(d,e,a),(e,a,d)):
            directed[u,v]+=1;ec[tuple(sorted((u,v)))]+=1;links[u].append((v,w))
    boundary={tuple(sorted((i,(i+1)%b))) for i in range(b)}
    adjacency=defaultdict(set)
    for (a,d),count in ec.items():
        assert count==(1 if (a,d) in boundary else 2)
        if (a,d) not in boundary:
            assert directed[a,d]==directed[d,a]==1
        adjacency[a].add(d);adjacency[d].add(a)
    for i in range(b):
        assert directed[i,(i+1)%b]==1 and directed[(i+1)%b,i]==0
    reached,todo={0},[0]
    while todo:
        for v in adjacency[todo.pop()]:
            if v not in reached:
                reached.add(v);todo.append(v)
    assert reached==set(range(b+n))
    for vertex,les in links.items():
        adj=defaultdict(set)
        for a,d in les:
            adj[a].add(d);adj[d].add(a)
        seen,todo={next(iter(adj))},[next(iter(adj))]
        while todo:
            for v in adj[todo.pop()]:
                if v not in seen:
                    seen.add(v);todo.append(v)
        assert seen==set(adj)
        if vertex<b:
            assert sorted(v for v,ns in adj.items() if len(ns)==1)==sorted(((vertex-1)%b,(vertex+1)%b))
            assert all(len(ns) in (1,2) for ns in adj.values())
        else:
            assert all(len(ns)==2 for ns in adj.values())
    assert len(triangles)==2*n+b-2 and len(ec)==3*n+2*b-3
    # Real angle samples propose isolating rays, exact trig/interval cross accepts.
    import math
    trigsource=ROOT.parent/"n13-global/independent_checks.py"
    sp=importlib.util.spec_from_file_location("upper_survey_trig",trigsource)
    trig=importlib.util.module_from_spec(sp);sp.loader.exec_module(trig)
    proposed=json.loads((EV/f"n{n}/candidate-numeric.json").read_text())["theta"]
    th=[F(format(float(x/(2*math.pi)),".15f")) for x in proposed]
    hw=F(1,10**7)
    assert th[0]==0 and all(0<x-hw<x+hw<1 for x in th[1:])
    assert all(th[i]+hw<th[i+1]-hw for i in range(b-1))
    def unit(t):
        return [(F(lo,trig.S60),F(hi,trig.S60)) for lo,hi in trig.trig(t)]
    for i in range(1,b):
        assert R.cross(unit(th[i]-hw),q[i])[0]>0
        assert R.cross(q[i],unit(th[i]+hw))[0]>0
        assert R.dot(unit(th[i]),q[i])[0]>0
    result={"verified":True,"N":n,"same_core_root_entire_disk_upper":True,"cover_radius_equals_core_radius":True,
            "vertices":b+n,"edges":len(ec),"triangles":len(triangles),"caps":b,
            "active_center_faces":len(active),"strict_slack_faces":slack,
            "fixed_slack_centers":data["fixed_slack_centers"],
            "root_sha256":sha(EV/f"n{n}/core-root.json"),"global_optimality_proved":False}
    (output/"upper-verified.json").write_text(json.dumps(result,indent=2),encoding="utf8")
    print("N",n,"EXACT SAME-ROOT WHOLE-DISK UPPER PASS",len(triangles),"triangles",flush=True)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--n",type=int,nargs="+",default=[22,23,24])
    parser.add_argument("--generate",action="store_true")
    parser.add_argument("--tag",default="algebraic-check1")
    args=parser.parse_args()
    for n in args.n:
        assert n in (22,23,24)
        output=EV/f"n{n}"/args.tag
        assert not output.exists()
        output.mkdir()
        if args.generate:
            generate(n)
        data,z,rho=verify(n,output)
        upper(n,data,z,rho,output)


if __name__=="__main__":
    main()
