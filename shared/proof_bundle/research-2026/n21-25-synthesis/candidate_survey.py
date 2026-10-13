"""Numerical survey + rigorous fixed rational upper bounds for n22..25.

Correctly uses boundary owners, not only convex-hull vertices. Degenerate
boundary collinear extensions are NOT declared optimality proofs.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import os
os.environ["OPENBLAS_NUM_THREADS"]="1"
os.environ["OMP_NUM_THREADS"]="1"
import argparse
import hashlib
import json
import sys
import time
import numpy as np
from scipy.spatial import Delaunay
from scipy.optimize import minimize
from scipy.linalg import null_space

ROOT=Path(__file__).resolve().parent
RESEARCH=ROOT.parent
LEGACY=RESEARCH/"session2/n1314"
sys.path.insert(0,str(LEGACY/"py"))
import certify_cfg
from rd import evalR_np


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def arrangement(c,r):
    boundary=np.where(np.linalg.norm(c,axis=1)+r >= 1-1e-7)[0].tolist()
    boundary.sort(key=lambda j:np.arctan2(c[j,1],c[j,0]))
    inner=[j for j in range(len(c)) if j not in boundary]
    c=c[boundary+inner]
    b=len(boundary);n=len(c)
    # Delaunay outside skinny triangles are not required clipped Voronoi faces.
    kept=[]
    for triangle in Delaunay(c).simplices:
        a,d,e=c[triangle]
        try:
            witness=np.linalg.solve(2*np.array([d-a,e-a]),[d@d-a@a,e@e-a@a])
        except np.linalg.LinAlgError:
            continue
        if witness@witness < 1-1e-9:
            kept.append(tuple(sorted(map(int,triangle))))
    kept=sorted(kept)
    assert len(kept)==2*n-b-2,(n,b,len(kept))
    edges=Counter(tuple(sorted((fa[k],fa[(k+1)%3]))) for fa in kept for k in range(3))
    assert {e for e,k in edges.items() if k==1}=={tuple(sorted((i,(i+1)%b))) for i in range(b)}
    return c,b,kept,boundary+inner


def solve(c,b,faces):
    n=len(c)
    ed=np.array([(i,b+i) for i in range(b)]+[(i,b+(i+1)%b) for i in range(b)]+
                [(b+n+k,b+v) for k,fa in enumerate(faces) for v in fa])
    angles=np.unwrap(np.arctan2(c[:b,1],c[:b,0]))
    rotate=(angles[0]+angles[1])/2
    c=c@np.array([[np.cos(rotate),-np.sin(rotate)],[np.sin(rotate),np.cos(rotate)]])
    # Actual angle midpoint seeds respect non-uniform boundary arcs.
    angles=np.unwrap(np.arctan2(c[:b,1],c[:b,0]))
    switch=np.r_[(angles[:-1]+angles[1:])/2,(angles[-1]+angles[0]+2*np.pi)/2]
    switch=(switch-switch[0])%(2*np.pi)
    w=[]
    for fa in faces:
        a,d,e=c[list(fa)]
        w.append(np.linalg.solve(2*np.array([d-a,e-a]),[d@d-a@a,e@e-a@a]))
    x=np.r_[switch[1:],c.ravel(),np.array(w).ravel(),evalR_np(c)[0]**2]
    nv=len(x)
    def constraints(x,jac=False):
        q=np.c_[np.cos(np.r_[0,x[:b-1]]),np.sin(np.r_[0,x[:b-1]])]
        z=np.vstack((q,x[b-1:-1].reshape(-1,2)))
        delta=z[ed[:,0]]-z[ed[:,1]]
        value=x[-1]-np.sum(delta*delta,axis=1)
        if not jac:
            return value
        result=np.zeros((len(ed),nv));result[:,-1]=1
        for k,(u,v) in enumerate(ed):
            for node,sign in ((u,-1),(v,1)):
                if node==0:
                    continue
                if node<b:
                    result[k,node-1]+=2*sign*delta[k]@np.array([-q[node,1],q[node,0]])
                else:
                    j=b-1+2*(node-b)
                    result[k,j:j+2]+=2*sign*delta[k]
        return result
    gradient=np.zeros(nv);gradient[-1]=1
    solution=minimize(lambda x:x[-1],x,jac=lambda x:gradient,method="SLSQP",
                      constraints={"type":"ineq","fun":constraints,"jac":lambda x:constraints(x,True)},
                      options={"ftol":1e-14,"maxiter":1000})
    q=np.c_[np.cos(np.r_[0,solution.x[:b-1]]),np.sin(np.r_[0,solution.x[:b-1]])]
    z=np.vstack((q,solution.x[b-1:-1].reshape(-1,2)))
    lens=np.sum((z[ed[:,0]]-z[ed[:,1]])**2,axis=1)
    return {"N":n,"B":b,"success":bool(solution.success),"message":str(solution.message),
            "points":z[b:b+n].tolist(),"witnesses":z[b+n:].tolist(),
            "theta":np.r_[0,solution.x[:b-1]].tolist(),"faces":faces,"edges":ed.tolist(),
            "t":float(solution.fun),"r":float(np.sqrt(solution.fun)),
            "rod_slacks":(solution.fun-lens).tolist(),"proposal_only":True}


def inspection(p):
    b,n=p["B"],p["N"]
    active=[k for k in range(len(p["faces"])) if max(p["rod_slacks"][2*b+3*k:2*b+3*k+3])<1e-9]
    points=np.array(p["points"])
    q=np.c_[np.cos(p["theta"]),np.sin(p["theta"])]
    witnesses=np.array(p["witnesses"])[active]
    z=np.vstack((q,points,witnesses))
    edges=[(i,b+i) for i in range(b)]+[(i,b+(i+1)%b) for i in range(b)]
    edges += [(b+n+k,b+v) for k,fa in enumerate([p["faces"][k] for k in active]) for v in fa]
    g=2*(len(z)-1)
    jac=[]
    for u,v in edges:
        row=np.zeros(g+1);row[-1]=-1
        for node,sign in ((u,1),(v,-1)):
            if node:
                row[2*(node-1):2*node]=2*sign*(z[u]-z[v])
        jac.append(row)
    for i in range(1,b):
        row=np.zeros(g+1);row[2*(i-1):2*i]=2*z[i]
        jac.append(row)
    jac=np.array(jac)
    target=np.zeros(g+1);target[-1]=-1
    stress=np.linalg.lstsq(jac.T,target,rcond=1e-10)[0]
    degree=Counter(v for e in edges for v in e)
    return {"active_faces":[p["faces"][k] for k in active],"all_faces":p["faces"],"edges":edges,
            "N":n,"B":b,"G":g,"M":len(edges),"D":g+1+len(jac),
            "unweighted_center_indices":[j for j in range(n) if not degree[b+j]],
            "numeric_constraint_rank":int(np.linalg.matrix_rank(jac,tol=1e-8)),
            "numeric_stationarity_residual":float(max(abs(jac.T@stress-target))),
            "minimum_numeric_rod_weight":float(min(stress[:len(edges)])),
            "numeric_seed":np.r_[z[1:].ravel(),p["t"],stress].tolist(),
            "proposal_only":True}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--n",nargs="+",type=int,default=[25,22,23,24])
    parser.add_argument("--certify",action="store_true")
    args=parser.parse_args()
    assert all(n in (22,23,24,25) for n in args.n)
    source=LEGACY/"cfg/incumbents.json"
    assets=json.loads(source.read_text())
    for n in args.n:
        out=ROOT/f"evidence/n{n}"
        assert not out.exists(),"Use new candidate output, do not replace evidence"
        out.mkdir(parents=True)
        c=np.array(assets[str(n)]["centers"])
        c,b,faces,perm=arrangement(c,assets[str(n)]["r"])
        p=solve(c,b,faces)
        actual=evalR_np(np.array(p["points"]))[0]
        p.update(cover_radius_numeric=actual,source_sha256=sha(source),center_permutation=perm)
        (out/"candidate-numeric.json").write_text(json.dumps(p,indent=2),encoding="utf8")
        info=inspection(p)
        (out/"kkt-numeric.json").write_text(json.dumps(info,indent=2),encoding="utf8")
        decimals={"n":n,"centers_dec17":[[format(float(v),".17f") for v in point] for point in p["points"]]}
        proposal=out/"candidate-dec17.json"
        proposal.write_text(json.dumps(decimals,indent=2),encoding="utf8")
        print(f"N{n}: B={b}, graph r={p['r']:.17g}, true numeric r={actual:.17g}, active={len(info['active_faces'])}, "
              f"zero centers={info['unweighted_center_indices']}, constraint rank={info['numeric_constraint_rank']}/{info['M']+b-1}",
              flush=True)
        if args.certify:
            result=certify_cfg.certify(str(proposal),"centers_dec17",17,verbose=False)
            assert result["bb_ok"]
            result={k:str(v) if isinstance(v,F) else v for k,v in result.items()}
            result.update(verified_upper_bound=True,global_optimality_proved=False,
                          caliber="fixed exact rational centers, not same algebraic optimum root")
            (out/"rational-upper-verified.json").write_text(json.dumps(result,indent=2),encoding="utf8")
            print("N",n,"D1+D2 rigorous fixed rational upper:",result["claim"],flush=True)


if __name__=="__main__":
    main()
