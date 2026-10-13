"""N21 proposal only: reuse local centers, minimize full witnessed graph, inspect KKT.

The external graph optimizer is an untrusted proposal generator. Exact upper
recheck and exact root/isolation are separate obligations.
"""
from pathlib import Path
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import argparse
import hashlib
import importlib.util
import json
import sys
import time
import numpy as np
from scipy.spatial import ConvexHull
from scipy.optimize import linprog
from scipy.linalg import null_space

ROOT = Path(__file__).resolve().parent
RESEARCH = ROOT.parent
LEGACY = RESEARCH/"session2/n1314"
EXTERNAL = RESEARCH/"disk-cover-proof-library/external/pinned/cover20/proof_bundle/discovery/discover20.py"


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def inspect(proposal):
    b,n = proposal["B"],21
    faces = proposal["faces"]
    active = [k for k in range(len(faces))
              if max(proposal["rod_slacks"][2*b+3*k:2*b+3*k+3]) < 2e-9]
    points = np.asarray(proposal["points"])
    q = np.column_stack((np.cos(proposal["theta"]),np.sin(proposal["theta"])))
    witnesses = []
    for k in active:
        a,c,d = points[list(faces[k])]
        witnesses.append(np.linalg.solve(2*np.array([c-a,d-a]),
                         np.array([c@c-a@a,d@d-a@a])))
    allpoints = np.vstack((q,points,witnesses))
    edges = [(i,b+i) for i in range(b)]+[(i,b+(i+1)%b) for i in range(b)]
    edges += [(b+n+j,b+v) for j,k in enumerate(active) for v in faces[k]]
    g = 2*(len(allpoints)-1)
    rows = []
    for u,v in edges:
        row = np.zeros(g+1)
        for node,sign in ((u,1),(v,-1)):
            if node:
                row[2*(node-1):2*node] += sign*2*(allpoints[u]-allpoints[v])
        row[-1] = -1
        rows.append(row)
    for i in range(1,b):
        row = np.zeros(g+1)
        row[2*(i-1):2*i] = 2*allpoints[i]
        rows.append(row)
    jac = np.asarray(rows)
    target = np.zeros(g+1)
    target[-1] = -1
    weights = np.linalg.lstsq(jac.T,target,rcond=1e-12)[0]
    # Search positive equilibrated stresses, but never certify using LP success.
    ne = len(edges)
    aug = np.column_stack((jac.T,np.zeros(g+1)))
    inequalities = np.zeros((ne,len(weights)+1))
    inequalities[:,:ne] = -np.eye(ne)
    inequalities[:,-1] = 1
    objective = np.zeros(len(weights)+1)
    objective[-1] = -1
    lp = linprog(objective,A_ub=inequalities,b_ub=np.zeros(ne),
                 A_eq=aug,b_eq=target,bounds=[(None,None)]*len(weights)+[(0,None)],method="highs")
    if lp.success:
        weights = lp.x[:-1]
    graphlap = np.zeros((len(allpoints),len(allpoints)))
    for (u,v),w in zip(edges,weights):
        graphlap[u,u] += w
        graphlap[v,v] += w
        graphlap[u,v] -= w
        graphlap[v,u] -= w
    for i in range(1,b):
        graphlap[i,i] += weights[ne+i-1]
    m = np.kron(graphlap[1:,1:],np.eye(2))
    a = jac[:,:-1]
    kernel = null_space(a,rcond=1e-8)
    tangent = np.linalg.eigvalsh(kernel.T@m@kernel).tolist()
    root = np.r_[allpoints[1:].ravel(),proposal["t"],weights]
    return {"N":21,"B":b,"geometry_dimension":g,"kkt_dimension":len(root),
            "active_faces":[faces[k] for k in active],"all_faces":faces,"edges":edges,
            "numeric_seed":root.tolist(),"numeric_stationarity_residual":float(max(abs(jac.T@weights-target))),
            "minimum_numeric_rod_weight":float(min(weights[:ne])),
            "numeric_circle_multipliers":weights[ne:].tolist(),
            "numeric_constraint_rank":int(np.linalg.matrix_rank(jac,tol=1e-8)),
            "numeric_geometry_rank":int(np.linalg.matrix_rank(a,tol=1e-8)),
            "numeric_tangent_eigenvalues":tangent,"proposal_only":True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--starts",type=int,default=3)
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location("proposal_cover20_graph",EXTERNAL)
    model = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(model)
    model.N = 21
    asset = LEGACY/"cfg/incumbents.json"
    original = json.loads(asset.read_text())["21"]
    points = np.asarray(original["centers"])
    hull = ConvexHull(points).vertices.tolist()
    turn_a = points[hull[1]]-points[hull[0]]
    turn_b = points[hull[2]]-points[hull[1]]
    if turn_a[0]*turn_b[1]-turn_a[1]*turn_b[0] < 0:
        hull.reverse()
    interior = [j for j in range(21) if j not in hull]
    points = points[hull+interior]
    model.B = len(hull)
    start = time.time()
    rng = np.random.default_rng(2026100321)
    best = None
    sys.path.insert(0,str(LEGACY/"py"))
    from rd import evalR_np
    for trial in range(args.starts):
        p = points.copy()
        if trial:
            p += rng.normal(0,0.002,p.shape)
        fa,ed = model.data(p)
        result = model.solve(p,fa,ed)
        actual,_ = evalR_np(np.asarray(result["points"]))
        result.update(N=21,B=model.B,actual_cover_radius_numeric=actual,
                      legacy_source_sha256=sha(asset),optimizer_source_sha256=sha(EXTERNAL),
                      proposal_only=True,trial=trial)
        print(f"trial {trial}: graph r={result['r']:.17g}, actual numeric r={actual:.17g}, success={result['success']}",flush=True)
        if best is None or actual < best["actual_cover_radius_numeric"]:
            best = result
    out = ROOT/"evidence"
    out.mkdir(exist_ok=True)
    (out/"candidate-numeric.json").write_text(json.dumps(best,indent=2),encoding="utf8")
    kkt = inspect(best)
    (out/"kkt-numeric.json").write_text(json.dumps(kkt,indent=2),encoding="utf8")
    frozen = {"n":21,"note":"Exact decimal-rational proposal; numerical discovery does not prove optimality",
              "centers_dec17":[[format(float(x),".17f") for x in p] for p in best["points"]]}
    (out/"candidate-dec17.json").write_text(json.dumps(frozen,indent=2),encoding="utf8")
    print(json.dumps({k:v for k,v in kkt.items() if k not in ("numeric_seed","edges","all_faces","active_faces")},
                     indent=2),flush=True)
    print("Numerical discovery elapsed",time.time()-start,flush=True)


if __name__ == "__main__":
    main()
