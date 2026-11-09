"""Search and checkpoint transferable flow proofs for completed outer shells."""

import argparse
import json
import os
from collections import defaultdict
from contextlib import nullcontext
from multiprocessing import get_context
from pathlib import Path

os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"

from find_belt_geometry import anchored_search, free_angle_flow, graph_flow, search
from find_transfer14 import map_flows, sparse_flow
from linear_flow14 import linear_angle_flow, mean_gauge
from verify_belt_geometry import certificate_domain, graph_from_faces
from verify_outer_windows import model_windows
from verify_patch14 import RADIUS
from verify_shell_fills import angle_map, check, mask, matches, origin_cap, parse_fill
from verify_shells import angles, parse_shell
from verify_template import certified_trial_radius


def init(n, b, file, depth, linear_only, anchored, full_angles, skip_linear=False,
         tight_radius=False, constrained_fit=False, use_mean=False, use_warm=False):
    global N, B, WINDOWS, DEPTH, LINEAR_ONLY, ANCHORED, FULL_ANGLES, SKIP_LINEAR, TRIAL, CONSTRAINED_FIT, USE_MEAN
    global USE_WARM
    N, B, DEPTH = n, b, depth
    LINEAR_ONLY, ANCHORED, FULL_ANGLES, SKIP_LINEAR = linear_only, anchored, full_angles, skip_linear
    WINDOWS = model_windows(file,n,b) if isinstance(file,str) else file
    TRIAL = certified_trial_radius() if tight_radius else RADIUS
    CONSTRAINED_FIT = constrained_fit
    USE_MEAN = use_mean
    USE_WARM = use_warm


def one(all_faces, edges, origin=None, cap=None, warm=None):
    graph = graph_from_faces(N, all_faces, origin, B)
    cap = min(cap,TRIAL) if cap is not None else None
    dist = certificate_domain(tuple(edges), B)[0]
    if dist is None:
        return {"cycle": True}
    mean = mean_gauge(dist) if USE_MEAN else None
    if not SKIP_LINEAR:
        seed = linear_angle_flow(graph, None, edges, cap, boundary=B,radius=TRIAL)
        if seed is not None and seed[1] > float(TRIAL) - 1e-6:
            proof = search(graph, lambda _: (None, None), edges, 0, [seed[0]], cap, B,radius=TRIAL)
            if proof is not None:
                return proof
        if USE_MEAN:
            seed = linear_angle_flow(graph,None,edges,cap,iterations=12,boundary=B,radius=TRIAL,anchor=mean)
            if seed is not None and seed[0] is not None and seed[1] > float(TRIAL)-1e-6:
                proof = search(graph,lambda _: (None,None),edges,0,[seed[0]],cap,B,anchors=[mean],radius=TRIAL)
                if proof is not None:
                    return proof
    if LINEAR_ONLY:
        return None
    if ANCHORED:
        start = warm.get(origin) if warm is not None else None
        for guess in (start,None) if start is not None else (None,):
            fit = free_angle_flow(graph,None,cap,B,with_prefix=True,angle_edges=edges if CONSTRAINED_FIT else None,
                                  with_layout=warm is not None,warm_start=guess)
            if fit is None or fit[3] < float(TRIAL)**2-1e-9:
                continue
            if warm is not None and fit[5]:
                warm[origin] = fit[1],fit[4],fit[3]
            proof = anchored_search(graph,edges,cap,B,fit[:4],DEPTH,TRIAL,mean)
            if proof is not None:
                return proof
        return None
    flow = free_angle_flow(graph, None, cap, B)
    return search(graph, lambda u: graph_flow(graph, None, u, cap, B), edges, DEPTH,
                  [flow] if flow is not None else (), cap, B,radius=TRIAL)


def propose(shell_faces, faces, h, edges, warm=None):
    all_faces = shell_faces + faces
    if h < N-B-1:
        tree = one(all_faces,edges,warm=warm)
        if tree is not None:
            return {"tree": tree}
    cap = origin_cap(N,B,h,WINDOWS)
    trees = []
    for u in range(B+h, N):
        tree = one(all_faces,edges,u,cap,warm)
        if tree is None:
            return None
        trees.append(tree)
    return {"trees": trees}


def thin(proof, shell_faces, faces, h):
    def reduce(tree, origin=None):
        _, _, free, edges = graph_from_faces(N,shell_faces+faces,origin,B)
        return map_flows(tree, lambda f: sparse_flow(f, free, edges))

    if "tree" in proof:
        return {**proof, "tree": reduce(proof["tree"])}
    return {**proof, "trees": [reduce(t, u) for u, t in enumerate(proof["trees"], start=B+h)]}


def solve(task):
    i, shell, fills = task
    h, shell_faces, _ = parse_shell(shell, N, B)
    edges = angles(B,B+h,shell_faces,WINDOWS)
    outer = mask(shell_faces, B)
    targets = []
    for line in fills:
        _, faces = parse_fill(line,N,B)
        full = angles(B,N,shell_faces+faces,WINDOWS) if FULL_ANGLES else None
        targets.append((line, faces, mask(faces,B)|outer, full, angle_map(full) if full is not None else None))
    covered, proofs = set(), []
    warm = {} if USE_WARM else None
    for j, (line, faces, _, full, _) in enumerate(targets):
        if j in covered:
            continue
        proof = propose(shell_faces,faces,h,full if full is not None else edges,warm)
        if proof is None:
            continue
        if FULL_ANGLES:
            proof["full_angles"] = True
        if TRIAL != RADIUS:
            proof["tight"] = True
        small = thin(proof,shell_faces,faces,h)
        try:
            needs, _, extra = check(small,N,B,h,shell_faces,faces,edges,WINDOWS,full)
            proof = small
        except ValueError:
            needs, _, extra = check(proof,N,B,h,shell_faces,faces,edges,WINDOWS,full)
        covered.update(j1 for j1, (_, _, have, _, domain) in enumerate(targets)
                       if matches(have,domain,needs,extra))
        proofs.append({**proof, "fill": line})
    open_fills = [line for j,line in enumerate(fills) if j not in covered]
    record = {"index":i,"shell":shell,"proofs":proofs,"open":open_fills}
    return record,len(covered),len(fills)


def safe_solve(task):
    try:
        return solve(task)
    except MemoryError:
        return task[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shells", type=Path)
    parser.add_argument("fills", type=Path)
    parser.add_argument("windows", type=Path)
    parser.add_argument("--disks", type=int, required=True)
    parser.add_argument("--boundary", type=int, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--depth", type=int, default=1)
    parser.add_argument("--linear-only", action="store_true")
    parser.add_argument("--anchored", action="store_true")
    parser.add_argument("--full-angles", action="store_true")
    parser.add_argument("--skip-linear", action="store_true")
    parser.add_argument("--tight-radius", action="store_true")
    parser.add_argument("--constrained-fit", action="store_true")
    parser.add_argument("--mean-gauge", action="store_true")
    parser.add_argument("--warm", action="store_true")
    args = parser.parse_args()
    if args.skip_linear and args.linear_only:
        parser.error("Cannot skip linear proposals in a linear-only run")
    shells = args.shells.read_text(encoding="utf-8").splitlines()
    groups = defaultdict(list)
    with args.fills.open(encoding="utf-8") as f:
        for line in f:
            i = int(line.split("\t",1)[0])
            if not 0 <= i < len(shells):
                raise ValueError("Unknown shell")
            groups[i].append(line.rstrip("\n"))
    done = set()
    if args.out.exists():
        with args.out.open(encoding="utf-8") as old:
            for line in old:
                record = json.loads(line)
                i = record["index"]
                if i not in groups or record["shell"] != shells[i] or i in done:
                    raise ValueError("Checkpoint mismatch")
                done.add(i)
    tasks = [(i,shells[i],f) for i,f in sorted(groups.items()) if i not in done]
    n = len(tasks)
    windows = model_windows(args.windows,args.disks,args.boundary)
    print(f"shells to solve={n}", flush=True)
    covered = total = 0
    initargs = (args.disks,args.boundary,windows,args.depth,args.linear_only,
                args.anchored,args.full_angles,args.skip_linear,args.tight_radius,args.constrained_fit,
                args.mean_gauge,args.warm)
    if args.workers == 1:
        init(*initargs)
        workers = nullcontext(None)
    else:
        workers = get_context("spawn").Pool(processes=args.workers, initializer=init,
                                           initargs=initargs, maxtasksperchild=64)
    with args.out.open("a",encoding="utf-8") as out, workers as pool:
        results = map(safe_solve,tasks) if pool is None else pool.imap_unordered(safe_solve,tasks)
        for j, r in enumerate(results,1):
            if isinstance(r,int):
                print(f"shell {r}: memory allocation failed, checkpoint omitted", flush=True)
                continue
            record, solved, tried = r
            out.write(json.dumps(record,separators=(",",":"))+"\n")
            out.flush()
            covered += solved
            total += tried
            if j % max(1,min(50,n//10)) == 0 or j == n:
                print(f"shells={j}/{n} latest={record['index']} excluded={covered}/{total}",flush=True)


if __name__ == "__main__":
    main()
