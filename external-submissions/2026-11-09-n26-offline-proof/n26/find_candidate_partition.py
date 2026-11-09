"""Propose flow certificates outside the certified candidate prefix box."""

import argparse
import gc
import json
import warnings
from collections import deque
from math import floor
from pathlib import Path

from find_belt_geometry import anchored_search, free_angle_flow, search
import numpy as np
from scipy.optimize import OptimizeWarning, linprog

from linear_flow14 import linear_angle_flow, mean_gauge
from verify_belt_geometry import certificate_domain, closure, energy_affine, flow_affine, gauge_weights, split_edges, verify_tree
from verify_belt_pruning import SCALE
from verify_candidate_cell import ROOT, halfturn_cut, partition_domain, targets


def seed_terms(seeds):
    flows, anchors, energies = [], [], []
    for p in seeds:
        f = p["flows"]
        flows.extend(f)
        anchors.extend(p.get("anchors",[0]*len(f)))
        energies.extend(p.get("energies",[]))
    return flows,anchors,energies


def proposal(graph, edges, trial, refine, seeds=(), mean=None, *, boundary=16, cap=None):
    flows,anchors,energies = seed_terms(seeds)
    if seeds:
        result = search(graph,lambda _: (None,None),edges,0,flows,cap,boundary,
                        anchors=anchors,energies=energies,radius=trial,adaptive_energy=True)
        if result is not None:
            verify_tree(result,graph,edges,cap,boundary,radius=trial)
            return result
    result = None
    for anchor in (0,mean) if mean is not None else (0,):
        seed = linear_angle_flow(graph,None,edges,cap,iterations=10,boundary=boundary,radius=trial,anchor=anchor)
        if seed is not None and seed[0] is not None:
            flows.append(seed[0])
            anchors.append(anchor)
            if seed[1] > float(trial)-1e-8 or len(flows) > 1:
                result = search(graph,lambda _: (None,None),edges,0,flows,cap,boundary,
                                anchors=anchors,energies=energies,radius=trial,adaptive_energy=True)
                if result is not None:
                    break
    if result is None and refine:
        fit = free_angle_flow(graph,None,cap,boundary,with_prefix=True,angle_edges=edges)
        if fit is not None and fit[3] > float(trial)**2+1e-11:
            result = anchored_search(graph,edges,cap,boundary,fit,0,trial,mean)
    if result is not None:
        verify_tree(result,graph,edges,cap,boundary,radius=trial)
    return result


def tighten(graph,edges,trial,lo,hi,mean=None,*,boundary=16,cap=None,seeds=()):
    anchor = 0 if mean is None else mean
    coordinates = sorted(range(1,boundary),key=lambda j: hi[j]-lo[j],reverse=True)

    def test_cut(j,sign,value,flows,anchors,energies=()):
        m = sign*(floor(value*SCALE)-2)
        if not lo[j] < m < hi[j]:
            return None
        removed_width = m-lo[j] if sign > 0 else hi[j]-m
        if removed_width < max(8,(hi[j]-lo[j])//25):
            return None
        cut = (j,0,-m) if sign > 0 else (0,j,m)
        changed = edges+[cut]
        proof = search(graph,lambda _: (None,None),changed,0,flows,cap,boundary,
                       anchors=anchors,energies=energies,radius=trial,adaptive_energy=True)
        if proof is not None:
            verify_tree(proof,graph,changed,cap,boundary,radius=trial)
            return j,m,sign,proof
        return None

    if seeds:
        flows,anchors,energies = seed_terms(seeds)
        dist,lower,upper,rows = certificate_domain(tuple(edges),boundary)
        all_rows = rows + [flow_affine(f,graph,lower,upper,cap,True,anchor=j,dist=dist,radius=trial)
                           for f,j in zip(flows,anchors)]
        all_rows += [energy_affine(e,graph,dist,cap,trial) for e in energies]
        a = np.asarray([row for row,_ in all_rows],dtype=float)
        b = np.asarray([rhs for _,rhs in all_rows],dtype=float)
        bounds = [(float(l),float(h)) for l,h in zip(lower,upper)]
        for j in coordinates[:8]:
            for sign in (1,-1):
                objective = np.zeros(boundary)
                objective[j] = sign
                with warnings.catch_warnings():
                    warnings.filterwarnings("ignore","Unrecognized options detected",OptimizeWarning)
                    res = linprog(objective,A_ub=a,b_ub=b,bounds=bounds,method="highs",options={"threads":1})
                if res.success:
                    cut = test_cut(j,sign,res.fun,flows,anchors,energies)
                    if cut is not None:
                        return cut

    for j in coordinates[:8]:
        if hi[j]-lo[j] <= 4:
            continue
        for sign in (1,-1):
            seed = linear_angle_flow(graph,None,edges,cap,iterations=6,boundary=boundary,radius=trial,
                                     prefix_goal=(j,sign),anchor=anchor)
            if seed is None or seed[0] is None:
                continue
            cut = test_cut(j,sign,seed[1],[seed[0]],[anchor])
            if cut is not None:
                return cut
    return None


def frontier(tree, edges, boundary=16):
    if tree.get("open") is True:
        yield tree,edges
    elif "split" in tree:
        *_,low,high = split_edges(tree["split"],boundary)
        yield from frontier(tree["lower"],edges+[low],boundary)
        yield from frontier(tree["upper"],edges+[high],boundary)


def proof_seeds(tree, edges, boundary=16):
    if "exclusion" in tree and "flows" in tree["exclusion"]:
        dist = closure(edges,boundary)
        if dist is not None:
            yield center_of(dist),tree["exclusion"]
    elif "split" in tree:
        *_,low,high = split_edges(tree["split"],boundary)
        yield from proof_seeds(tree["lower"],edges+[low],boundary)
        yield from proof_seeds(tree["upper"],edges+[high],boundary)


def center_of(dist):
    return tuple(x-row[0] for x,row in zip(dist[0],dist))


def balanced_split(dist, mean):
    n = len(dist)
    matrix = np.asarray(dist,dtype=np.int64)
    weights = np.asarray(gauge_weights([1]*n if mean is None else mean,n),dtype=float)

    def score(i,j,m):
        # A closed difference matrix needs at most one traversal of the new edge.
        narrowed = np.maximum(matrix,matrix[:,i,None]+m+matrix[None,j,:])
        widths = weights @ (-narrowed-narrowed.T)
        return widths @ widths

    best = None
    for i in range(n):
        for j in range(i+1,n):
            lo,hi = dist[i][j],-dist[j][i]
            if hi-lo < 2:
                continue
            m = (lo+hi)//2
            rank = (max(score(i,j,m),score(j,i,-m)),lo-hi,i,j)
            if best is None or rank < best:
                best = rank
    return best[2:] if best is not None else (0,1)


def carve_local(tree, edges, data):
    for node, domain in list(frontier(tree,edges)):
        cuts = [(j,m,sign) for j in range(1,16)
                for m,sign in ((data["lo"][j],1),(data["hi"][j],-1))]
        inside = [(0,j,m) if sign > 0 else (j,0,-m) for j,m,sign in cuts]
        if closure(domain+inside,16) is None:
            continue
        for (j,m,sign), constraint in zip(cuts,inside):
            dist = closure(domain,16)
            if not dist[0][j] < m < -dist[j][0]:
                continue
            child, outside = {"open":True}, {"open":True}
            low, high = (outside,child) if sign > 0 else (child,outside)
            node.clear()
            node.update(split=[j,m],lower=low,upper=high)
            node = child
            domain = domain+[constraint]
        dist = closure(domain,16)
        if all(a >= l and -row[0] <= h for a,row,l,h in zip(dist[0],dist,data["lo"],data["hi"])):
            node.clear()
            node["local"] = True


def save(tree, path):
    temporary = path.with_name(path.name+".tmp")
    with temporary.open("w",encoding="utf-8") as stream:
        json.dump(tree,stream,separators=(",",":"))
        stream.write("\n")
    temporary.replace(path)


def search_domains(root, graph, edges, trial, nodes, checkpoint, *, boundary=16, cap=None,
                   tighten_bounds=False, refine=False, reuse=False, relative=False, use_mean=False, box=None):
    queue = deque(frontier(root,edges,boundary))
    cache = deque(proof_seeds(root,edges,boundary),maxlen=512) if reuse else None
    excluded = local = tried = 0

    def memory_checkpoint():
        if cache is not None:
            cache.clear()
        certificate_domain.cache_clear()
        gc.collect()
        checkpoint()
        print("Numerical memory allocation failed; open node retained in the checkpoint",flush=True)

    while queue and tried < nodes:
        if tried and tried % 100 == 0:
            checkpoint()
            print(f"nodes={tried} excluded={excluded} local={local} queued={len(queue)}",flush=True)
        node, bounds = queue.popleft()
        tried += 1
        dist = closure(bounds,boundary)
        if dist is None:
            proof = {"cycle": True}
        else:
            lo, hi = dist[0], [-r[0] for r in dist]
            if box is not None and all(a >= l and b <= h for a,b,l,h in zip(lo,hi,*box)):
                node.clear()
                node["local"] = True
                local += 1
                continue
            seeds = ()
            if cache:
                center = center_of(dist)
                closest = sorted(cache,key=lambda entry: sum((x-y)**2 for x,y in zip(entry[0],center)))[:3]
                seeds = [p for _,p in closest]
            mean = mean_gauge(dist) if use_mean else None
            try:
                proof = proposal(graph,bounds,trial,refine,seeds,mean,boundary=boundary,cap=cap)
            except MemoryError:
                memory_checkpoint()
                break
        if proof is not None:
            node.clear()
            node["exclusion"] = proof
            excluded += 1
            if reuse and "flows" in proof:
                cache.append((center_of(dist),proof))
        else:
            try:
                cut = tighten(graph,bounds,trial,lo,hi,mean,boundary=boundary,cap=cap,seeds=seeds) if tighten_bounds else None
            except MemoryError:
                memory_checkpoint()
                break
            if cut is not None:
                j,m,sign,proof = cut
                child, removed = {"open":True}, {"exclusion":proof}
                low, high = (removed,child) if sign > 0 else (child,removed)
                node.clear()
                node.update(split=[j,m],lower=low,upper=high)
                queue.appendleft((child,bounds+[(0,j,m) if sign > 0 else (j,0,-m)]))
                if reuse and "flows" in proof:
                    rejected = closure(bounds+[(j,0,-m) if sign > 0 else (0,j,m)],boundary)
                    cache.append((center_of(rejected),proof))
                excluded += 1
                continue
            overlap = box is not None and all(a <= h and b >= l for a,b,l,h in zip(lo,hi,*box))
            i = 0
            j = max(range(1,boundary),key=lambda k: hi[k]-lo[k])
            if relative and not overlap:
                i,j = balanced_split(dist,mean)
            a,b = dist[i][j],-dist[j][i]
            m = (a+b)//2
            if i == 0 and b-a < 150000 and overlap:
                stops = [t for t in (box[0][j],box[1][j]) if lo[j]+2 < t < hi[j]-2]
                if stops:
                    m = min(stops,key=lambda t: abs(t-m))
            if a < m < b:
                node.clear()
                low, high = {"open":True}, {"open":True}
                node.update(split=[i,j,m],lower=low,upper=high)
                queue.append((low,bounds+[(j,i,-m)]))
                queue.append((high,bounds+[(i,j,m)]))
    print(f"nodes={tried} excluded={excluded} local={local} queued={len(queue)}",flush=True)
    return root


def search_partition(data,nodes,output,tighten_bounds=False,root=None,refine=False,reuse=False,
                     relative=False,carve=False,halfturn=False,use_mean=False):
    graph,edges,trial = partition_domain(data)
    targets(data)
    if halfturn:
        edges.append(halfturn_cut(data))
    root = {"open":True} if root is None else root
    if carve:
        carve_local(root,edges,data)
    return search_domains(root,graph,edges,trial,nodes,lambda:save(root,output),
                          tighten_bounds=tighten_bounds,refine=refine,reuse=reuse,
                          relative=relative,use_mean=use_mean,box=(data["lo"],data["hi"]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nodes",type=int,default=2000)
    parser.add_argument("--tighten",action="store_true")
    parser.add_argument("--refine-angle",action="store_true")
    parser.add_argument("--reuse",action="store_true")
    parser.add_argument("--relative",action="store_true")
    parser.add_argument("--carve-local",action="store_true")
    parser.add_argument("--halfturn",action="store_true")
    parser.add_argument("--mean-gauge",action="store_true")
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--resume",type=Path)
    args = parser.parse_args()
    data = json.loads((ROOT/"candidate_b16_cell.json").read_text(encoding="utf-8"))
    root = json.loads(args.resume.read_text(encoding="utf-8")) if args.resume else None
    tree = search_partition(data,args.nodes,args.out,args.tighten,root,args.refine_angle,
                            args.reuse,args.relative,args.carve_local,args.halfturn,args.mean_gauge)
    save(tree,args.out)


if __name__ == "__main__":
    main()
