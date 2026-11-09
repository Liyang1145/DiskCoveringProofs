"""Find whole-belt exclusion trees. All accepted leaves are checked exactly."""

import argparse
import json
import os
import warnings
from pathlib import Path

os.environ["OPENBLAS_NUM_THREADS"] = "1"

import numpy as np
from scipy.optimize import OptimizeWarning, linprog, minimize

from find_patch14 import balance_flow, fixed_graph_flow
from verify_belt_geometry import (
    build_graph, certificate_domain, combination_margin, energy_affine, flow_affine, gauge_weights, graph_terminals,
    starting_constraints,
    verify_tree,
)
from verify_belt_pruning import B, SCALE, cut_table, parse_belt
from verify_patch14 import ARC_CAP, RADIUS


def initial_positions(graph, paths, y, boundary=B):
    sites, faces, free, _ = graph
    p = np.zeros((free, 2))
    p[:boundary] = .94 * (y + np.roll(y, -1, axis=0)) / 2
    if paths is None:
        profiles = [set() for _ in range(sites-boundary)]
        for face in faces:
            outer = [u for u in face if u < boundary]
            for u in face:
                if u >= boundary:
                    profiles[u-boundary].update(outer)
        profiles = [sorted(s) for s in profiles]
    else:
        profiles = [[i for i, path in enumerate(paths) if j in path]
                    for j in range(sites-boundary)]
    core = []
    for j, profile in enumerate(profiles, start=boundary):
        if profile:
            p[j] = .68 * p[profile].mean(axis=0)
        else:
            core.append(j)
    if core:
        t = np.arange(len(core)) * (2 * np.pi / len(core))
        p[core] = .12 * np.stack((np.cos(t), np.sin(t)), axis=1)
    for i, face in enumerate(faces):
        p[sites + i] = p[list(face)].mean(axis=0)
    return p


def graph_flow(graph, paths, prefix, origin_cap=None, boundary=B):
    _, _, free, edges = graph
    t = float(ARC_CAP) * np.arange(boundary) - prefix
    y = np.stack((np.cos(t), np.sin(t)), axis=1)
    p = initial_positions(graph, paths, y, boundary)
    if origin_cap is not None:
        return fixed_graph_flow(free, edges, np.vstack((y, [0., 0.])), p, origin_cap / RADIUS)
    return fixed_graph_flow(free, edges, y, p)


def free_angle_flow(graph, paths, origin_cap=None, boundary=B, *, with_prefix=False, angle_edges=None,
                    with_layout=False, warm_start=None):
    """Propose a flow using a nonlinear fit in which every seam may move."""
    _, _, free, edges = graph
    u, v = np.asarray(edges).T
    rows = np.arange(len(edges))
    angle_map = (np.arange(boundary)[None, :] < np.arange(boundary)[:, None]).astype(float)
    scale = np.ones(len(edges))
    if origin_cap is not None:
        angle_map = np.vstack((angle_map, np.zeros((1, boundary))))
        scale[-1] = float(origin_cap / RADIUS)**2

    def terminal_positions(gaps):
        t = angle_map @ gaps
        y = np.stack((np.cos(t), np.sin(t)), axis=1)
        if origin_cap is not None:
            y[-1] = 0
        return y

    def positions(x):
        return np.vstack((x[:2 * free].reshape(-1, 2), terminal_positions(x[-boundary-1:-1])))

    def con(x):
        p = positions(x)
        d = p[u] - p[v]
        return scale * x[-1] - np.sum(d*d, axis=1)

    def jac(x):
        p = positions(x)
        d = p[u] - p[v]
        result = np.zeros((len(edges), len(x)))
        result[:, -1] = scale
        for ids, sign in ((u, -2), (v, 2)):
            inside = ids < free
            outside = ~inside
            result[rows[inside], 2 * ids[inside]] = sign * d[inside, 0]
            result[rows[inside], 2 * ids[inside] + 1] = sign * d[inside, 1]
            j = ids[outside] - free
            result[rows[outside], 2 * free:-1] += sign * (
                -d[outside, 0] * p[ids[outside], 1] + d[outside, 1] * p[ids[outside], 0]
            )[:, None] * angle_map[j]
        return result

    gaps = np.full(boundary, 2 * np.pi / boundary)
    if angle_edges is not None:
        dist, _, _, _ = certificate_domain(tuple(angle_edges),boundary)
        if dist is None:
            return None
        prefix = np.mean([[d-row[0] for d in row] for row in dist],axis=0)/SCALE
        theta = float(ARC_CAP)*np.arange(boundary)-prefix
        gaps = np.diff(np.r_[theta,2*np.pi])
    initial_q = .25**2
    if warm_start is not None:
        prefix, warm_sites, initial_q = warm_start
        theta = float(ARC_CAP)*np.arange(boundary)-prefix
        gaps = np.diff(np.r_[theta,2*np.pi])
    p = initial_positions(graph, paths, terminal_positions(gaps)[:boundary], boundary)
    if warm_start is not None:
        p[:graph[0]] = warm_sites
        for i,face in enumerate(graph[1],start=graph[0]):
            p[i] = p[list(face)].mean(axis=0)
    equality = np.r_[np.zeros(2 * free), np.ones(boundary), 0]
    objective = np.r_[np.zeros(2 * free + boundary), 1]
    conditions = [{"type": "ineq", "fun": con, "jac": jac},
                  {"type": "eq", "fun": lambda x: equality @ x - 2*np.pi, "jac": lambda x: equality}]
    if angle_edges is not None:
        a = np.zeros((len(angle_edges),len(objective)))
        a[:,2*free:-1] = [angle_map[i]-angle_map[j] for i,j,_ in angle_edges]
        c = np.array([(j-i)*float(ARC_CAP)-w/SCALE for i,j,w in angle_edges])
        conditions.append({"type":"ineq", "fun": lambda x: a @ x + c, "jac":lambda x: a})
    fit = minimize(lambda x: x[-1], np.r_[p.ravel(), gaps, initial_q], jac=lambda x: objective,
                   constraints=conditions,
                   bounds=[(None, None)] * (2 * free) + [(0, float(ARC_CAP))] * boundary + [(0, None)],
                   method="SLSQP", options={"ftol": 1e-12, "maxiter": 600})
    if not hasattr(fit, "multipliers") or not np.all(np.isfinite(fit.x)):
        return None
    p = positions(fit.x)
    multipliers = np.maximum(0, fit.multipliers[1:1+len(edges)])
    f = multipliers[:, None] * (p[v] - p[u])
    if not np.all(np.isfinite(f)) or np.max(np.abs(f)) < 1e-12:
        return None
    flow = balance_flow(f, free, len(p), edges)
    if not with_prefix or flow is None:
        return flow
    prefix = float(ARC_CAP) * np.arange(boundary) - angle_map[:boundary] @ fit.x[-boundary-1:-1]
    result = flow, prefix, multipliers, float(fit.fun)
    return (*result,p[:graph[0]].tolist(),bool(fit.success)) if with_layout else result


def leaf(rows, flows, anchors, energies, nbase, marginals, lo, hi):
    # Drop unused flow rows, keeping the index mapping exact.
    weights = [[i, round(-m * 10**10)] for i, m in enumerate(marginals) if -m > 1e-9]
    weights = [(i, w) for i, w in weights if w > 0]
    if combination_margin(rows, weights, lo, hi) <= 0:
        return None
    selected, selected_anchors, selected_energy = [], [], []
    remapped = []
    for i, w in weights:
        if i >= nbase:
            remapped.append([nbase + len(selected) + len(selected_energy), w])
            j = i - nbase
            if j < len(flows):
                selected.append(flows[j])
                selected_anchors.append(anchors[j])
            else:
                selected_energy.append(energies[j - len(flows)])
        else:
            remapped.append([i, w])
    result = {"flows": selected, "multipliers": remapped}
    if any(selected_anchors):
        result["anchors"] = selected_anchors
    if selected_energy:
        result["energies"] = selected_energy
    return result


def search(graph, flow_at, edges, depth, inherited=(), origin_cap=None, boundary=B, *,
           anchors=None, energies=(), radius=RADIUS, adaptive_energy=False, mean_anchor=None):
    dist, lo, hi, base = certificate_domain(tuple(edges), boundary)
    if dist is None:
        return {"cycle": True}
    limits = [(float(a), float(b)) for a, b in zip(lo, hi)]
    flows = list(inherited)
    energies = list(energies)
    anchors = list(anchors) if anchors is not None else [0] * len(flows)
    mean = np.array(gauge_weights(mean_anchor,boundary),dtype=float) if mean_anchor else None
    rows = base + [flow_affine(f, graph, lo, hi, origin_cap, rounded=True, anchor=j, dist=dist, radius=radius)
                   for f, j in zip(flows, anchors)]
    rows += [energy_affine(e, graph, dist, origin_cap, radius) for e in energies]
    # Average feasible potentials obtained by rooting longest paths at each vertex.
    prefix = np.mean([[d - row[0] for d in row] for row in dist], axis=0) / SCALE
    last_flow = None
    for _ in range(18):
        if flows or energies:
            a = np.array([r for r, _ in rows], dtype=float)
            b = np.array([r for _, r in rows], dtype=float)
            aux = np.r_[np.zeros(len(base)), -np.ones(len(flows)+len(energies))]
            with warnings.catch_warnings():
                warnings.filterwarnings("ignore", "Unrecognized options detected", OptimizeWarning)
                opt = linprog(np.r_[np.zeros(boundary), 1], A_ub=np.column_stack((a, aux)), b_ub=b,
                              bounds=limits + [(None, None)], method="highs", options={"threads": 1})
            if not opt.success:
                return None
            if opt.fun > 0:
                proof = leaf(rows, flows, anchors, energies, len(base), opt.ineqlin.marginals, lo, hi)
                if proof is not None:
                    return proof
            prefix = opt.x[:-1]
            if adaptive_energy and energies and len(energies) < 8:
                candidate = {"weights": energies[0]["weights"], "prefix": [round(SCALE*x) for x in prefix]}
                a, b = energy_affine(candidate,graph,dist,origin_cap,radius)
                gain = np.dot(np.asarray(a,dtype=float),prefix)-float(b)
                if gain > opt.fun+1e-8:
                    energies.append(candidate)
                    rows.append((a,b))
                    continue
        last_flow, q = flow_at(prefix)
        if last_flow is None or q <= float(radius)**2 - 1e-8:
            return None
        flow, anchor = last_flow, 0
        a, b = flow_affine(flow,graph,lo,hi,origin_cap,rounded=True,radius=radius)
        gain = np.dot(np.asarray(a, dtype=float), prefix) - float(b)
        if mean is not None:
            angle = mean @ (float(ARC_CAP)*np.arange(boundary)-prefix)
            rotated = rotate_flow(last_flow,angle)
            c, d = flow_affine(rotated,graph,lo,hi,origin_cap,rounded=True,
                               anchor=mean_anchor,dist=dist,radius=radius)
            better = np.dot(np.asarray(c,dtype=float),prefix)-float(d)
            if better > gain:
                flow, anchor, a, b, gain = rotated, mean_anchor, c, d, better
        if (flows or energies) and gain <= opt.fun + 1e-8:
            break
        flows.append(flow)
        anchors.append(anchor)
        rows.insert(len(base)+len(flows)-1, (a, b))
    if depth <= 0 or last_flow is None:
        return None
    _, _, free, graph_edges = graph
    end, _ = graph_terminals(last_flow, free, graph_edges, origin_cap, boundary, radius)
    width = [-dist[j][0] - dist[0][j] for j in range(boundary)]
    candidates = [j for j in range(1, boundary) if width[j] >= 2]
    if not candidates:
        return None
    j = max(candidates, key=lambda j: width[j]**2 * (sum(map(abs, end[j])) + 1))
    middle = (dist[0][j] - dist[j][0]) // 2
    low = search(graph, flow_at, edges + [(j, 0, -middle)], depth - 1, flows, origin_cap, boundary,
                 anchors=anchors, energies=energies, radius=radius, adaptive_energy=adaptive_energy,mean_anchor=mean_anchor)
    if low is None:
        return None
    high = search(graph, flow_at, edges + [(0, j, middle)], depth - 1, flows, origin_cap, boundary,
                  anchors=anchors, energies=energies, radius=radius, adaptive_energy=adaptive_energy,mean_anchor=mean_anchor)
    if high is None:
        return None
    return {"split": [j, middle], "lower": low, "upper": high}


def rotate_flow(flow, angle):
    c, s = round(10**6*np.cos(angle)), round(10**6*np.sin(angle))
    return [[c*x+s*y,c*y-s*x] for x,y in flow]


def anchored_search(graph, edges, origin_cap, boundary, seed, depth, radius=RADIUS, mean_anchor=None):
    flow, prefix, multipliers, _ = seed
    energy = {"weights": [round(10**6 * w) for w in multipliers],
              "prefix": [round(SCALE * u) for u in prefix]}
    energies = (energy,) if any(energy["weights"]) else ()
    angles = float(ARC_CAP)*np.arange(boundary)-prefix
    adaptive = radius != RADIUS or mean_anchor is not None
    roots, roots_anchors = [flow],[0]
    if mean_anchor is not None:
        weights = np.array(gauge_weights(mean_anchor,boundary),dtype=float)
        roots.append(rotate_flow(flow,weights @ angles))
        roots_anchors.append(mean_anchor)
    root = search(graph,lambda _: (None,None),edges,0,roots,origin_cap,boundary,
                  anchors=roots_anchors,energies=energies,radius=radius,adaptive_energy=adaptive)
    if root is not None:
        return root
    # Integer rotation and scaling preserve balance at every free vertex.
    flows = roots + [rotate_flow(flow,angle) for angle in angles[1:]]
    return search(graph, lambda u: graph_flow(graph, None, u, origin_cap, boundary), edges, depth,
                  flows, origin_cap, boundary, anchors=roots_anchors+list(range(1,boundary)),
                  energies=energies,radius=radius,adaptive_energy=adaptive,mean_anchor=mean_anchor)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("belts", type=Path)
    parser.add_argument("patch_cuts", type=Path)
    parser.add_argument("--layer", type=int)
    parser.add_argument("--depth", type=int, default=3)
    parser.add_argument("--free-angle", action="store_true")
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int, default=1000000)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    cuts = cut_table(json.loads(args.patch_cuts.read_text(encoding="utf-8")))
    rows = args.belts.read_text(encoding="utf-8").splitlines()
    proofs = []
    tried = 0
    for i in range(args.start, min(args.stop, len(rows))):
        meta, paths = parse_belt(rows[i])
        if args.layer is not None and meta[1] != args.layer:
            continue
        tried += 1
        graph = build_graph(paths)
        edges = starting_constraints(paths, cuts)
        flow = free_angle_flow(graph, paths) if args.free_angle else None
        tree = search(graph, lambda u: graph_flow(graph, paths, u), edges, args.depth,
                      [flow] if flow is not None else ())
        if tree is not None:
            verify_tree(tree, graph, edges)
            proofs.append({"index": i, "belt": rows[i], "tree": tree})
            print(f"belt {i}, apices={meta[0]}, layer={meta[1]} proved", flush=True)
    args.out.write_text(json.dumps(proofs, separators=(",", ":")) + "\n", encoding="utf-8")
    print(f"tried={tried}, proved={len(proofs)}", flush=True)


if __name__ == "__main__":
    main()
