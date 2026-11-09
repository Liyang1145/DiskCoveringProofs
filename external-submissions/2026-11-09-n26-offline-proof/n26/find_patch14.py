"""Generate patch-flow candidates offline. The acceptance check uses fractions."""

import argparse
import json
import os
from collections import deque
from fractions import Fraction as Q
from pathlib import Path

os.environ["OPENBLAS_NUM_THREADS"] = "1"

import numpy as np
from scipy.optimize import linprog, minimize

from verify_belt14 import RADIUS
from verify_patch14 import (
    ARC_CAP, angle_vertices, axes, cut_margin, flow_margin, flow_row, patch_graph, terminals,
)


def balance_flow(flow, free, vertices, edges):
    """Round to integers and route each free-node imbalance toward a terminal."""
    rows = [[int(round(float(x) * 10**10)) for x in v] for v in flow]
    net = [[0, 0] for _ in range(vertices)]
    adj = [[] for _ in range(vertices)]
    for i, ((u, v), xy) in enumerate(zip(edges, rows)):
        for j, x in enumerate(xy):
            net[u][j] -= x
            net[v][j] += x
        adj[u].append((v, i))
        adj[v].append((u, i))
    queue = deque(range(free, vertices))
    parent = {v: (-1, -1) for v in queue}
    order = []
    while queue:
        u = queue.popleft()
        order.append(u)
        for v, i in adj[u]:
            if v not in parent:
                parent[v] = (u, i)
                queue.append(v)
    if len(order) != vertices:
        raise ValueError("Disconnected patch")
    for u in reversed(order):
        if u >= free:
            continue
        v, i = parent[u]
        sign = 1 if edges[i][0] == u else -1
        for j, x in enumerate(net[u]):
            rows[i][j] += sign * x
            net[v][j] += x
    return rows


def generate_flow(blocks, extras, weights=None, caps=None):
    free, arcs, edges = patch_graph(blocks, extras)
    e = np.asarray(edges)
    u, v = e[:, 0], e[:, 1]
    r = float(RADIUS)
    a = float(ARC_CAP)
    w = np.ones(arcs) if weights is None else np.asarray(weights, dtype=float)
    theta_matrix = (np.arange(arcs)[None, :] < np.arange(arcs + 1)[:, None]).astype(float) - .5
    us = u < free
    vs = v < free
    ut, vt = ~us, ~vs
    rows = np.arange(len(edges))

    def positions(z):
        theta = theta_matrix @ z[-arcs:]
        return np.vstack([z[:-arcs].reshape(-1, 2), np.stack([np.cos(theta), np.sin(theta)], 1)])

    def constraints(z):
        x = positions(z)
        d = x[u] - x[v]
        return r * r - (d * d).sum(axis=1)

    def jacobian(z):
        x = positions(z)
        d = x[u] - x[v]
        j = np.zeros((len(edges), len(z)))
        for ids, sites, terms, sign in ((u, us, ut, -2), (v, vs, vt, 2)):
            j[rows[sites], 2 * ids[sites]] = sign * d[sites, 0]
            j[rows[sites], 2 * ids[sites] + 1] = sign * d[sites, 1]
            t = ids[terms] - free
            dy = np.stack([-x[ids[terms], 1], x[ids[terms], 0]], 1)
            j[rows[terms], 2 * free:] += sign * np.sum(
                d[terms] * dy, axis=1
            )[:, None] * theta_matrix[t]
        return j

    caps = np.full(arcs, a) if caps is None else np.asarray(caps, dtype=float)
    gaps = np.minimum(.4, caps)
    t = theta_matrix @ gaps
    y = np.stack([np.cos(t), np.sin(t)], 1)
    p = np.tile([.6, 0.], (free, 1))
    p[:arcs] = .94 * (y[:-1] + y[1:]) / 2
    p[arcs:arcs + len(blocks)] = .65 * y[np.cumsum([0, *blocks[:-1]]) + 1]
    # Each witness is initially the centroid of its triangle.
    for witness in range(arcs + len(blocks) + sum(extras), free):
        p[witness] = p[u[v == witness]].mean(axis=0)
    obj_jac = np.r_[np.zeros(2 * free), -w]
    res = minimize(lambda z: obj_jac @ z, np.r_[p.ravel(), gaps],
                   jac=lambda z: obj_jac, constraints=[{
                       "type": "ineq", "fun": constraints, "jac": jacobian,
                   }], bounds=[(None, None)] * (2 * free) + [(0, t) for t in caps],
                   method="SLSQP", options={"ftol": 1e-12, "maxiter": 1000})
    if not res.success:
        return None, None
    x = positions(res.x)
    flows = np.maximum(0, res.multipliers)[:, None] * (x[v] - x[u])
    return balance_flow(flows, free, free + arcs + 1, edges), float(w @ (a - res.x[-arcs:]))


def fixed_graph_flow(free, edges, terminals_xy, initial, last_ratio=1):
    e = np.asarray(edges)
    u, v = e[:, 0], e[:, 1]
    i = np.arange(len(e))
    radius_scale = np.ones(len(e))
    radius_scale[-1] = float(last_ratio)**2

    def positions(z):
        return np.vstack([z[:-1].reshape(-1, 2), terminals_xy])

    def constraints(z):
        x = positions(z)
        d = x[u] - x[v]
        return radius_scale * z[-1] - np.sum(d * d, axis=1)

    def jacobian(z):
        x = positions(z)
        d = x[u] - x[v]
        j = np.zeros((len(e), len(z)))
        j[:, -1] = radius_scale
        for node, sign in ((u, -2), (v, 2)):
            inside = node < free
            j[i[inside], 2 * node[inside]] = sign * d[inside, 0]
            j[i[inside], 2 * node[inside] + 1] = sign * d[inside, 1]
        return j

    res = minimize(lambda z: z[-1], np.r_[initial.ravel(), .3**2],
                   jac=lambda z: np.r_[np.zeros(2 * free), 1], constraints=[{
                       "type": "ineq", "fun": constraints, "jac": jacobian,
                   }], method="SLSQP", options={"ftol": 1e-13, "maxiter": 600})
    if not hasattr(res, "multipliers") or not np.all(np.isfinite(res.x)):
        return None, None
    x = positions(res.x)
    f = np.maximum(0, res.multipliers)[:, None] * (x[v] - x[u])
    if not np.all(np.isfinite(f)) or np.max(np.abs(f)) < 1e-12:
        return None, None
    q = np.max(np.sum((x[v] - x[u])**2, axis=1) / radius_scale)
    return balance_flow(f, free, free + len(terminals_xy), edges), q


def fixed_flow(blocks, extras, angles):
    free, arcs, edges = patch_graph(blocks, extras)
    e = np.asarray(edges)
    u, v = e[:, 0], e[:, 1]
    t = np.asarray(angles, dtype=float)
    y = np.stack([np.cos(t), np.sin(t)], axis=1)
    p = np.tile([.6, 0.], (free, 1))
    p[:arcs] = .94 * (y[:-1] + y[1:]) / 2
    p[arcs:arcs + len(blocks)] = .65 * y[np.cumsum([0, *blocks[:-1]]) + 1]
    for witness in range(arcs + len(blocks) + sum(extras), free):
        p[witness] = p[u[v == witness]].mean(axis=0)
    return fixed_graph_flow(free, edges, y, p)[0]


def mixed_cut(entry, deficit, weights):
    blocks, extras = entry["blocks"], entry["extras"]
    free, arcs, edges = patch_graph(blocks, extras)
    vertices = list(angle_vertices(weights or [Q(1)] * arcs, [
        [Q(0)] * arcs, *axes(arcs, deficit),
    ]))
    flows, rows, costs = [], [], []

    def add(flow):
        if flow is None or not any(x or y for x, y in flow):
            return False
        b, cost = terminals(flow, free, arcs, edges)
        flows.append(flow)
        costs.append(cost)
        rows.append(flow_row(b, cost, vertices))
        return True

    add(entry["flow"])
    for _ in range(arcs + 12):
        mat = np.array([[float(q / c) for q in row] for row, c in zip(rows, costs)])
        # Find a nonnegative combination with every vertex coefficient positive.
        dual = linprog(np.r_[np.zeros(len(flows)), -1],
                       A_ub=np.column_stack((-mat.T, np.ones(arcs + 1))),
                       b_ub=np.zeros(arcs + 1), A_eq=[np.r_[np.ones(len(flows)), 0]],
                       b_eq=[1], bounds=[(0, None)] * len(flows) + [(None, None)],
                       method="highs")
        if dual.success and dual.x[-1] > 0:
            mixture = []
            for f, cost, w in zip(flows, costs, dual.x[:-1]):
                coefficient = Q(round(w * 10**9), 10**9) / cost
                if coefficient > 0:
                    mixture.append([str(coefficient), f])
            candidate = {**entry, "deficit": str(deficit), "mixture": mixture}
            if cut_margin(candidate) > 0:
                return candidate
        # Find an angular point where the current affine cuts are weakest.
        primal = linprog(np.r_[np.zeros(arcs + 1), 1],
                         A_ub=np.column_stack((mat, -np.ones(len(flows)))),
                         b_ub=np.zeros(len(flows)), A_eq=[np.r_[np.ones(arcs + 1), 0]],
                         b_eq=[1], bounds=[(0, None)] * (arcs + 1) + [(None, None)],
                         method="highs")
        if not primal.success:
            return None
        point = primal.x[:-1] @ np.asarray(vertices, dtype=float)
        if not add(fixed_flow(blocks, extras, point)):
            return None
        if np.dot(np.asarray(rows[-1], dtype=float), primal.x[:-1]) <= 0:
            return None
    return None


def split_cut(entry, deficit, weights):
    blocks, extras = entry["blocks"], entry["extras"]
    free, arcs, edges = patch_graph(blocks, extras)
    w = [Q(1)] * arcs if weights is None else weights
    end, cost = terminals(entry["flow"], free, arcs, edges)

    def margin(d):
        return flow_margin(end, cost, list(angle_vertices(w, d)))

    for ratio in (Q(".51"), Q(".57"), Q(".64"), Q(".72")):
        threshold = ratio * deficit
        base = axes(arcs, threshold)
        tail = axes(arcs, deficit - threshold)
        central = [[Q(0)] * arcs, *base, *(
            [a+b for a, b in zip(x, y)]
            for i, x in enumerate(base) for j, y in enumerate(tail) if i != j
        )]
        if margin(central) <= 0:
            continue
        flows = []
        for i, x in enumerate(base):
            corner = [x, *([a+b for a, b in zip(x, y)] for y in tail)]
            if margin(corner) > 0:
                flows.append(entry["flow"])
                continue
            caps = [ARC_CAP] * arcs
            caps[i] -= threshold / w[i]
            flow, _ = generate_flow(blocks, extras, weights, caps)
            if flow is None:
                break
            b, size = terminals(flow, free, arcs, edges)
            if flow_margin(b, size, list(angle_vertices(w, corner))) <= 0:
                break
            flows.append(flow)
        if len(flows) == arcs:
            result = {**entry, "deficit": str(deficit), "threshold": str(threshold),
                      "corners": flows}
            if cut_margin(result) > 0:
                return result
    return None


def find_cut(blocks, extras, scale=100000, limit=Q(".35033"), weights=None):
    flow, deficit = generate_flow(blocks, extras, weights)
    if flow is None or deficit < 1 / scale:
        return None, deficit
    entry = {"blocks": list(blocks), "extras": list(extras), "flow": flow}
    if weights is not None:
        entry["weights"] = [str(x) for x in weights]
    lo, hi = 0, min(int(limit * scale), int(deficit * scale) + 1)
    if min(weights or [1]) < 1:
        hi = min(hi, int(ARC_CAP * min(weights) * scale))
    entry["deficit"] = str(Q(hi, scale))
    if cut_margin(entry) > 0:
        return entry, deficit
    if hi == int(limit * scale):
        proof = mixed_cut(entry, Q(hi, scale), weights)
        if proof is None:
            proof = split_cut(entry, Q(hi, scale), weights)
        if proof is not None:
            return proof, deficit
    while lo < hi:
        mid = (lo + hi + 1) // 2
        entry["deficit"] = str(Q(mid, scale))
        if cut_margin(entry) > 0:
            lo = mid
        else:
            hi = mid - 1
    if not lo:
        return None, deficit
    entry["deficit"] = str(Q(lo, scale))
    return entry, deficit


def direct_sequences(total):
    if total == 0:
        yield ()
    for width in (1, 2):
        if total >= width:
            for rest in direct_sequences(total - width):
                yield (width, *rest)


def direct_library():
    cuts, forbidden = [], set()
    limit = Q(".35033")
    for total in range(4, 14):
        for blocks in direct_sequences(total):
            if blocks > blocks[::-1] or blocks.count(2) < 2:
                continue
            if any(blocks[i:i + len(p)] == p for p in forbidden
                   for i in range(len(blocks) - len(p) + 1)):
                continue
            cut, _ = find_cut(blocks, (0,) * (len(blocks) - 1), limit=limit)
            if cut is not None:
                cuts.append(cut)
                if Q(cut["deficit"]) == limit:
                    forbidden.add(blocks)
                    forbidden.add(blocks[::-1])
                    print("Fully excluded patch", blocks, flush=True)
        print(f"Through {total} boundary edges: {len(cuts)} cuts", flush=True)
    return cuts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--blocks", type=int, nargs="+")
    modes.add_argument("--all-direct", action="store_true")
    parser.add_argument("--extras", type=int, nargs="+")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if args.all_direct:
        entries = direct_library()
        if args.out:
            args.out.write_text(json.dumps(entries, separators=(",", ":")) + "\n", encoding="utf-8")
        return
    cut, guess = find_cut(args.blocks, args.extras or [0] * (len(args.blocks) - 1))
    print(f"Numerical deficit {guess}, certified deficit {cut['deficit'] if cut else None}")
    if args.out and cut:
        args.out.write_text(json.dumps([cut], indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
