"""Exact whole-belt angular certificates using linearized vector-flow cuts."""

import argparse
import json
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from pathlib import Path

from rational_trig import pi_bounds
from verify_belt_pruning import B, SCALE, constraints, cut_table, parse_belt, window_edges
from verify_fan import require
from verify_patch14 import ARC_CAP, RADIUS, terminals, total_deficit_upper, trig_bounds, trig_dot_lower
from verify_template import Interval


def graph_from_faces(sites, faces, origin=None, boundary=B):
    free = sites + len(faces)
    edges = [(u, sites + j) for j, face in enumerate(faces) for u in face]
    edges.extend((i, free + (i + j) % boundary) for i in range(boundary) for j in range(2))
    if origin is not None:
        edges.append((origin, free + boundary))
    return sites, faces, free, edges


def build_graph(paths, more_faces=(), inner_count=None, origin=None):
    h = 1 + max(x for p in paths for x in p)
    sites = B + (h if inner_count is None else inner_count)
    faces = [(i, (i + 1) % B, B + p[-1]) for i, p in enumerate(paths)]
    faces.extend((i, B + u, B + v) for i, p in enumerate(paths) for u, v in zip(p, p[1:]))
    faces.extend(tuple(B + x for x in face) for face in more_faces)
    return graph_from_faces(sites, faces, origin)


def starting_constraints(paths, cuts, windows=False):
    q = total_deficit_upper() * SCALE
    edges = constraints(paths, cuts, -((-q.numerator) // q.denominator))
    return edges + window_edges() if windows else edges


def closure(edges, boundary=B):
    return closed_differences(tuple(edges),boundary)


@lru_cache(maxsize=512)
def closed_differences(edges, boundary):
    dist = [[None] * boundary for _ in range(boundary)]
    for i in range(boundary):
        dist[i][i] = 0
    for i, j, w in edges:
        if dist[i][j] is None or w > dist[i][j]:
            dist[i][j] = w
    for k in range(boundary):
        via = dist[k]
        for row in dist:
            start = row[k]
            if start is None:
                continue
            for j,end in enumerate(via):
                if end is not None:
                    w = start+end
                    if row[j] is None or w > row[j]:
                        row[j] = w
        if any(dist[i][i] > 0 for i in range(boundary)):
            return None
    return tuple(map(tuple,dist))


def domain(dist):
    boundary = len(dist)
    lo = [Q(x, SCALE) for x in dist[0]]
    hi = [Q(-row[0], SCALE) for row in dist]
    rows = []
    for i in range(boundary):
        for j in range(boundary):
            if i != j:
                row = [Q(0)] * boundary
                row[i], row[j] = Q(1), Q(-1)
                rows.append((row, Q(-dist[i][j], SCALE)))
    return lo, hi, rows


def full_dot_lower(vec, angle):
    # Reduce angles with an exact allowance for the uncertainty in pi.
    pi0, pi1 = pi_bounds()
    if abs(angle) > Q("3.5"):
        reduced = angle - 2 * pi0 if angle > 0 else angle + 2 * pi0
        return trig_dot_lower(vec, reduced) - sum(map(abs, vec)) * 2 * (pi1 - pi0)
    return trig_dot_lower(vec, angle)


@lru_cache(maxsize=8192)
def rounded_trig(angle):
    pi0, pi1 = pi_bounds()
    error = Q(0)
    if abs(angle) > Q("3.5"):
        angle += -2 * pi0 if angle > 0 else 2 * pi0
        error = 2 * (pi1 - pi0)
    c0, c1, s0, s1 = trig_bounds(angle)
    scale = 10**15

    def down(x):
        a = (x - error) * scale
        return a.numerator // a.denominator

    def up(x):
        a = (x + error) * scale
        return -((-a.numerator) // a.denominator)

    return down(c0), up(c1), down(s0), up(s1), scale


def rounded_dot_lower(vec, angle):
    x, y = vec
    c0, c1, s0, s1, scale = rounded_trig(angle)
    return Q(x * (c0 if x >= 0 else c1) + y * (s0 if y >= 0 else s1), scale)


def gauge_weights(anchor, boundary):
    if type(anchor) is int:
        require(0 <= anchor < boundary, "Invalid seam anchor")
        return [int(j == anchor) for j in range(boundary)]
    require(isinstance(anchor, list) and len(anchor) == boundary
            and all(type(w) is int and w >= 0 for w in anchor) and any(anchor),
            "Invalid mean-gauge weights")
    total = sum(anchor)
    return [Q(w,total) for w in anchor]


def flow_affine(flow, graph, lo, hi, origin_cap=None, rounded=False, *, anchor=0, dist=None, radius=RADIUS):
    _, _, free, edges = graph
    end, cost = graph_terminals(flow, free, edges, origin_cap, len(lo), radius)
    dot = rounded_dot_lower if rounded else full_dot_lower
    offset = 0
    weights = None
    if type(anchor) is int and anchor:
        lo = [Q(x, SCALE) for x in dist[anchor]]
        hi = [Q(-row[anchor], SCALE) for row in dist]
        offset = anchor
    elif type(anchor) is not int:
        weights = gauge_weights(anchor,len(lo))
        offset = sum(j*w for j,w in enumerate(weights))
        lo = [sum(w*dist[i][j] for i,w in enumerate(weights))/SCALE for j in range(len(lo))]
        hi = [-sum(w*dist[j][i] for i,w in enumerate(weights))/SCALE for j in range(len(hi))]
    coef, constant = [], Q(0)
    for j, (v, a, b) in enumerate(zip(end, lo, hi)):
        nominal = (j - offset) * ARC_CAP
        left = dot(v, nominal - a)
        if a == b:
            constant += left
            coef.append(Q(0))
            continue
        right = dot(v, nominal - b)
        slope = (right - left) / (b - a)
        bound = dot(v, nominal - (a + b) / 2) - sum(map(abs, v)) * (b - a) / 2
        curvature_loss = max(Q(0), -bound) * (b - a)**2 / 8
        constant += left - slope * a - curvature_loss
        coef.append(slope / cost)
    if weights is not None:
        total = sum(coef)
        coef = [c-w*total for c,w in zip(coef,weights)]
    elif anchor:
        coef[anchor] -= sum(coef)
    return coef, radius - constant / cost


def graph_terminals(flow, free, edges, origin_cap, boundary=B, radius=RADIUS):
    if origin_cap is None:
        return terminals(flow, free, boundary - 1, edges)
    require(edges[-1][1] == free + boundary and 0 < origin_cap <= radius, "Invalid origin edge")
    return terminals(flow, free, boundary, edges, origin_cap / radius)


@lru_cache(maxsize=128)
def reduced_energy(edges, weights, free, count, rounded=False):
    neighbors = [{} for _ in range(count)]

    def add(u, v, weight):
        new = neighbors[u].get(v, 0) + weight
        neighbors[u][v] = neighbors[v][u] = new

    for (u, v), weight in zip(edges, weights):
        if weight:
            add(u, v, Interval(weight) if rounded else Q(weight))
    pending = set(range(free))
    while pending:
        u = min(pending, key=lambda j: (len(neighbors[j]), j))
        pending.remove(u)
        row = neighbors[u]
        total = sum(row.values())
        for (v, a), (w, b) in combinations(row.items(), 2):
            add(v, w, a*b/total)
        for v in row:
            del neighbors[v][u]
    scale = Interval(1).lo
    return [(u-free, v-free, Q(w.lo,scale) if rounded else w) for u in range(free, count)
            for v, w in neighbors[u].items() if u < v]


def energy_affine(proof, graph, dist, origin_cap, radius=RADIUS, rounded=True):
    _, _, free, edges = graph
    weights, prefix = proof["weights"], proof["prefix"]
    b = len(dist)
    require(len(weights) == len(edges) and all(type(w) is int and w >= 0 for w in weights)
            and any(weights), "Invalid energy weights")
    require(len(prefix) == b and all(type(x) is int for x in prefix), "Invalid tangent point")
    denom = radius**2 * sum(weights)
    if origin_cap is not None:
        denom += (origin_cap**2 - radius**2) * weights[-1]
    require(denom > 0, "Nonpositive energy budget")
    coef, constant = [Q(0)] * b, Q(0)
    key = (tuple(edges),tuple(weights),free,free+b+int(origin_cap is not None))
    try:
        pairs = reduced_energy(*key,rounded)
    except ValueError:
        pairs = reduced_energy(*key,False)
    for i,j,w in pairs:
        if j == b:  # The fixed origin is at squared distance one from every seam.
            constant += w
            continue
        a, z = Q(dist[i][j], SCALE), Q(-dist[j][i], SCALE)
        nominal = (j-i)*ARC_CAP

        def circle(t):
            c0, c1, s0, s1, scale = rounded_trig(nominal-t)
            return Q(c0,scale), Q(c1,scale), Q(s0,scale), Q(s1,scale)

        mid0, mid1, _, _ = circle((a+z)/2)
        if a == z:
            constant += w * (2-2*mid1)
            continue
        if mid0 >= (z-a)/2:
            # The pair energy is convex here, so use a supporting tangent.
            t = max(a, min(z, Q(prefix[j]-prefix[i], SCALE)))
            _, c1, s0, s1 = circle(t)
            slope = -(s0+s1)
            intercept = 2-2*c1 - slope*t - (s1-s0)*max(z-t,t-a)
        else:
            # Subtract the interpolation error where the curvature can be positive.
            left, right = (2-2*circle(t)[1] for t in (a,z))
            slope = (right-left)/(z-a)
            intercept = left-slope*a-max(0,2*mid1+z-a)*(z-a)**2/8
        coef[i] -= w*slope
        coef[j] += w*slope
        constant += w*intercept
    return [c/denom for c in coef], 1-constant/denom


def combination_margin(rows, multipliers, lo, hi):
    a, b = [Q(0)] * len(lo), Q(0)
    for index, weight in multipliers:
        w = Q(weight)
        require(type(index) is int and 0 <= index < len(rows) and w > 0,
                "Invalid multiplier")
        c, d = rows[index]
        a = [x + w * y for x, y in zip(a, c)]
        b += w * d
    return sum(x * (l if x >= 0 else h) for x, l, h in zip(a, lo, hi)) - b


def certificate_margin(dist, rows, multipliers, lo, hi):
    boundary = len(dist)
    nbase = boundary*(boundary-1)
    a, b = [Q(0)]*boundary,Q(0)
    for index,weight in multipliers:
        w = Q(weight)
        require(type(index) is int and 0 <= index < nbase+len(rows) and w > 0,"Invalid multiplier")
        if index < nbase:
            i,j = divmod(index,boundary-1)
            j += j >= i
            a[i] += w
            a[j] -= w
            b -= w*Q(dist[i][j],SCALE)
        else:
            c,d = rows[index-nbase]
            a = [x+w*y for x,y in zip(a,c)]
            b += w*d
    return sum(x*(l if x >= 0 else h) for x,l,h in zip(a,lo,hi))-b


@lru_cache(maxsize=32)
def certificate_domain(edges, boundary=B):
    dist = closure(edges, boundary)
    return (dist, *domain(dist)) if dist is not None else (None, None, None, None)


def split_edges(split, boundary):
    require(isinstance(split,list) and len(split) in (2,3), "Invalid angular split")
    i,j,m = (0,*split) if len(split) == 2 else split
    require(all(type(x) is int for x in (i,j,m)) and 0 <= i < j < boundary, "Invalid angular split")
    return i,j,m,(j,i,-m),(i,j,m)


def verify_tree(tree, graph, edges, origin_cap=None, boundary=B, *, radius=RADIUS):
    dist = closure(edges,boundary)
    if dist is None:
        require(tree.get("cycle") is True, "Expected a positive-cycle leaf")
        return 1
    if "split" in tree:
        i,j,m,low,high = split_edges(tree["split"],boundary)
        require(dist[i][j] < m < -dist[j][i], "Angular split outside its domain")
        return (
            verify_tree(tree["lower"],graph,edges+[low],origin_cap,boundary,radius=radius)
            + verify_tree(tree["upper"],graph,edges+[high],origin_cap,boundary,radius=radius)
        )
    lo = [Q(x,SCALE) for x in dist[0]]
    hi = [Q(-row[0],SCALE) for row in dist]
    flows = tree["flows"]
    anchors = tree.get("anchors", [0] * len(flows))
    require(len(anchors) == len(flows), "Invalid flow anchors")
    for anchor in anchors:
        gauge_weights(anchor,boundary)
    for rounded in (True, False):
        energies = [energy_affine(e,graph,dist,origin_cap,radius,rounded) for e in tree.get("energies",[])]
        rows = [flow_affine(f,graph,lo,hi,origin_cap,rounded,anchor=j,dist=dist,radius=radius)
                for f,j in zip(flows,anchors)] + energies
        if certificate_margin(dist,rows,tree["multipliers"],lo,hi) > 0:
            return 1
    raise ValueError("The linear combination did not prove infeasibility")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("belts", type=Path)
    parser.add_argument("patch_cuts", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--remaining", type=Path)
    args = parser.parse_args()
    cuts = cut_table(json.loads(args.patch_cuts.read_text(encoding="utf-8")))
    rows = args.belts.read_text(encoding="utf-8").splitlines()
    proofs = json.loads(args.certificate.read_text(encoding="utf-8"))
    excluded = set()
    counts = Counter()
    leaves = 0
    for proof in proofs:
        i = proof["index"]
        require(type(i) is int and 0 <= i < len(rows) and i not in excluded
                and proof["belt"] == rows[i], "Missing, duplicate or changed belt")
        meta, paths = parse_belt(rows[i])
        graph = build_graph(paths)
        leaves += verify_tree(proof["tree"], graph,
                              starting_constraints(paths, cuts, proof.get("windows", False)))
        excluded.add(i)
        counts[meta[:2]] += 1
    require(bool(excluded), "Empty whole-belt certificate")
    if args.remaining:
        args.remaining.write_text("".join(s + "\n" for i, s in enumerate(rows) if i not in excluded),
                                  encoding="utf-8")
    print(f"PASS whole-belt exclusions={len(excluded)}, leaves={leaves}, "
          f"remaining={len(rows)-len(excluded)}")
    for (a, h), count in sorted(counts.items()):
        print(f"apices={a}, layer={h}, excluded={count}")


if __name__ == "__main__":
    main()
