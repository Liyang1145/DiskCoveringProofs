"""Force certificates for the finite Voronoi face tables.

SciPy is used only to propose a force. Integer balance and outward interval
arithmetic independently check whether the force excludes the whole angle box.
"""

import argparse
import gzip
import json
from collections import Counter, deque
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import factorial
from pathlib import Path

from interval import Interval as I, PI, SCALE, asin
from topology import face_lists


GRID = 1 << 22
TRIAL = ".331732034277"


def representatives(n):
    seen = set()
    relabelings = list(permutations(range(n, 14)))
    for family, raw in face_lists(n):
        if n == 11 and family > 2:
            continue
        if n == 11 and family == 2:
            ears = [b for a, b, c in raw if max(a, b, c) < n]
            if (ears[0]-ears[1]) % n not in (2, n-2):
                continue
        faces = tuple(sorted(tuple(sorted(face)) for face in raw))
        if faces in seen:
            continue
        yield family, faces
        for sign in (1, -1):
            for shift in range(n):
                outer = tuple((sign*i+shift) % n for i in range(n))
                for inner in relabelings:
                    order = outer+inner
                    seen.add(tuple(sorted(tuple(sorted(order[v] for v in f)) for f in faces)))


def graph(n, faces):
    cuts = 14+len(faces)
    edges = [(i, 14+j) for j, face in enumerate(faces) for i in face]
    edges.extend((j, cuts+i) for i in range(n) for j in (i, (i+1) % n))
    return cuts, edges


def divergence(edges, forces, size):
    net = [[0, 0] for _ in range(size)]
    assert len(edges) == len(forces)
    for (a, b), (fx, fy) in zip(edges, forces):
        assert type(fx) is int and type(fy) is int
        net[a][0] += fx
        net[a][1] += fy
        net[b][0] -= fx
        net[b][1] -= fy
    return net


def balance(edges, forces, cuts, n):
    """Cancel the divergence at each nonboundary vertex along a spanning tree."""
    forces = [list(f) for f in forces]
    size = cuts+n
    adjacency = [[] for _ in range(size)]
    for e, (a, b) in enumerate(edges):
        adjacency[a].append((b, e, 1))
        adjacency[b].append((a, e, -1))
    parents = {cuts: None}
    queue = deque([cuts])
    while queue:
        a = queue.popleft()
        for b, e, sign in adjacency[a]:
            if b not in parents:
                parents[b] = (a, e, -sign)
                queue.append(b)
    assert len(parents) == size
    net = divergence(edges, forces, size)
    for v in reversed(parents):
        if v >= cuts:
            continue
        a, e, sign = parents[v]
        for k in range(2):
            residual = net[v][k]
            forces[e][k] -= sign*residual
            net[a][k] += residual
            net[v][k] = 0
    return forces


@lru_cache(maxsize=65536)
def unit_at(lo, hi):
    """Enclose a unit vector at an interval-enclosed real angle."""
    x = I.endpoints(lo, hi)
    half_pi = PI/2
    k = (x.lo+x.hi+half_pi.lo)//(2*half_pi.lo)
    y = x-k*half_pi
    assert -SCALE <= y.lo <= y.hi <= SCALE
    yy = y.square()
    c, s = I(1), y
    ct, st = c, s
    for j in range(1, 11):
        ct = -ct*yy/((2*j-1)*(2*j))
        st = -st*yy/((2*j)*(2*j+1))
        c += ct
        s += st
    # Taylor's theorem through degree 20 for cos and 21 for sin.
    err_c = Fraction(1, factorial(21))
    err_s = Fraction(1, factorial(22))
    c += I(-err_c, err_c)
    s += I(-err_s, err_s)
    return [(c, s), (-s, c), (-c, -s), (s, -c)][k % 4]


@lru_cache(maxsize=16)
def cap_data(n, rlo, rhi):
    cap = 2*asin(I.endpoints(rlo, rhi))
    return cap, n*cap-2*PI


def angle_box(n, r, box):
    cap, slack = cap_data(n, r.lo, r.hi)
    assert slack.lo > 0
    assert len(box) == n-1
    return [(I(0), I(0))]+[(i*cap-slack*hi, i*cap-slack*lo)
                           for i, (lo, hi) in enumerate(box, 1)]


@lru_cache(maxsize=16)
def order_rows(n, rlo, rhi):
    """Linear inequalities shared by all cut positions in cyclic order."""
    cap, slack = cap_data(n, rlo, rhi)
    assert max(cap.hi, slack.hi) < (PI/2).lo
    normals = []
    for i in range(n+1):
        angle = i*cap
        normals.append(unit_at(angle.lo, angle.hi))
    rows = []
    for i in range(n):
        j = (i+1) % n
        a, b = normals[i]
        c, d = normals[i+1]
        # sin(S[i+1]) >= sin(S[i]) and cos(S[i]) >= cos(S[i+1]).
        rows.append((i, -b, a, j, d, -c))
        rows.append((i, a, b, j, -c, -d))
        # sin(theta[i+1]-i*cap) >= sin(theta[i]-i*cap).
        rows.append((i, b, -a, j, -b, a))
    return rows


def force_margin(n, faces, r, box, certificate):
    """Positive result certifies infeasibility for every cut choice in box."""
    forces, order_force = certificate
    cuts, edges = graph(n, faces)
    net = divergence(edges, forces, cuts+n)
    assert all(f == [0, 0] for f in net[:cuts])
    length = sum(I(a*a+b*b).sqrt() for a, b in forces)
    normals = [[I(a), I(b)] for a, b in net[cuts:]]
    rows = order_rows(n, r.lo, r.hi)
    assert len(order_force) == len(rows)
    for w, (i, a, b, j, c, d) in zip(order_force, rows):
        assert type(w) is int and w >= 0
        if w:
            normals[i][0] -= w*a
            normals[i][1] -= w*b
            normals[j][0] -= w*c
            normals[j][1] -= w*d
    lower = normals[0][0].lo
    for (lo, hi), (a, b) in zip(angle_box(n, r, box)[1:], normals[1:]):
        if a.lo == a.hi == b.lo == b.hi == 0:
            continue
        assert hi.hi-lo.lo < PI.lo
        ux, uy = unit_at(lo.lo, lo.hi)
        vx, vy = unit_at(hi.lo, hi.hi)
        end = min((a*ux+b*uy).lo, (a*vx+b*vy).lo)
        # A positive minimum of the two endpoints is a lower bound on
        # the short arc, by positive sine interpolation. Otherwise use
        # the unconditional lower bound from Cauchy--Schwarz.
        lower += end if end >= 0 else -(a.square()+b.square()).sqrt().hi
    return lower-(r*length).hi


def caps_force(n, faces, r, box):
    """Solve a floating-point convex relaxation to propose balanced forces."""
    import numpy as np
    from scipy.optimize import minimize

    cuts, edges = graph(n, faces)
    size = cuts+n
    first, last = np.array(edges).T
    rows = np.arange(len(edges))
    angle = angle_box(n, r, box)
    lo = np.array([pair[0].lo/SCALE for pair in angle])
    hi = np.array([pair[1].hi/SCALE for pair in angle])
    middle = (lo+hi)/2
    normals = np.c_[np.cos(middle), np.sin(middle)]
    offsets = np.cos((hi-lo)/2)
    points = np.zeros((size, 2))
    points[cuts:] = normals
    points[:n] = .46*(normals+np.roll(normals, 1, axis=0))
    for i in range(n, 14):
        adjacent = sorted({j for face in faces if i in face for j in face if j < n})
        if adjacent:
            points[i] = .4*points[adjacent].mean(axis=0)
    for j, face in enumerate(faces):
        points[14+j] = points[list(face)].mean(axis=0)

    def loss(x):
        return x[-1]

    objective = np.r_[np.zeros(2*size), 1.]
    width = 2*size+1
    order = order_rows(n, r.lo, r.hi)
    planar = np.zeros((n-1+len(order), width))
    for i in range(1, n):
        planar[i-1, 2*(cuts+i):2*(cuts+i+1)] = normals[i]
    for k, (i, a, b, j, c, d) in enumerate(order, n-1):
        planar[k, 2*(cuts+i):2*(cuts+i+1)] += [a.lo/SCALE, b.lo/SCALE]
        planar[k, 2*(cuts+j):2*(cuts+j+1)] += [c.lo/SCALE, d.lo/SCALE]
    rhs = np.r_[offsets[1:], np.zeros(len(order))]

    def constraints(x):
        p = x[:-1].reshape((-1, 2))
        d = p[first]-p[last]
        return np.r_[x[-1]-np.sum(d*d, axis=1), planar@x-rhs]

    def jacobian(x):
        p = x[:-1].reshape((-1, 2))
        d = p[first]-p[last]
        j = np.zeros((len(edges)+len(planar), width))
        j[rows, -1] = 1
        for k in (0, 1):
            j[rows, 2*first+k] = -2*d[:, k]
            j[rows, 2*last+k] = 2*d[:, k]
        j[len(edges):] = planar
        return j

    bounds = [(None, None)]*width
    bounds[2*cuts:2*cuts+2] = [(1, 1), (0, 0)]
    bounds[-1] = (0, None)
    ans = minimize(loss, np.r_[points.ravel(), .5], jac=lambda x: objective,
                   constraints=[{'type': 'ineq', 'fun': constraints, 'jac': jacobian}],
                   bounds=bounds, method='SLSQP', options={'ftol': 2e-10, 'maxiter': 120})
    assert np.all(np.isfinite(ans.x))
    p = ans.x[:-1].reshape((-1, 2))
    stress = np.maximum(0, ans.multipliers[:len(edges)])
    forces = [[round(float(u)) for u in f]
              for f in 10**8 * stress[:, None]*(p[first]-p[last])]
    order_force = [round(float(w)) for w in 5*10**7*np.maximum(0, ans.multipliers[-len(order):])]
    cap_weights = np.maximum(0, ans.multipliers[len(edges):len(edges)+n-1])
    return ans.fun**.5, (balance(edges, forces, cuts, n), order_force), cap_weights


@lru_cache(maxsize=65536)
def grid_point(x):
    return I(Fraction(x, GRID))


def interval_box(box):
    return tuple((grid_point(a), grid_point(b)) for a, b in box)


def tighten(n, r, box):
    """Propagate nondecreasing cumulative deficits and their step bound."""
    cap, slack = cap_data(n, r.lo, r.hi)
    limit = ((cap/slack).hi*GRID+SCALE-1)//SCALE
    assert len(box) == n-1
    lo = [0]+[a for a, b in box]+[GRID]
    hi = [0]+[b for a, b in box]+[GRID]
    for i in range(1, n+1):
        lo[i] = max(lo[i], lo[i-1])
        hi[i] = min(hi[i], hi[i-1]+limit)
    for i in range(n-1, -1, -1):
        lo[i] = max(lo[i], lo[i+1]-limit)
        hi[i] = min(hi[i], hi[i+1])
    if any(a > b for a, b in zip(lo, hi)):
        return None
    return tuple(zip(lo[1:-1], hi[1:-1]))


def split_box(box, k, x):
    lo, hi = box[k]
    assert lo < x < hi
    return box[:k]+((lo, x),)+box[k+1:], box[:k]+((x, hi),)+box[k+1:]


def choose_split(n, r, box, cap_weights):
    scale = max(cap_weights)
    best = None
    for k, (lo, hi) in enumerate(box):
        if hi-lo < 2:
            continue
        x = (lo+hi)//2
        score = 0
        for raw in split_box(box, k, x):
            sub = tighten(n, r, raw)
            if sub:
                score += sum((b-a)**2 for a, b in sub)
        weight = cap_weights[k]/scale if scale else 0.
        merit = score/(1+.15*weight)
        if best is None or merit < best[0]:
            best = merit, k, x
    return None if best is None else best[1:]


def prove_tree(n, faces, r, budget, near=None):
    root = tuple((0, GRID) for _ in range(n-1))
    tried = 0
    todo = deque([(root, [])])
    root_record = todo[0][1]
    while todo and tried < budget:
        raw, record = todo.popleft()
        box = tighten(n, r, raw)
        if box is None:
            record.append("e")
            continue
        inside = interval_box(box)
        if near is not None and near(inside):
            record.append("n")
            continue
        tried += 1
        _, force, cap_weights = caps_force(n, faces, r, inside)
        if force_margin(n, faces, r, inside, force) > 0:
            record.extend(["f", *force])
            continue
        split = choose_split(n, r, box, cap_weights)
        if split is None:
            continue
        k, x = split
        left, right = [], []
        record.extend(["s", k, x, left, right])
        for child, branch in zip(split_box(box, k, x), (left, right)):
            todo.append((child, branch))
    return root_record, tried


def check_tree(n, faces, r, tree, near=None):
    root = tuple((0, GRID) for _ in range(n-1))
    todo = [(root, tree)]
    count = Counter()
    while todo:
        raw, node = todo.pop()
        box = tighten(n, r, raw)
        if not node:
            count["open"] += 1
        elif node[0] == "e":
            assert len(node) == 1 and box is None
            count["empty"] += 1
        elif node[0] == "f":
            assert len(node) == 3 and box is not None
            assert force_margin(n, faces, r, interval_box(box), node[1:]) > 0
            count["force"] += 1
        elif node[0] == "n":
            assert len(node) == 1 and box is not None
            assert near is not None and near(interval_box(box))
            count["near"] += 1
        else:
            assert len(node) == 5 and node[0] == "s" and box is not None
            _, k, x, left, right = node
            assert type(k) is type(x) is int and 0 <= k < n-1
            todo.extend(zip(split_box(box, k, x), (left, right)))
    return count


def prove_file(n, start, stop, budget, output):
    from neighborhood import near_checker

    r = I(TRIAL)
    cases = list(representatives(n))
    entries = []
    stop = len(cases) if stop is None else stop
    assert 0 <= start <= stop <= len(cases)
    for j in range(start, stop):
        family, faces = cases[j]
        near = near_checker(n, faces, r) if family == "quadrilateral" else None
        tree, tried = prove_tree(n, faces, r, budget, near)
        count = check_tree(n, faces, r, tree, near)
        entries.append([j, tree])
        if count["open"] or tried > 1 or j % 50 == 0:
            print(n, j, family, "solves", tried, dict(count), flush=True)
    with gzip.open(output, "wt", encoding="utf-8") as file:
        json.dump({"n": n, "r": TRIAL, "entries": entries}, file, separators=(",", ":"))


def check_files(paths, require_complete=False):
    from neighborhood import near_checker
    from upper import ROOT_R

    cases = {}
    covered = {}
    for path in paths:
        with gzip.open(path, "rt", encoding="utf-8") as file:
            payload = json.load(file)
        sections = payload if isinstance(payload, list) else [payload]
        for data in sections:
            n, r = data["n"], I(data["r"])
            assert type(n) is int and n in (10, 11)
            assert (r-ROOT_R).lo > 0 and r.hi <= I(".331733").lo
            if n not in cases:
                cases[n] = list(representatives(n))
            total = Counter()
            seen = set()
            for j, tree in data["entries"]:
                assert type(j) is int and 0 <= j < len(cases[n]) and j not in seen
                seen.add(j)
                family, faces = cases[n][j]
                near = near_checker(n, faces, r) if family == "quadrilateral" else None
                result = check_tree(n, faces, r, tree, near)
                total.update(result)
                if not result["open"]:
                    covered.setdefault(n, set()).add(j)
            if require_complete:
                assert not total["open"], (path, n, total)
            print(path, n, dict(total))
    if require_complete:
        assert set(cases) == {10, 11}
    for n, data in cases.items():
        done = covered.get(n, set())
        print(n, "excluded", len(done), "of", len(data), "by family",
              dict(Counter(data[j][0] for j in done)))
        remaining = sorted(set(range(len(data)))-done)
        print("Open representatives:", remaining)
        if require_complete:
            assert not remaining, (n, remaining)


def main():
    if not __debug__:
        raise RuntimeError("Run the certificate with assertions enabled.")
    cli = argparse.ArgumentParser(description=__doc__)
    sub = cli.add_subparsers(dest="mode", required=True)
    prove = sub.add_parser("prove")
    prove.add_argument("n", type=int, choices=(10, 11))
    prove.add_argument("file", type=Path)
    prove.add_argument("--start", type=int, default=0)
    prove.add_argument("--stop", type=int)
    prove.add_argument("--budget", type=int, default=1000)
    check = sub.add_parser("check")
    check.add_argument("--complete", action="store_true")
    check.add_argument("files", type=Path, nargs="+")
    args = cli.parse_args()
    if args.mode == "prove":
        prove_file(args.n, args.start, args.stop, args.budget, args.file)
    else:
        check_files(args.files, args.complete)


if __name__ == "__main__":
    main()
