"""Bind the seam-neighborhood theorem to a labeled candidate fill and angular box."""

import argparse
import json
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

from rational_trig import pi_bounds, sqrt_bounds
from refine_template import dot, sub
from verify_belt_geometry import closure, graph_from_faces, rounded_trig, split_edges, verify_tree
from verify_belt_pruning import SCALE
from verify_candidate_seams import SEAM_NEIGHBORHOOD, lower, upper, verify
from verify_local import I, circumcenter, cross, norm2, template_configuration, transform
from verify_patch14 import ARC_CAP, RADIUS
from verify_fan import require
from verify_shell_fills import orbit_key, parse_fill, shell_symmetries
from verify_shells import angles, parse_shell
from verify_outer_windows import model_windows
from verify_template import certified_trial_radius


ROOT = Path(__file__).resolve().parent


def template_triangles():
    quad = ((0,1,16), (1,2,17), (2,3,17), (3,4,18), (1,17,16), (3,18,17), (16,17,24), (17,18,24))
    for sx, sy in ((1,1),(-1,1),(-1,-1),(1,-1)):
        for f in quad:
            yield tuple(transform(u,sx,sy) for u in f)
    yield (18,25,24)
    yield (22,24,25)


def seam_order(data):
    perm,sign = data["labeling"],data["sign"]
    order = [None]*16
    for i in range(16):
        j = perm[(i+1)%16] if sign == 1 else perm[i]
        order[j] = i
    return order


def targets(data):
    b, n = 16, 26
    _, outer, _ = parse_shell(data["shell"], n, b)
    _, inner = parse_fill(data["fill"], n, b)
    sites, seams, _ = template_configuration()
    perm, shift, sign = data["labeling"], data["shift"], data["sign"]
    require(len(perm) == len(sites) and sorted(perm) == list(range(n)) and sign in (-1,1)
            and all(perm[i] == (shift+sign*i)%b for i in range(b)), "Invalid site relabeling")
    have = {tuple(sorted(f)) for f in outer+inner}
    want = {tuple(sorted(perm[u] for u in tri)) for tri in template_triangles()}
    require(len(have) == len(outer)+len(inner) == 34 and have == want,
            "The filling differs from the 34-triangle candidate")
    ordered = [seams[i] for i in seam_order(data)]
    first = ordered[0]
    return [(dot(first,y), sign*cross(first,y)) for y in ordered]


def equivalent_fills(data, shells, lines):
    h, outer, _ = parse_shell(data["shell"],26,16)
    _, inner = parse_fill(data["fill"],26,16)
    require(h == 8 and lines, "Unexpected candidate first layer or empty fill set")
    maps = shell_symmetries(outer,26,16,h)
    want = orbit_key(inner,maps)
    for line in lines:
        i, fs = parse_fill(line,26,16)
        require(0 <= i < len(shells) and shells[i] == data["shell"], "Fill has a different exterior shell")
        require(orbit_key(fs,maps) == want, "Residual fill is not isomorphic to the candidate")
    return len(lines)


def trial_radius():
    trial = certified_trial_radius()
    require(trial <= RADIUS, "Invalid candidate exclusion radius")
    return trial


def check_candidate_edges(trial):
    sites, seams, _ = template_configuration()
    for f in template_triangles():
        points = [sites[u] for u in f]
        z = circumcenter(*points)
        d = [norm2(sub(z,p)) for p in sites]
        r2 = max(upper(d[u]) for u in f)
        require(r2 < trial**2 and upper(norm2(z)) < 1, "Candidate triangle does not fit")
        require(all(lower(x) > r2 for u,x in enumerate(d) if u not in f),
                "The candidate triangle is not a strict Voronoi vertex")
    for i,y in enumerate(seams):
        require(all(upper(norm2(sub(y,sites[u]))) < trial**2 for u in (i,(i+1)%16)),
                "Candidate seam does not fit")


def certify_box(lo, hi, target):
    require(len(lo) == len(hi) == len(target) and lo[0] == hi[0] == 0,
            "Wrong angle box dimension or gauge")
    for j, (a,z,y) in enumerate(zip(lo,hi,target)):
        require(type(a) is int and type(z) is int and a <= z, "Invalid angle box")
        theta = j*ARC_CAP - Q(a+z,2*SCALE)
        c0,c1,s0,s1,scale = rounded_trig(theta)
        dx = I(Q(c0,scale), Q(c1,scale)) - y[0]
        dy = I(Q(s0,scale), Q(s1,scale)) - y[1]
        _, distance = sqrt_bounds(upper(norm2((dx,dy))))
        require(distance + Q(z-a,2*SCALE) <= SEAM_NEIGHBORHOOD,
                f"Seam {j} may lie outside the proved neighborhood")


def candidate_prefix_bounds(data, target):
    lower, higher = [Q(0)], [Q(0)]
    for j in range(1,16):
        def cross_at(u):
            c0,c1,s0,s1,scale = rounded_trig(j*ARC_CAP-u/SCALE)
            return cross((I(Q(c0,scale),Q(c1,scale)), I(Q(s0,scale),Q(s1,scale))), target[j])

        a,z = Q(data["lo"][j]),Q(data["hi"][j])
        require(cross_at(a).hi < 0 and cross_at(z).lo > 0, "Candidate angle is not bracketed")
        # certify_box has already placed the whole bracket in the same local arc.
        while z-a > Q(".02"):
            m = (a+z)/2
            check = cross_at(m)
            if check.hi < 0:
                a = m
            elif check.lo > 0:
                z = m
            else:
                a,z = m-Q(".01"),m+Q(".01")
                require(cross_at(a).hi < 0 and cross_at(z).lo > 0, "Need sharper trigonometric bounds")
                break
        lower.append(a)
        higher.append(z)
    return lower,higher


def partition_domain(data):
    _, outer, _ = parse_shell(data["shell"],26,16)
    _, inner = parse_fill(data["fill"],26,16)
    windows = model_windows(ROOT/"outer_windows.json",26,16)
    graph = graph_from_faces(26,outer+inner,boundary=16)
    return graph, angles(16,26,outer+inner,windows), trial_radius()


def halfturn_cut(data):
    h, outer, _ = parse_shell(data["shell"],26,16)
    _, inner = parse_fill(data["fill"],26,16)
    faces = {tuple(sorted(t)) for t in inner}
    for mapping in shell_symmetries(outer,26,16,h):
        if all(mapping[j] == (j+8)%16 for j in range(16)):
            if {tuple(sorted(mapping[u] for u in t)) for t in inner} == faces:
                q = SCALE*(8*ARC_CAP-pi_bounds()[1])
                return 0,8,q.numerator//q.denominator
    raise ValueError("The entire filling must admit the half-turn relabeling")


def split_data(split):
    return split_edges(split,16)


def replay_partition(tree, graph, edges, trial, target=None, *, boundary=16, cap=None):
    if "exclusion" in tree:
        return Counter(excluded=verify_tree(tree["exclusion"],graph,edges,cap,boundary,radius=trial))
    dist = closure(edges,boundary)
    require(dist is not None, "Use a cycle certificate for an empty domain")
    lo, hi = dist[0], [-r[0] for r in dist]
    if tree.get("local") is True:
        require(target is not None, "Local candidate theorem is unavailable in this domain")
        certify_box(lo,hi,target)
        return Counter(local=1)
    if tree.get("open") is True:
        return Counter(open=1)
    i,j,m,lower_cut,upper_cut = split_edges(tree["split"],boundary)
    require(dist[i][j] < m < -dist[j][i],"Candidate partition split lies outside its domain")
    return (replay_partition(tree["lower"],graph,edges+[lower_cut],trial,target,boundary=boundary,cap=cap)
            + replay_partition(tree["upper"],graph,edges+[upper_cut],trial,target,boundary=boundary,cap=cap))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, nargs="?", default=ROOT/"candidate_b16_cell.json")
    parser.add_argument("--partition", type=Path)
    parser.add_argument("--halfturn", action="store_true")
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--shells", type=Path)
    parser.add_argument("--fills", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text(encoding="utf-8"))
    target = targets(data)
    verify(seam_order(data)[0])
    check_candidate_edges(trial_radius())
    certify_box(data["lo"], data["hi"], target)
    graph, edges, trial = partition_domain(data)
    lo, hi = candidate_prefix_bounds(data,target)
    require(all(lo[j]-hi[i] >= w for i,j,w in edges), "Candidate does not satisfy the starting angular bounds")
    print("PASS labeled candidate filling and its closed prefix box")
    if args.shells or args.fills:
        require(args.shells is not None and args.fills is not None, "Both residual inputs are required")
        shells = args.shells.read_text(encoding="utf-8").splitlines()
        lines = args.fills.read_text(encoding="utf-8").splitlines()
        count = equivalent_fills(data,shells,lines)
        print(f"PASS {count} residual fills are isomorphic to the candidate")
    if args.partition:
        tree = json.loads(args.partition.read_text(encoding="utf-8"))
        if args.halfturn:
            edges.append(halfturn_cut(data))
        result = replay_partition(tree,graph,edges,trial,target)
        print(f"PASS candidate partition: excluded={result['excluded']} local={result['local']} open={result['open']}")
        if args.require_complete:
            require(result["open"] == 0 and result["local"] > 0,
                    "Incomplete partition or lost feasible candidate")


if __name__ == "__main__":
    main()
