"""Exact replay and transfer on completed shells with 15 to 17 arcs."""

import argparse
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path

from rational_trig import cos_lower, sin_lower, sqrt_bounds
from verify_belt_geometry import graph_from_faces, verify_tree
from verify_fan import require
from verify_outer_windows import model_windows
from verify_patch14 import ARC_CAP, RADIUS
from verify_shells import angles, parse_shell
from verify_template import certified_trial_radius
from verify_transfer14 import face_mask, read_records, required_faces


def parse_fill(line, n, b):
    fields = line.rstrip().split("\t")
    index = int(fields[0])
    faces = [tuple(map(int, t.split(","))) for t in fields[1:]]
    require(all(len(f) == 3 and len(set(f)) == 3 and b <= min(f) <= max(f) < n
                for f in faces), "Invalid inner face")
    require(len(set(tuple(sorted(f)) for f in faces)) == len(faces), "Duplicate inner face")
    return index, faces


def mask(faces, b):
    return face_mask(tuple(u-b for u in f if u >= b) for f in faces)


def shell_links(faces, b):
    step = [{} for _ in range(b)]
    for f in faces:
        for j,u in enumerate(f):
            if u < b:
                require(f[(j+1)%3] not in step[u], "Repeated exterior link step")
                step[u][f[(j+1)%3]] = f[(j+2)%3]
    result = []
    for i,table in enumerate(step):
        chain = [(i+1)%b]
        while chain[-1] in table:
            nxt = table[chain[-1]]
            require(nxt not in chain, "Cyclic exterior link")
            chain.append(nxt)
        require(chain[-1] == (i-1)%b, "Incomplete exterior link")
        result.append(chain)
    return result


def shell_symmetries(outer, n, b, h):
    chain = shell_links(outer,b)
    first_layer = set(range(b+h))
    target = {tuple(sorted(f)) for f in outer}
    result = []
    for sign in (1,-1):
        for shift in range(b):
            names = {i:(shift+sign*i)%b for i in range(b)}
            good = True
            for i,p in enumerate(chain):
                q = chain[names[i]][::sign]
                if len(p) != len(q) or any(names.setdefault(u,v) != v for u,v in zip(p,q)):
                    good = False
                    break
            if good and set(names) == set(names.values()) == first_layer:
                require({tuple(sorted(names[u] for u in f)) for f in outer} == target,
                        "Exterior link map does not preserve all faces")
                for core in permutations(range(b+h,n)):
                    result.append(tuple(names[u] for u in range(b+h)) + core)
    require(bool(result), "Missing identity relabeling")
    return result


def orbit_key(inner, maps):
    return min(tuple(sorted(tuple(sorted(m[u] for u in t)) for t in inner)) for m in maps)


def origin_cap(n, b, h, windows):
    r = RADIUS
    require(r < Q(1, 4), "An outer neighbor could cover the origin")
    if h != n-b-1:
        return r
    t = 1-r
    if 1 in windows:
        half = (ARC_CAP-windows[1])/2
        if half > 0:
            _, root = sqrt_bounds(r*r-sin_lower(half)**2)
            t = max(t, cos_lower(half)-root)
    return 4*r-t


def angle_map(edges):
    return {(i,j): w for i,j,w in edges}


def matches(have, target_angles, needs, extra):
    return any(have & req == req for req in needs) and all(
        target_angles.get((u,v), -10**10) >= w for u,v,w in extra
    )


def check(proof, n, b, h, shell_faces, faces, edges, windows, full=None):
    require(len(shell_faces)+len(faces) == 2*n-b-2, "Wrong triangle count")
    support = proof.get("support", faces)
    if "support" in proof:
        have = mask((*shell_faces, *faces), b)
        for f in support:
            req = mask([f], b)
            require(len(f) in (2,3) and len(set(f)) == len(f)
                    and b <= min(f) <= max(f) < n and req & have == req,
                    "Unsupported inner witness")
    all_faces = shell_faces + support
    trial = certified_trial_radius() if proof.get("tight",False) else RADIUS
    require(trial <= RADIUS, "The exclusion radius exceeds the angular trial radius")
    extra = []
    if proof.get("full_angles", False):
        outer = angle_map(edges)
        edges = angles(b, n, shell_faces + faces, windows) if full is None else full
        extra = [(u,v,w) for u,v,w in edges if w > outer.get((u,v), -10**10)]
    if "tree" in proof:
        graph = graph_from_faces(n, all_faces, boundary=b)
        leaves = verify_tree(proof["tree"], graph, edges, boundary=b,radius=trial)
    else:
        require(len(proof["trees"]) == n-b-h, "Missing an origin branch")
        cap = min(origin_cap(n,b,h,windows),trial)
        leaves = sum(
            verify_tree(tree, graph_from_faces(n, all_faces, u, b), edges, cap, b,radius=trial)
            for u, tree in enumerate(proof["trees"], start=b+h)
        )
    local = [tuple(u-b for u in f) for f in support]
    return required_faces(proof, local, len(shell_faces), h, n-b), leaves, extra


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shells", type=Path)
    parser.add_argument("fills", type=Path)
    parser.add_argument("windows", type=Path)
    parser.add_argument("proofs", type=Path, nargs="+")
    parser.add_argument("--disks", type=int, required=True)
    parser.add_argument("--boundary", type=int, required=True)
    parser.add_argument("--remaining", type=Path)
    parser.add_argument("--orbits", action="store_true")
    args = parser.parse_args()
    n, b = args.disks, args.boundary
    windows = model_windows(args.windows,n,b)
    shells = args.shells.read_text(encoding="utf-8").splitlines()
    fills = args.fills.read_text(encoding="utf-8").splitlines()
    require(len(set(fills)) == len(fills), "Repeated filling")
    by_shell = defaultdict(dict)
    for line in fills:
        i, f = parse_fill(line, n, b)
        require(0 <= i < len(shells), "Unknown shell")
        by_shell[i][line] = f
    covered, checked, leaves, count = set(), set(), 0, 0
    for record in read_records(args.proofs):
        i = record["index"]
        require(type(i) is int and i in by_shell and record["shell"] == shells[i], "Changed shell")
        checked.add(i)
        h, shell_faces, _ = parse_shell(shells[i], n, b)
        edges = angles(b,b+h,shell_faces,windows)
        outer = mask(shell_faces, b)
        full = any(p.get("full_angles", False) for p in record["proofs"])
        domains = {line: angles(b,n,shell_faces+f,windows) for line,f in by_shell[i].items()} if full else {}
        targets = [(line, mask(f,b)|outer, angle_map(domains[line]) if full else None)
                   for line,f in by_shell[i].items()]
        for proof in record["proofs"]:
            line = proof["fill"]
            require(line in by_shell[i], "Missing source fill")
            needs, sub, extra = check(proof,n,b,h,shell_faces,by_shell[i][line],edges,windows,domains.get(line))
            covered.update(line for line, have, domain in targets if matches(have,domain,needs,extra))
            leaves += sub
            count += 1
            if count % 10000 == 0:
                print(f"checked={count} excluded={len(covered)}",flush=True)
    if args.orbits:
        for i in checked:
            h, outer, _ = parse_shell(shells[i],n,b)
            maps = shell_symmetries(outer,n,b,h)
            keys = {line:orbit_key(f,maps) for line,f in by_shell[i].items()}
            closed = {key for line,key in keys.items() if line in covered}
            covered.update(line for line,key in keys.items() if key in closed)
    print(f"PASS n={n} b={b} shells={len(checked)} proofs={count} leaves={leaves} "
          f"excluded={len(covered)} remaining={len(fills)-len(covered)}", flush=True)
    if args.remaining:
        args.remaining.write_text("".join(x+"\n" for x in fills if x not in covered), encoding="utf-8")


if __name__ == "__main__":
    main()
