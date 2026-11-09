"""Exact angular and flow replay for exterior shells with 15 to 17 arcs."""

import argparse
from collections import Counter
from functools import lru_cache
from pathlib import Path

from rational_trig import pi_bounds, sin_lower
from verify_belt_geometry import graph_from_faces, verify_tree
from verify_belt_pruning import SCALE
from verify_cycles14 import bits
from verify_fan import require
from verify_outer_chords import ARC_LIMITS
from verify_outer_windows import model_windows
from verify_patch14 import ARC_CAP, RADIUS
from verify_transfer14 import read_records


def parse_shell(line, n, b):
    fields = line.rstrip().split("\t")
    h = int(fields[0])
    require(1 <= h < n-b and "/" in fields, "Invalid shell header")
    slash = fields.index("/")
    faces = [tuple(map(int, t.split(","))) for t in fields[1:slash]]
    holes = [tuple(map(int, t.split(","))) for t in fields[slash+1:]]
    require(all(len(f) == 3 and len(set(f)) == 3 and min(f) < b
                and 0 <= min(f) and max(f) < b+h for f in faces), "Invalid shell face")
    require(holes and all(len(p) >= 3 and len(set(p)) == len(p)
                          and min(p) >= b and max(p) < b+h for p in holes), "Invalid shell hole")
    directed = Counter()

    def add(cycle, sign):
        for u, v in zip(cycle, (*cycle[1:], cycle[0])):
            edge = (min(u,v), max(u,v))
            directed[edge] += sign if u < v else -sign

    for f in faces:
        add(f, 1)
    add(tuple(range(b)), -1)
    for p in holes:
        add(p, 1)
    require(not any(directed.values()), "Wrong oriented boundary of exterior shell")
    return h, faces, holes


@lru_cache(maxsize=4)
def angle_constants(b):
    pi0, pi1 = pi_bounds()
    require(15 <= b <= 17 and 2*pi0 - 8*ARC_CAP > ARC_LIMITS[-1],
            "A complementary arc may be short")
    for k, c in enumerate(ARC_LIMITS, start=1):
        require(c < pi0 and sin_lower(c/2) > k*RADIUS and (c*SCALE).denominator == 1,
                "Unverified angular path cap")
    q = SCALE * (b*ARC_CAP - 2*pi0)
    upper = -((-q.numerator) // q.denominator)
    q = SCALE * (b*ARC_CAP - 2*pi1)
    lower = q.numerator // q.denominator
    return lower, upper, int(SCALE*ARC_CAP)


def angles(b, sites, faces, windows):
    lower, upper, cap = angle_constants(b)
    req = {}

    def add(i, j, w):
        k = (i, j)
        req[k] = max(req.get(k, w), w)

    for i in range(b):
        j = (i+1) % b
        add(i, j, -upper if j == 0 else 0)
        add(j, i, -cap + (lower if j == 0 else 0))
    for length, bound in windows.items():
        v = bound*SCALE
        w = v.numerator // v.denominator
        require(v == w, "Rounding a deficit upper bound")
        for i in range(b):
            end = i+length
            add(end%b, i, -w + (lower if end >= b else 0))
    adj = [1 << i for i in range(sites)]
    for face in faces:
        both = sum(1 << v for v in face)
        for v in face:
            adj[v] |= both
    reach = [adj]
    for _ in range(2):
        prev = reach[-1]
        layer = []
        for row in prev:
            to = 0
            for j in bits(row):
                to |= adj[j]
            layer.append(to)
        reach.append(layer)
    for i in range(b):
        for s in range(2, b//2+1):
            j = (i+s)%b
            target = (1 << j) | (1 << ((j-1)%b))
            for k, paths in enumerate(reach, start=1):
                if (paths[i] | paths[(i-1)%b]) & target:
                    w = int(SCALE*(s*ARC_CAP - ARC_LIMITS[k]))
                    if w > 0:
                        add(i, j, w - (upper if i+s >= b else 0))
                    break
    return [(i, j, w) for (i, j), w in sorted(req.items())]


def prepare(line, n, b, windows):
    h, faces, _ = parse_shell(line, n, b)
    return h, graph_from_faces(b+h, faces, boundary=b), angles(b, b+h, faces, windows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shells", type=Path)
    parser.add_argument("windows", type=Path)
    parser.add_argument("proofs", type=Path, nargs="+")
    parser.add_argument("--disks", type=int, required=True)
    parser.add_argument("--boundary", type=int, required=True)
    parser.add_argument("--remaining", type=Path)
    args = parser.parse_args()
    n, b = args.disks, args.boundary
    windows = model_windows(args.windows,n,b)
    rows = args.shells.read_text(encoding="utf-8").splitlines()
    covered, leaves = set(), 0
    for p in read_records(args.proofs):
        i = p["index"]
        require(type(i) is int and 0 <= i < len(rows) and p["shell"] == rows[i]
                and i not in covered, "Unknown, changed or duplicate shell")
        h, graph, edges = prepare(rows[i], n, b, windows)
        leaves += verify_tree(p["tree"], graph, edges, boundary=b)
        covered.add(i)
        if len(covered) % 20000 == 0:
            print(f"checked exterior proofs={len(covered)}",flush=True)
    remain = [s for i, s in enumerate(rows) if i not in covered]
    print(f"PASS n={n} b={b} excluded={len(covered)} leaves={leaves} remaining={len(remain)}",
          flush=True)
    print("remaining by first layer", sorted(Counter(int(x.split()[0]) for x in remain).items()))
    if args.remaining is not None:
        args.remaining.write_text("".join(s+"\n" for s in remain), encoding="utf-8")


if __name__ == "__main__":
    main()
