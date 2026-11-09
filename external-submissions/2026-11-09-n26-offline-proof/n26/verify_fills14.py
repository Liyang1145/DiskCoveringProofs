"""Replay certified inner chord and completed topology exclusions."""

import argparse
import gzip
import json
from fractions import Fraction as Q
from pathlib import Path

from verify_belt_geometry import build_graph, starting_constraints, verify_tree
from verify_belt14 import OUTER_NORM, window_deficits
from verify_belt_pruning import B, cut_table, parse_belt
from verify_fan import require
from verify_patch14 import RADIUS


INSIDE = 12


def parse_fill(row):
    fields = row.split("\t")
    index = int(fields[0])
    faces = [tuple(map(int, t.split(","))) for t in fields[1:]]
    require(all(len(t) == 3 and len(set(t)) == 3 and all(0 <= i < INSIDE for i in t)
                for t in faces), "Invalid inner face")
    require(len({tuple(sorted(t)) for t in faces}) == len(faces), "Duplicate inner face")
    return index, faces


def origin_radius(h):
    require(RADIUS < Q(1, 4) and 1 - 3 * RADIUS > RADIUS, "Origin separation failed")
    if h == INSIDE - 1:
        window_deficits()
        return 4 * RADIUS - OUTER_NORM
    return RADIUS


def verify_chords(proofs, belts, cuts):
    blocked = set()
    leaves = 0
    for proof in proofs:
        i, (u, v) = proof["index"], proof["chord"]
        require(type(i) is int and 0 <= i < len(belts) and proof["belt"] == belts[i],
                "Changed belt")
        meta, paths = parse_belt(belts[i])
        require(type(u) is int and type(v) is int and 0 <= u < v < meta[1]
                and (i, u, v) not in blocked, "Invalid or duplicate chord")
        graph = build_graph(paths, [(u, v)])
        leaves += verify_tree(proof["tree"], graph,
                              starting_constraints(paths, cuts, proof.get("windows", False)))
        blocked.add((i, u, v))
    require(bool(blocked), "Empty chord certificate")
    print(f"PASS {len(blocked)} chord exclusions, leaves={leaves}")
    return blocked


def verify_fills(proofs, fills, belts, cuts):
    excluded = set()
    leaves = 0
    for proof in proofs:
        j = proof["index"]
        require(type(j) is int and 0 <= j < len(fills) and proof["fill"] == fills[j]
                and j not in excluded, "Changed or duplicate filling")
        i, faces = parse_fill(fills[j])
        require(0 <= i < len(belts) and proof["belt"] == belts[i], "Changed belt")
        meta, paths = parse_belt(belts[i])
        h = meta[1]
        constraints = starting_constraints(paths, cuts, proof.get("windows", False))
        graph = build_graph(paths, faces, INSIDE)
        require(len(graph[1]) == 2 * (B + INSIDE) - B - 2, "Wrong triangle count")
        if "tree" in proof:
            leaves += verify_tree(proof["tree"], graph, constraints)
        else:
            require(len(proof["trees"]) == INSIDE - h, "Missing an origin branch")
            for p, tree in enumerate(proof["trees"], start=h):
                graph = build_graph(paths, faces, INSIDE, B + p)
                leaves += verify_tree(tree, graph, constraints, origin_radius(h))
        excluded.add(j)
    require(bool(excluded), "Empty filling certificate")
    print(f"PASS {len(excluded)} full fillings excluded, leaves={leaves}, "
          f"unexcluded in supplied sample={len(fills) - len(excluded)}")
    return excluded


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("belts", type=Path)
    parser.add_argument("patch_cuts", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--fills", type=Path)
    parser.add_argument("--blocked", type=Path)
    parser.add_argument("--unexcluded", type=Path)
    args = parser.parse_args()
    belts = args.belts.read_text(encoding="utf-8").splitlines()
    cuts = cut_table(json.loads(args.patch_cuts.read_text(encoding="utf-8")))
    if args.certificate.suffix == ".gz":
        with gzip.open(args.certificate, "rt", encoding="utf-8") as source:
            proofs = json.load(source)
    else:
        proofs = json.loads(args.certificate.read_text(encoding="utf-8"))
    if args.fills is not None:
        fills = args.fills.read_text(encoding="utf-8").splitlines()
        excluded = verify_fills(proofs, fills, belts, cuts)
        if args.unexcluded:
            args.unexcluded.write_text("\n".join(str(i) for i in range(len(fills)) if i not in excluded),
                                       encoding="utf-8")
    else:
        blocked = verify_chords(proofs, belts, cuts)
        if args.blocked:
            args.blocked.write_text(
                "".join(f"{i}\t{u}\t{v}\n" for i, u, v in sorted(blocked)), encoding="utf-8"
            )


if __name__ == "__main__":
    main()
