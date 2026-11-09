"""Replay flow proofs and transfer them to fills containing their used faces."""

import argparse
import gzip
import json
from collections import defaultdict
from itertools import combinations, permutations
from pathlib import Path

from verify_belt_geometry import build_graph, starting_constraints, verify_tree
from verify_belt_pruning import B, cut_table, parse_belt
from verify_fan import require
from verify_fills14 import INSIDE, origin_radius, parse_fill


FACE_BIT = {
    p: 1 << i
    for i, p in enumerate((*combinations(range(INSIDE), 2), *combinations(range(INSIDE), 3)))
}


def groups(fills, belts):
    result = defaultdict(list)
    for line in fills:
        i, faces = parse_fill(line)
        require(0 <= i < len(belts), "Unknown belt")
        result[i].append((line, faces))
    require(sum(map(len, result.values())) == len(fills)
            and len(set(fills)) == len(fills), "Repeated filling")
    return result


def face_mask(faces):
    result = 0
    for face in faces:
        v = sorted(face)
        for p in combinations(v, 2):
            result |= FACE_BIT[p]
        if len(v) == 3:
            result |= FACE_BIT[tuple(v)]
    return result


def shell_mask(paths):
    return face_mask((u, v) for p in paths for u, v in zip(p, p[1:]))


def flow_rows(tree):
    if "split" in tree:
        yield from flow_rows(tree["lower"])
        yield from flow_rows(tree["upper"])
    elif "flows" in tree:
        yield from tree["flows"]
        for energy in tree.get("energies", []):
            yield [(w,) for w in energy["weights"]]


def required_faces(proof, faces, shell_faces, h, inside=INSIDE):
    required = set()
    trees = [proof["tree"]] if "tree" in proof else proof["trees"]
    for tree in trees:
        for f in flow_rows(tree):
            offset = 3 * shell_faces
            for face in faces:
                used = tuple(sorted(u for k, u in enumerate(face) if any(f[offset + k])))
                offset += len(face)
                if len(used) >= 2:
                    required.add(used)
    result = set()
    for perm in permutations(range(h, inside)):
        labels = (*range(h), *perm)
        mask = 0
        for p in required:
            mask |= FACE_BIT[tuple(sorted(labels[u] for u in p))]
        result.add(mask)
    return tuple(sorted(result))


def check_proof(proof, paths, faces, cuts, edges=None):
    h = 1 + max(u for p in paths for u in p)
    shell_faces = B + sum(len(p) - 1 for p in paths)
    require(shell_faces + len(faces) == 2 * (B + INSIDE) - B - 2,
            "Wrong triangle count")
    support = proof.get("support", faces)
    if "support" in proof:
        have = face_mask(faces) | shell_mask(paths)
        for p in support:
            v = tuple(sorted(p))
            require(v in FACE_BIT and have & FACE_BIT[v], "Unsupported inner witness")
    graph = build_graph(paths, support, INSIDE)
    if edges is None:
        edges = starting_constraints(paths, cuts, proof.get("windows", False))
    if "tree" in proof:
        leaves = verify_tree(proof["tree"], graph, edges)
    else:
        require(len(proof["trees"]) == INSIDE - h, "Missing an origin branch")
        leaves = sum(
            verify_tree(tree, build_graph(paths, support, INSIDE, B + u), edges, origin_radius(h))
            for u, tree in enumerate(proof["trees"], start=h)
        )
    return required_faces(proof, support, shell_faces, h), leaves


def read_records(files):
    for file in files:
        opener = gzip.open if file.suffix == ".gz" else open
        with opener(file, "rt", encoding="utf-8") as stream:
            for line in stream:
                yield json.loads(line)


def verify(belts, fills, cuts, records):
    partition = groups(fills, belts)
    covered = set()
    seen_belts, proofs, leaves = set(), 0, 0
    for record in records:
        i = record["index"]
        require(type(i) is int and i in partition and record["belt"] == belts[i],
                "Unknown or changed belt")
        seen_belts.add(i)
        _, paths = parse_belt(belts[i])
        shell = shell_mask(paths)
        source = dict(partition[i])
        target = [(line, face_mask(faces) | shell) for line, faces in partition[i]]
        domains = {}
        for proof in record["proofs"]:
            require(proof["fill"] in source, "Source filling missing")
            windows = proof.get("windows", False)
            if windows not in domains:
                domains[windows] = starting_constraints(paths, cuts, windows)
            needs, n = check_proof(proof, paths, source[proof["fill"]], cuts, domains[windows])
            proofs += 1
            leaves += n
            covered.update(line for line, have in target if any(have & need == need for need in needs))
    print(f"PASS belts={len(seen_belts)}, proofs={proofs}, leaves={leaves}, "
          f"excluded={len(covered)}, remaining={len(fills)-len(covered)}", flush=True)
    return covered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("belts", type=Path)
    parser.add_argument("fills", type=Path)
    parser.add_argument("patch_cuts", type=Path)
    parser.add_argument("proofs", type=Path, nargs="+")
    parser.add_argument("--remaining", type=Path)
    args = parser.parse_args()
    belts = args.belts.read_text(encoding="utf-8").splitlines()
    fills = args.fills.read_text(encoding="utf-8").splitlines()
    cuts = cut_table(json.loads(args.patch_cuts.read_text(encoding="utf-8")))
    covered = verify(belts, fills, cuts, read_records(args.proofs))
    if args.remaining is not None:
        args.remaining.write_text("".join(s + "\n" for s in fills if s not in covered),
                                  encoding="utf-8")


if __name__ == "__main__":
    main()
