"""Search for exact cone-graph certificates on specified chords or fills."""

import argparse
import json
from itertools import combinations
from pathlib import Path

from find_belt_geometry import free_angle_flow, graph_flow, search
from verify_belt_geometry import build_graph, starting_constraints, verify_tree
from verify_belt_pruning import B, cut_table, parse_belt
from verify_cycles14 import split_walk
from verify_fills14 import INSIDE, origin_radius, parse_fill


def possible_chords(paths, h):
    profile = [{i for i, path in enumerate(paths) if u in path} for u in range(h)]
    shell = {tuple(sorted((u, v))) for p in paths for u, v in zip(p, p[1:])}
    walk = [paths[0][0], *(x for path in paths for x in path[1:])]
    pairs = {tuple(sorted((u, v))) for polygon in split_walk(walk)
             for u, v in combinations(polygon[:-1], 2)}
    for u, v in sorted(pairs):
        if (u, v) not in shell and all(
            min(abs(a - b), B - abs(a - b)) <= 4 for a in profile[u] for b in profile[v]
        ):
            yield u, v


def generate_chords(belts, cuts, layer, depth, start=0, stop=None, free_angle=False, windows=False):
    proofs = []
    tried = 0
    for i in range(start, min(len(belts), len(belts) if stop is None else stop)):
        line = belts[i]
        meta, paths = parse_belt(line)
        if layer != meta[1]:
            continue
        edges = starting_constraints(paths, cuts, windows)
        for chord in possible_chords(paths, layer):
            tried += 1
            graph = build_graph(paths, [chord])
            f = free_angle_flow(graph, paths) if free_angle else None
            tree = search(graph, lambda u: graph_flow(graph, paths, u), edges, depth,
                          [f] if f is not None else ())
            if tree is not None:
                verify_tree(tree, graph, edges)
                proofs.append({"index": i, "belt": line, "chord": chord, "tree": tree, "windows": windows})
                print(f"belt {i}, chord {chord} excluded", flush=True)
    return tried, proofs


def generate_fills(belts, fills, cuts, depth, start=0, stop=None, candidates=None,
                   free_angle=False, windows=False):
    proofs = []
    tried = 0
    for j in range(start, min(len(fills), len(fills) if stop is None else stop)):
        if candidates is not None and j not in candidates:
            continue
        tried += 1
        fill = fills[j]
        i, faces = parse_fill(fill)
        meta, paths = parse_belt(belts[i])
        h = meta[1]
        edges = starting_constraints(paths, cuts, windows)
        graph = build_graph(paths, faces, INSIDE)
        f = free_angle_flow(graph, paths) if free_angle else None
        proof = search(graph, lambda u: graph_flow(graph, paths, u), edges, depth,
                       [f] if f is not None else ())
        if proof is not None:
            verify_tree(proof, graph, edges)
            proofs.append({"index": j, "fill": fill, "belt": belts[i],
                           "tree": proof, "windows": windows})
            print(f"fill {j} of belt {i} excluded", flush=True)
            continue
        cap = origin_radius(h)
        trees = []
        for p in range(h, INSIDE):
            graph = build_graph(paths, faces, INSIDE, B + p)
            f = free_angle_flow(graph, paths, cap) if free_angle else None
            tree = search(graph, lambda u: graph_flow(graph, paths, u, cap), edges, depth,
                          [f] if f is not None else (), origin_cap=cap)
            if tree is None:
                break
            verify_tree(tree, graph, edges, cap)
            trees.append(tree)
        if len(trees) == INSIDE - h:
            proofs.append({"index": j, "fill": fill, "belt": belts[i],
                           "trees": trees, "windows": windows})
            print(f"fill {j} of belt {i} excluded", flush=True)
    return tried, proofs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("belts", type=Path)
    parser.add_argument("patch_cuts", type=Path)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--layer", type=int)
    modes.add_argument("--fills", type=Path)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int)
    parser.add_argument("--indices", type=Path, help="Optional list of fill indices to retry")
    parser.add_argument("--free-angle", action="store_true")
    parser.add_argument("--windows", action="store_true")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    belts = args.belts.read_text(encoding="utf-8").splitlines()
    cuts = cut_table(json.loads(args.patch_cuts.read_text(encoding="utf-8")))
    if args.fills is None:
        tried, proofs = generate_chords(belts, cuts, args.layer, args.depth,
                                        args.start, args.stop, args.free_angle, args.windows)
    else:
        tried, proofs = generate_fills(belts, args.fills.read_text(encoding="utf-8").splitlines(),
                                      cuts, args.depth, args.start, args.stop,
                                      set(map(int, args.indices.read_text().split()))
                                      if args.indices else None, args.free_angle, args.windows)
    args.out.write_text(json.dumps(proofs, separators=(",", ":")) + "\n", encoding="utf-8")
    print(f"tried={tried}, proved={len(proofs)}")


if __name__ == "__main__":
    main()
