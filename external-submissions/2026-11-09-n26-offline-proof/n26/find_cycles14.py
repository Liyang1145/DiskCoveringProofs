"""Find rational cycle exclusions for common inner face walks."""

import argparse
import json
from collections import Counter
from pathlib import Path

from find_belt_geometry import search
from find_patch14 import fixed_graph_flow, np
from verify_belt_geometry import verify_tree
from verify_belt_pruning import B, parse_belt
from verify_cycles14 import cycle_constraints, cycle_graph, cycles
from verify_patch14 import ARC_CAP


def flow_at(graph, pattern, prefix):
    sites, faces, free, edges = graph
    outer = sorted(set(pattern))
    h, m = len(outer), len(pattern)
    t = float(ARC_CAP) * np.arange(B) - prefix
    y = np.stack((np.cos(t), np.sin(t)), axis=1)
    p = np.zeros((free, 2))
    p[:h] = .94 * (y[outer] + y[(np.array(outer) + 1) % B]) / 2
    for i in range(m):
        p[h + i] = .72 * (p[faces[i - 1][0]] + p[faces[i][0]]) / 2
    for i, face in enumerate(faces):
        p[sites + i] = p[list(face)].mean(axis=0)
    return fixed_graph_flow(free, edges, y, p)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("belts", type=Path)
    parser.add_argument("--min-length", type=int, default=7)
    parser.add_argument("--max-length", type=int, default=8)
    parser.add_argument("--depth", type=int, default=3)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    freq = Counter()
    with args.belts.open(encoding="utf-8") as source:
        for line in source:
            _, paths = parse_belt(line)
            freq.update(p for p in cycles(paths) if args.min_length <= len(p) <= args.max_length)
    edges = cycle_constraints()
    proofs = []
    for pattern, count in freq.most_common():
        graph = cycle_graph(pattern)
        tree = search(graph, lambda u: flow_at(graph, pattern, u), edges, args.depth)
        if tree is not None:
            verify_tree(tree, graph, edges)
            proofs.append({"pattern": pattern, "tree": tree})
        print(f"{pattern}, belts={count}, proved={tree is not None}", flush=True)
    args.out.write_text(json.dumps(proofs, separators=(",", ":")) + "\n", encoding="utf-8")
    print(f"tried={len(freq)}, proved={len(proofs)}", flush=True)


if __name__ == "__main__":
    main()
