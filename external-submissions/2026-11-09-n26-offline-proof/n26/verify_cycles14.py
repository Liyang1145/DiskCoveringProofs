"""Reuse an exact geometric exclusion across every belt containing an inner cycle."""

import argparse
import json
from collections import Counter
from pathlib import Path

from verify_belt_geometry import build_graph, starting_constraints, verify_tree
from verify_belt_pruning import B, parse_belt
from verify_fan import require


def split_walk(walk):
    first = {}
    for i, v in enumerate(walk[:-1]):
        if v in first:
            j = first[v]
            yield from split_walk(walk[j:i + 1])
            yield from split_walk(walk[:j] + walk[i:])
            return
        first[v] = i
    yield walk


def canonical(indices):
    return min(
        tuple((a[k] - a[j]) % B for k in (*range(j, len(a)), *range(j)))
        for a in (indices, [-i for i in reversed(indices)])
        for j in range(len(a))
    )


def cycles(paths):
    edge_slot = {(u, v): i for i, path in enumerate(paths) for u, v in zip(path, path[1:])}
    walk = [paths[0][0], *(v for p in paths for v in p[1:])]
    require(walk[0] == walk[-1], "Open inner face walk")
    return {
        canonical([edge_slot[u, v] for u, v in zip(c, c[1:])])
        for c in split_walk(walk) if len(c) > 3
    }


def cycle_graph(pattern):
    require(3 <= len(pattern) <= 11 and all(
        type(x) is int and 0 <= x < B for x in pattern
    ), "Invalid inner cycle")
    outer = sorted(set(pattern))
    label = {x: i for i, x in enumerate(outer)}
    h, m = len(outer), len(pattern)
    sites = h + m
    faces = [(label[x], h + i, h + (i + 1) % m) for i, x in enumerate(pattern)]
    free = sites + m
    edges = [(u, sites + j) for j, face in enumerate(faces) for u in face]
    edges.extend((i, free + (x + j) % B) for i, x in enumerate(outer) for j in range(2))
    return sites, faces, free, edges


def cycle_constraints():
    # Empty patch table. Use only nonnegative arc deficits and their total.
    return starting_constraints([(i, (i + 1) % B) for i in range(B)], {})


def bits(mask):
    while mask:
        lowest = mask & -mask
        yield lowest.bit_length() - 1
        mask ^= lowest


def witness_adjacency(paths):
    sites, faces, _, _ = build_graph(paths)
    containing = [0] * sites
    for i, face in enumerate(faces):
        for u in face:
            containing[u] |= 1 << i
    return containing[:B], [containing[u] | containing[v] | containing[w] for u, v, w in faces]


def pattern_walk(pattern, exterior, neighbors):
    """Test whether the cycle graph maps into the belt, allowing identifications."""
    for sign in (1, -1):
        for shift in range(B):
            masks = [exterior[(shift + sign * j) % B] for j in pattern]
            start = min(range(len(masks)), key=lambda i: masks[i].bit_count())
            masks = masks[start:] + masks[:start]
            for root in bits(masks[0]):
                reached = 1 << root
                for mask in masks[1:]:
                    reached_next = 0
                    for u in bits(reached):
                        reached_next |= neighbors[u]
                    reached = reached_next & mask
                    if not reached:
                        break
                if reached & neighbors[root]:
                    return True
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("belts", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--remaining", type=Path)
    parser.add_argument("--all-walks", action="store_true")
    args = parser.parse_args()
    proofs = json.loads(args.certificate.read_text(encoding="utf-8"))
    forbidden, leaves = set(), 0
    edges = cycle_constraints()
    for proof in proofs:
        key = tuple(proof["pattern"])
        require(key == canonical(list(key)) and key not in forbidden, "Noncanonical or duplicate pattern")
        leaves += verify_tree(proof["tree"], cycle_graph(key), edges)
        forbidden.add(key)
    require(bool(forbidden), "Empty cycle certificate")
    excluded, kept = Counter(), Counter()
    survivors = []
    with args.belts.open(encoding="utf-8") as source:
        for line in source:
            meta, paths = parse_belt(line)
            rejected = bool(forbidden & cycles(paths))
            if args.all_walks and not rejected:
                exterior, neighbors = witness_adjacency(paths)
                rejected = any(pattern_walk(pattern, exterior, neighbors) for pattern in forbidden)
            (excluded if rejected else kept)[meta[:2]] += 1
            if not rejected and args.remaining:
                survivors.append(line)
    if args.remaining:
        args.remaining.write_text("".join(survivors), encoding="utf-8")
    print(f"PASS cycle patterns={len(forbidden)}, leaves={leaves}, "
          f"excluded={sum(excluded.values())}, remaining={sum(kept.values())}")
    print("apices layer excluded remaining")
    for a, h in sorted(excluded.keys() | kept.keys()):
        print(a, h, excluded[a, h], kept[a, h])


if __name__ == "__main__":
    main()
