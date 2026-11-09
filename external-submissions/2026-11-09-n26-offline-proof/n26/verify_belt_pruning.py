"""Replay the patch cuts and exact circular difference-constraint pruning."""

import argparse
import json
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

from rational_trig import pi_bounds
from verify_belt14 import ARC_CAP, window_deficits
from verify_fan import require
from verify_patch14 import cut_margin, total_deficit_upper


B = 14
SCALE = 10**6


def cut_table(entries):
    table = {}
    for row in entries:
        require(cut_margin(row) > 0, f"Unverified patch cut {row['blocks']}")
        widths = tuple(row["blocks"])
        extras = tuple(row.get("extras", [0] * (len(widths) - 1)))
        require(all(Q(x) == 1 for x in row.get("weights", [])),
                "Only unweighted cuts apply to difference constraints")
        q = Q(row["deficit"]) * SCALE
        weight = q.numerator // q.denominator
        for key in ((widths, extras), (widths[::-1], extras[::-1])):
            table[key] = max(table.get(key, 0), weight)
    return table


def parse_belt(line):
    fields = line.rstrip().split("	")
    require(len(fields) == B + 4, "Expected a belt with fourteen links")
    metadata = tuple(map(int, fields[:4]))
    paths = [tuple(map(int, field.split(","))) for field in fields[4:]]
    require(all(p and len(p) == len(set(p)) for p in paths), "Nonsimple link")
    require(all(paths[i - 1][-1] == paths[i][0] for i in range(B)), "Open belt walk")
    require(len({x for p in paths for x in p}) == metadata[1], "Invalid layer count")
    return metadata, paths


def constraints(paths, cuts, total):
    edges = [(i, (i + 1) % B, 0 if i + 1 < B else -total) for i in range(B)]
    start = [i for i, p in enumerate(paths) if p[0] != p[-1]]
    require(len(start) >= 2, "Expected distinct blocks")
    widths = [(start[(j + 1) % len(start)] - i) % B for j, i in enumerate(start)]
    require(all(w in (1, 2) for w in widths) and sum(widths) == B, "Invalid blocks")
    for j, index in enumerate(start):
        sizes, extras = [], []
        width = 0
        for offset in range(len(start) - 1):
            k = (j + offset) % len(start)
            sizes.append(widths[k])
            width += widths[k]
            if offset == 0:
                continue
            extras.append(len(paths[start[k]]) - 2)
            weight = cuts.get((tuple(sizes), tuple(extras)), 0)
            if weight:
                end = index + width + 1
                edges.append((index, end % B, weight - (total if end >= B else 0)))
    return edges


@lru_cache(maxsize=1)
def window_edges():
    _, pi1 = pi_bounds()
    lower = SCALE * (B * ARC_CAP - 2 * pi1)
    lower = lower.numerator // lower.denominator
    result = []
    for length, limit in window_deficits().items():
        u = limit * SCALE
        cap = -((-u.numerator) // u.denominator)
        for i in range(B):
            end = i + length
            result.append((end % B, i, -cap + (lower if end >= B else 0)))
    return result


def has_positive_cycle(edges):
    values = [0] * B
    for _ in range(B):
        changed = False
        for i, j, w in edges:
            if values[i] + w > values[j]:
                values[j] = values[i] + w
                changed = True
        if not changed:
            return False
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("belts", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--remaining", type=Path)
    parser.add_argument("--windows", action="store_true")
    args = parser.parse_args()
    entries = json.loads(args.certificate.read_text(encoding="utf-8"))
    require(bool(entries), "Empty patch certificate")
    cuts = cut_table(entries)
    q = total_deficit_upper() * SCALE
    total = -((-q.numerator) // q.denominator)
    excluded, kept = Counter(), Counter()
    survivors = []
    extra = window_edges() if args.windows else []
    with args.belts.open(encoding="utf-8") as source:
        for line in source:
            meta, paths = parse_belt(line)
            reject = has_positive_cycle(constraints(paths, cuts, total) + extra)
            (excluded if reject else kept)[meta[:2]] += 1
            if not reject and args.remaining:
                survivors.append(line)
    if args.remaining:
        args.remaining.write_text("".join(survivors), encoding="utf-8")
    print(f"PASS {len(entries)} patch cuts, total deficit <= {total}/{SCALE}")
    print(f"excluded={sum(excluded.values())}, remaining={sum(kept.values())}")
    print("apices layer excluded remaining")
    for a, h in sorted(excluded.keys() | kept.keys()):
        print(a, h, excluded[a, h], kept[a, h])


if __name__ == "__main__":
    main()
