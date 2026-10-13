"""Exact exposed-face grouping with streamed full-type bindings, n22..25."""
from pathlib import Path
from itertools import permutations, product
from collections import defaultdict, Counter
import argparse
import json
import time
from stream_catalog import Catalog, sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def bits(mask):
    return [v for v in range(mask.bit_length()) if mask >> v & 1]


def canonical_full(N, B, masks):
    """Frozen kernel's complete rooted BFS code, for attainment controls."""
    triangles = [bits(mask) for mask in masks]
    incidence = defaultdict(list)
    adjacency = [set() for _ in range(N)]
    for i, face in enumerate(triangles):
        assert len(face) == 3
        for j in face:
            adjacency[j].update(v for v in face if v != j)
        for u, v in ((face[0], face[1]), (face[1], face[2]), (face[2], face[0])):
            incidence[tuple(sorted((u, v)))].append(i)
    profiles = [(tuple(len(adjacency[(shift+sign*j) % B]) for j in range(B)), shift, sign)
                for sign in (1, -1) for shift in range(B)]
    minimum = min(row[0] for row in profiles)
    best = None
    for profile, shift, sign in profiles:
        if profile != minimum:
            continue
        labels = {(shift+sign*j) % B: j for j in range(B)}
        end = (shift+sign) % B
        roots = incidence[tuple(sorted((shift, end)))]
        assert len(roots) == 1
        queue = [(roots[0], shift, end)]
        seen = {roots[0]}
        code = []
        for index, u, v in queue:
            rest = set(triangles[index])-{u, v}
            assert len(rest) == 1
            w = rest.pop()
            if w not in labels:
                labels[w] = len(labels)
            code.append(sum(1 << labels[j] for j in (u, v, w)))
            for a, b in ((v, w), (w, u)):
                unseen = [i for i in incidence[tuple(sorted((a, b)))] if i not in seen]
                assert len(unseen) <= 1
                if unseen:
                    seen.add(unseen[0])
                    queue.append((unseen[0], a, b))
        assert len(seen) == len(masks) and len(labels) == N
        value = tuple(sorted(code))
        best = value if best is None else min(best, value)
    assert best is not None
    return best


def validate(N, B, code, mapping, full):
    center, anchor = mapping["centers"], mapping["anchors"]
    assert len(set(center)) == len(center) and sorted(center[:B]) == list(range(B))
    assert all(B <= v < N for v in center[B:])
    sign, shift = mapping["orientation"], mapping["shift"]
    assert sign in (1, -1) and 0 <= shift < B
    assert center[:B] == [(shift+sign*j) % B for j in range(B)]
    assert anchor == [(shift+sign*j-(sign < 0)) % B for j in range(B)]
    for i in range(B):
        assert {center[i], center[(i+1) % B]} == {anchor[i], (anchor[i]+1) % B}
    full = set(full)
    for mask in code:
        assert mask.bit_count() == 3
        assert sum(1 << center[v] for v in bits(mask)) in full


def canonical(N, B, full, threshold):
    assert threshold in (0, 1, 2)
    if threshold == 0:
        code = tuple(full)
        mapping = {"centers": list(range(N)), "anchors": list(range(B)), "orientation": 1, "shift": 0}
        validate(N, B, code, mapping, full)
        return code, mapping
    faces = [bits(mask) for mask in full if (mask & ((1 << B)-1)).bit_count() >= threshold]
    used = sorted({v for face in faces for v in face if v >= B})
    adjacency = [set() for _ in range(N)]
    for face in faces:
        for v in face:
            adjacency[v].update(w for w in face if w != v)
    minimum, roots = None, []
    for sign in (1, -1):
        for shift in range(B):
            profile = tuple(len(adjacency[(shift+sign*j) % B]) for j in range(B))
            if minimum is None or profile < minimum:
                minimum, roots = profile, []
            if profile == minimum:
                roots.append((shift, sign))
    best = bestmap = None
    for shift, sign in roots:
        inverse = {(shift+sign*j) % B: j for j in range(B)}
        colors = defaultdict(list)
        for v in used:
            boundary = sum(1 << inverse[w] for w in adjacency[v] if w < B)
            colors[(len(adjacency[v]), boundary)].append(v)
        blocks = [colors[k] for k in sorted(colors)]
        for choice in product(*(permutations(block) for block in blocks)):
            interior = [v for block in choice for v in block]
            old_to_new = dict(inverse)
            old_to_new.update({v: B+i for i, v in enumerate(interior)})
            code = tuple(sorted(sum(1 << old_to_new[v] for v in face) for face in faces))
            if best is None or code < best:
                best = code
                bestmap = {"centers": [(shift+sign*j) % B for j in range(B)]+interior,
                           "anchors": [(shift+sign*j-(sign < 0)) % B for j in range(B)],
                           "orientation": sign, "shift": shift}
    assert best is not None
    validate(N, B, best, bestmap, full)
    return best, bestmap


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--catalog", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--threshold", type=int, choices=(0, 1, 2), default=2)
    p.add_argument("--parent", type=Path)
    p.add_argument("--parent-proof", type=Path)
    p.add_argument("--max-types", type=int)
    args = p.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    catalog = Catalog(args.catalog)
    header = catalog.header
    N, B = header["N"], header["B"]
    assert N in (22, 23, 24, 25)
    parent_stream = None
    parent_row = None
    paid = set()
    if args.parent is not None:
        parent = json.loads(args.parent.read_text())
        assert parent["full_selected_catalog_scanned"]
        proof = json.loads(args.parent_proof.read_text())
        assert parent["catalog_sha256"] == sha(args.catalog)
        assert proof["groups_sha256"] == sha(args.parent)
        outcomes = proof["outcomes"]
        assert sorted(r["group"] for r in outcomes) == list(range(parent["group_count"]))
        paid = {r["group"] for r in outcomes if r["status"] == "excluded"}
        # Stream-merge the selected parent set, not the full catalogue minus
        # only this parent's paid set (that would reintroduce earlier types).
        bindings_path = args.parent.parent / parent["bindings_file"]
        assert sha(bindings_path) == parent["bindings_sha256"]
        parent_stream = bindings_path.open(encoding="utf8")
        line = parent_stream.readline()
        parent_row = json.loads(line) if line else None
    groups, counters = {}, Counter()
    selected = 0
    started = time.monotonic()
    bindingpath = args.output / "bindings.jsonl"
    exhausted = True
    with bindingpath.open("w", encoding="utf8") as bindings:
        for index, row in catalog.rows():
            if parent_stream is not None:
                if parent_row is None:
                    continue
                assert index <= parent_row["index"], "unordered or repeated parent binding"
                if index < parent_row["index"]:
                    continue
                choose = parent_row["group"] not in paid
                line = parent_stream.readline()
                parent_row = json.loads(line) if line else None
                if not choose:
                    continue
            code, mapping = canonical(N, B, row["faces"], args.threshold)
            gid = groups.setdefault(code, len(groups))
            bindings.write(json.dumps({"index": index, "group": gid, "map": mapping}, separators=(",", ":"))+"\n")
            counters[gid] += 1
            selected += 1
            if selected % 100000 == 0:
                print("N", N, "B", B, "grouped", selected, "types into", len(groups),
                      "groups; seconds", round(time.monotonic()-started, 2), flush=True)
            if args.max_types is not None and selected >= args.max_types:
                exhausted = False
                break
    if parent_stream is not None:
        assert not exhausted or parent_row is None
        parent_stream.close()
    ordered = [None]*len(groups)
    for code, gid in groups.items():
        ordered[gid] = {"id": gid, "faces": list(code),
                        "centers": max(v for mask in code for v in bits(mask))+1,
                        "members": counters[gid]}
    result = {"N": N, "B": B, "group_count": len(groups), "groups": ordered,
              "selected_types": selected, "catalog_types": header["orbits"],
              "catalog_sha256": sha(args.catalog), "threshold": args.threshold,
              "bindings_file": bindingpath.name, "bindings_sha256": sha(bindingpath),
              "verified_embeddings_during_generation": True, "full_selected_catalog_scanned": exhausted,
              "selection_is_not_yet_an_accepted_exclusion": True,
              "parent_groups_sha256": None if args.parent is None else sha(args.parent),
              "parent_proof_sha256": None if args.parent is None else sha(args.parent_proof),
              "global_optimality_proved": False, "source_sha256": sha(Path(__file__))}
    (args.output / "GROUPS.json").write_text(json.dumps(result, separators=(",", ":")), encoding="utf8")
    print("N", N, "B", B, "grouping finished", selected, len(groups), "complete scan", exhausted, flush=True)


if __name__ == "__main__":
    main()
