"""Exhaust all pure-inner completions when an outer collar has simple holes.

Nonmanifold/pinched cases fail closed as unhandled. The output exhausts only
the supplied collar's completion family, never all arbitrary-cover topologies.
"""
from pathlib import Path
from collections import defaultdict, Counter, deque
import argparse
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from group_catalog import canonical, canonical_full, validate
from cross_order_strict_transfer import validate_disk
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def bits(mask):
    return [v for v in range(mask.bit_length()) if mask >> v & 1]


def simple_holes(centers, B, masks):
    assert masks == sorted(set(masks)) and masks
    triangles = [bits(mask) for mask in masks]
    assert all(len(f) == 3 and max(f) < centers and any(v < B for v in f) for f in triangles)
    assert {v for face in triangles for v in face} == set(range(centers))
    incidence = defaultdict(list)
    for index, (a, b, c) in enumerate(triangles):
        for u, v in ((a, b), (b, c), (c, a)):
            incidence[tuple(sorted((u, v)))].append(index)
    assert all(len(faces) <= 2 for faces in incidence.values()), "nonmanifold edge"
    exterior = {tuple(sorted((i, (i+1) % B))) for i in range(B)}
    assert all(len(incidence[edge]) == 1 for edge in exterior)
    root = incidence[(0, 1)][0]
    third = next(v for v in triangles[root] if v not in (0, 1))
    oriented = {root: (0, 1, third)}
    todo = [root]
    for index in todo:
        a, b, c = oriented[index]
        for u, v in ((a, b), (b, c), (c, a)):
            for other in incidence[tuple(sorted((u, v)))]:
                if other == index:
                    continue
                w = next(k for k in triangles[other] if k not in (u, v))
                required = (v, u, w)
                if other in oriented:
                    old = oriented[other]
                    assert required in (old, old[1:]+old[:1], old[2:]+old[:2]), "orientation conflict"
                else:
                    oriented[other] = required
                    todo.append(other)
    assert len(oriented) == len(masks), "disconnected retained face dual"
    directed_single = set()
    for a, b, c in oriented.values():
        for u, v in ((a, b), (b, c), (c, a)):
            if len(incidence[tuple(sorted((u, v)))]) == 1:
                directed_single.add((u, v))
    assert {(i, (i+1) % B) for i in range(B)} <= directed_single
    inner_edges = {(v, u) for u, v in directed_single if tuple(sorted((u, v))) not in exterior}
    assert all(u >= B and v >= B for u, v in inner_edges)
    outgoing, incoming = defaultdict(list), defaultdict(list)
    for u, v in inner_edges:
        outgoing[u].append(v)
        incoming[v].append(u)
    assert set(outgoing) == set(incoming)
    assert all(len(outgoing[v]) == len(incoming[v]) == 1 for v in outgoing), "pinched hole boundary"
    holes, unused = [], set(inner_edges)
    while unused:
        start, nxt = min(unused)
        cycle, vertex = [start], start
        while True:
            other = outgoing[vertex][0]
            assert (vertex, other) in unused
            unused.remove((vertex, other))
            if other == start:
                break
            assert other not in cycle, "nonsimple hole"
            cycle.append(other)
            vertex = other
        assert len(cycle) >= 3
        holes.append(cycle)
    # Check every vertex link, independently of the face-dual orientation.
    for vertex in range(centers):
        link = defaultdict(set)
        for face in triangles:
            if vertex in face:
                u, v = [k for k in face if k != vertex]
                link[u].add(v)
                link[v].add(u)
        assert link and all(len(adj) in (1, 2) for adj in link.values())
        endpoints = {v for v, adj in link.items() if len(adj) == 1}
        expected = ({(vertex-1) % B, (vertex+1) % B} if vertex < B else
                    {outgoing[vertex][0], incoming[vertex][0]} if vertex in outgoing else set())
        assert endpoints == expected, "wrong vertex-link endpoints"
        reached, queue = {next(iter(link))}, [next(iter(link))]
        for u in queue:
            for v in link[u]:
                if v not in reached:
                    reached.add(v)
                    queue.append(v)
        assert reached == set(link), "disconnected vertex link"
    assert centers-len(incidence)+len(masks) == 1-len(holes), "not a genus-zero collar"
    return holes


def budgets(total, parts):
    if parts == 0:
        if total == 0:
            yield []
        return
    if parts == 1:
        yield [total]
        return
    for first in range(total+1):
        for tail in budgets(total-first, parts-1):
            yield [first]+tail


def full_code_map(N, B, masks):
    triangles = [bits(mask) for mask in masks]
    incidence, adjacency = defaultdict(list), [set() for _ in range(N)]
    for index, face in enumerate(triangles):
        for v in face:
            adjacency[v].update(set(face)-{v})
        for u, v in ((face[0], face[1]), (face[1], face[2]), (face[2], face[0])):
            incidence[tuple(sorted((u, v)))].append(index)
    profiles = [(tuple(len(adjacency[(shift+sign*j) % B]) for j in range(B)), shift, sign)
                for sign in (1, -1) for shift in range(B)]
    minimum, best, bestmap = min(p[0] for p in profiles), None, None
    for profile, start, sign in profiles:
        if profile != minimum:
            continue
        label = {(start+sign*j) % B: j for j in range(B)}
        root = incidence[tuple(sorted((start, (start+sign) % B)))]
        assert len(root) == 1
        queue, seen, code = [(root[0], start, (start+sign) % B)], {root[0]}, []
        for index, u, v in queue:
            w = next(k for k in triangles[index] if k not in (u, v))
            if w not in label:
                label[w] = len(label)
            code.append(sum(1 << label[k] for k in (u, v, w)))
            for a, b in ((v, w), (w, u)):
                unseen = [f for f in incidence[tuple(sorted((a, b)))] if f not in seen]
                assert len(unseen) <= 1
                if unseen:
                    seen.add(unseen[0])
                    queue.append((unseen[0], a, b))
        assert len(label) == N and len(seen) == len(masks)
        code = tuple(sorted(code))
        if best is None or code < best:
            best = code
            shift = (-sign*start) % B
            bestmap = {"centers": [label[v] for v in range(N)],
                       "anchors": [(shift+sign*j-(sign < 0)) % B for j in range(B)],
                       "orientation": sign, "shift": shift}
    assert best == canonical_full(N, B, masks)
    return best, bestmap


def enumerate_completions(N, B, centers, outer, holes, node_limit):
    adjacency = [set() for _ in range(N)]
    for mask in outer:
        face = bits(mask)
        for vertex in face:
            adjacency[vertex].update(set(face)-{vertex})
    count, completed, maps = 0, {}, {}

    def visit(adj, faces, next_label, pending):
        nonlocal count
        count += 1
        assert not node_limit or count < node_limit, "node limit: incomplete completion family"
        if not pending:
            assert next_label == N and len(faces) == 2*N-B-2
            masks = sorted(faces)
            assert len(set(masks)) == len(masks)
            assert [m for m in masks if m & ((1 << B)-1)] == outer
            validate_disk(N, B, masks)
            code, mapping = full_code_map(N, B, masks)
            restricted = {**mapping, "centers": mapping["centers"][:centers]}
            validate(N, B, outer, restricted, code)
            completed.setdefault(code, len(completed))
            maps.setdefault(code, restricted)
            return
        boundary, inside = pending[-1]
        rest = pending[:-1]
        size = len(boundary)
        if size == 2:
            if inside == 0:
                visit(adj, faces, next_label, rest)
            return
        assert size >= 3 and inside >= 0
        a, c = boundary[:2]

        def add(w):
            newadj = [set(v) for v in adj]
            for u, v in ((a, w), (c, w)):
                newadj[u].add(v)
                newadj[v].add(u)
            return newadj, faces+[(1 << a) | (1 << c) | (1 << w)]

        for k in range(2, size):
            w = boundary[k]
            if k > 2 and w in adj[c]:
                continue
            if k < size-1 and w in adj[a]:
                continue
            newadj, newfaces = add(w)
            left, right = [w]+boundary[1:k], [a]+boundary[k:]
            for left_inside in range(inside+1):
                if len(left) == 2 and left_inside:
                    continue
                if len(right) == 2 and inside-left_inside:
                    continue
                visit(newadj, newfaces, next_label,
                      rest+[(right, inside-left_inside), (left, left_inside)])
        if inside:
            assert next_label < N
            newadj, newfaces = add(next_label)
            visit(newadj, newfaces, next_label+1,
                  rest+[([a, next_label]+boundary[1:], inside-1)])

    for allocation in budgets(N-centers, len(holes)):
        visit(adjacency, list(outer), centers, list(zip(holes, allocation)))
    return completed, maps, count


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path)
    ap.add_argument("--group", type=int)
    ap.add_argument("--candidate", action="store_true")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists() and args.limit >= 0
    if args.candidate:
        source = ROOT.parent / "evidence/n25-algebraic-upper-round2/geometry.json"
        geometry = read(source)
        N, B = 25, 16
        raw = sorted(sum(1 << v for v in face) for face in geometry["faces"] if any(v < B for v in face))
        outer, mapping = canonical(N, B, raw, 1)
        outer, centers = list(outer), len(mapping["centers"])
    else:
        assert args.groups and args.group is not None
        source = args.groups
        data = read(source)
        N, B = data["N"], data["B"]
        assert N == 25 and B in (14, 15, 16, 17)
        row = data["groups"][args.group]
        assert row["id"] == args.group
        centers, outer = row["centers"], row["faces"]
    output = args.output.resolve()
    assert output.is_relative_to(ROOT)
    output.mkdir()
    started = time.monotonic()
    try:
        holes = simple_holes(centers, B, outer)
    except AssertionError as error:
        (output / "UNHANDLED.json").write_text(json.dumps({
            "handled": False, "N": N, "B": B, "source_sha256": sha(source),
            "reason": str(error), "no_exclusion_claimed": True, "global_optimality_proved": False,
        }, indent=2)+"\n", encoding="utf8")
        print("Collar completion unhandled:", error, flush=True)
        return
    completed, maps, calls = enumerate_completions(N, B, centers, outer, holes, args.limit)
    groups = [{"id": gid, "centers": N, "faces": list(code), "members": 1}
              for code, gid in completed.items()]
    bindings = output / "bindings.jsonl"
    with bindings.open("x", encoding="utf8") as stream:
        for group in groups:
            stream.write(json.dumps({
                "index": group["id"], "group": group["id"],
                "map": {"centers": list(range(N)), "anchors": list(range(B)),
                        "orientation": 1, "shift": 0},
            }, separators=(",", ":"))+"\n")
    with (output / "COLLAR-TO-COMPLETION.jsonl").open("x", encoding="utf8") as stream:
        for code, gid in completed.items():
            stream.write(json.dumps({"group": gid, "map": maps[code]}, separators=(",", ":"))+"\n")
    (output / "INPUT-COLLAR.json").write_text(json.dumps({
        "N": N, "B": B, "centers": centers, "faces": outer, "holes": holes,
        "new_inner_centers": N-centers, "source_input_sha256": sha(source),
    }, indent=2)+"\n", encoding="utf8")
    (output / "GROUPS.json").write_text(json.dumps({
        "N": N, "B": B, "threshold": 0, "groups": groups, "group_count": len(groups),
        "selected_types": len(groups), "catalog_types": len(groups),
        "catalog_sha256": sha(output / "INPUT-COLLAR.json"),
        "bindings_file": bindings.name, "bindings_sha256": sha(bindings),
        "verified_embeddings_during_generation": True, "full_selected_catalog_scanned": True,
        "parent_groups_sha256": None, "parent_proof_sha256": None,
        "complete_only_for_this_one_simple_hole_collar": True,
        "not_a_complete_boundary_family": True, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    (output / "SUMMARY.json").write_text(json.dumps({
        "complete_this_collar_completion_search": True, "N": N, "B": B, "calls": calls,
        "full_graph_count": len(groups), "seconds": time.monotonic()-started,
        "input_collar_sha256": sha(output / "INPUT-COLLAR.json"),
        "groups_sha256": sha(output / "GROUPS.json"),
        "maps_sha256": sha(output / "COLLAR-TO-COMPLETION.jsonl"),
        "source_sha256": sha(Path(__file__)),
        "source_induction_and_independent_controls_still_required": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    print("Single collar simple-hole completions enumerated:", len(groups), "full graphs;",
          calls, "calls; controls/source induction still required", flush=True)


if __name__ == "__main__":
    main()
