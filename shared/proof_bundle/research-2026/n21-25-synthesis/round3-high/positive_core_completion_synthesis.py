"""Exact center-skeleton audits and constructive n24 core completions.

Completeness of the n24 completion list is NOT claimed. Every listed
triangulation contains the specified core, with an explicit identity map.
No numerical seed, optimizer, or public optimality premise is used.
"""
from pathlib import Path
from itertools import combinations, product
from collections import Counter, defaultdict
from functools import lru_cache
import argparse
import gzip
import json
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(Path(path).read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def edges(faces):
    return {edge for face in faces for edge in combinations(face, 2)}


def disk_check(N, B, faces):
    faces = set(faces)
    assert len(faces) == 2*N-B-2
    assert all(len(f) == 3 and tuple(sorted(f)) == f and len(set(f)) == 3 for f in faces)
    assert {v for f in faces for v in f} == set(range(N))
    incidence = Counter(edge for f in faces for edge in combinations(f, 2))
    boundary = {tuple(sorted((i, (i+1) % B))) for i in range(B)}
    assert len(incidence) == 3*N-B-3
    assert {e for e, count in incidence.items() if count == 1} == boundary
    assert all(count == (1 if e in boundary else 2) for e, count in incidence.items())
    # Each vertex link is one boundary path or one interior cycle.
    for v in range(N):
        adjacency = defaultdict(set)
        for f in faces:
            if v in f:
                a, b = [w for w in f if w != v]
                adjacency[a].add(b)
                adjacency[b].add(a)
        assert adjacency
        visited, pending = set(), [next(iter(adjacency))]
        while pending:
            w = pending.pop()
            if w not in visited:
                visited.add(w)
                pending.extend(adjacency[w]-visited)
        assert visited == set(adjacency)
        degrees = sorted(map(len, adjacency.values()))
        if v < B:
            assert degrees[:2] == [1, 1] and all(d == 2 for d in degrees[2:])
        else:
            assert all(d == 2 for d in degrees)
    # Explicit coherent orientation, not just counts or a drawing.
    edge_faces = defaultdict(list)
    for f in faces:
        for e in combinations(f, 2):
            edge_faces[e].append(f)
    def direction(f, e):
        a, b, c = f
        return 1 if e in ((a, b), (b, c), (c, a)) else -1
    signs = {}
    root = next(iter(faces))
    signs[root] = 1
    pending = [root]
    while pending:
        f = pending.pop()
        for e in combinations(f, 2):
            for other in edge_faces[e]:
                if other == f:
                    continue
                required = -signs[f]*direction(f, e)*direction(other, e)
                if other in signs:
                    assert signs[other] == required
                else:
                    signs[other] = required
                    pending.append(other)
    assert len(signs) == len(faces)
    assert N-len(incidence)+len(faces) == 1
    return True


@lru_cache(None)
def triangulations(boundary, free):
    """Complete root-face recursion on a small labeled polygon region."""
    if len(boundary) == 2:
        return (frozenset(),) if not free else ()
    assert len(boundary) >= 3 and len(set(boundary)) == len(boundary)
    assert len(free) <= 1 and not set(boundary)&set(free)
    a, b = boundary[:2]
    result = set()
    for k in range(2, len(boundary)):
        w = boundary[k]
        left, right = (w,)+boundary[1:k], (a,)+boundary[k:]
        allocations = (((), ()),) if not free else ((free, ()), ((), free))
        for lfree, rfree in allocations:
            for lfaces, rfaces in product(triangulations(left, lfree), triangulations(right, rfree)):
                result.add(lfaces | rfaces | {tuple(sorted((a, b, w)))})
    if free:
        w = free[0]
        for rest in triangulations((a, w)+boundary[1:], ()):
            result.add(rest | {tuple(sorted((a, b, w)))})
    # Exposing an interior vertex makes the removed root edge a forbidden
    # diagonal of the remaining polygon. Unconstrained polygon recursion can
    # reintroduce the same root triangle; such a glued object is not a disk.
    # Reject it by exact distinct-face count before accepting a completion.
    expected_faces = len(boundary)+2*len(free)-2
    result = {faces for faces in result if len(faces) == expected_faces}
    return tuple(sorted(result, key=lambda x: sorted(x)))


def omitted_regions(full, active):
    missing = full-active
    remaining = set(missing)
    components = []
    while remaining:
        component, pending = set(), [min(remaining)]
        while pending:
            face = pending.pop()
            if face not in remaining:
                continue
            remaining.remove(face)
            component.add(face)
            pending.extend(other for other in remaining if len(set(face)&set(other)) == 2)
        counts = Counter(e for f in component for e in combinations(f, 2))
        frontier = {e for e, count in counts.items() if count == 1}
        adjacency = defaultdict(set)
        for a, b in frontier:
            adjacency[a].add(b)
            adjacency[b].add(a)
        assert all(len(values) == 2 for values in adjacency.values())
        first = min(adjacency)
        cycle = [first, min(adjacency[first])]
        while True:
            options = adjacency[cycle[-1]]-{cycle[-2]}
            assert len(options) == 1
            nxt = options.pop()
            if nxt == first:
                break
            assert nxt not in cycle
            cycle.append(nxt)
        assert set(cycle) == set(adjacency)
        interior = sorted({v for f in component for v in f}-set(cycle))
        components.append({"cycle": cycle, "interior": interior,
                           "original_faces": sorted(map(list, component))})
    return sorted(components, key=lambda row: row["cycle"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    records, sources = [], {}
    systems = {}
    for N in range(21, 25):
        path = (ROOT.parent / "round2-grouped/evidence/n21-interfaces-resume2/core-system.json"
                if N == 21 else ROOT.parent / f"evidence/n{N}/core-system.json")
        source = read(path)
        sources[str(path.resolve())] = sha(path)
        B = source["B"]
        full = {tuple(sorted(f)) for f in source["all_faces"]}
        active = {tuple(sorted(f)) for f in source["active_faces"]}
        assert active <= full and disk_check(N, B, full)
        boundary = {tuple(sorted((i, (i+1) % B))) for i in range(B)}
        retained_edges = boundary | edges(active)
        full_edges = boundary | edges(full)
        cliques = {triple for triple in combinations(range(N), 3)
                   if all(e in retained_edges for e in combinations(triple, 2))}
        forces = retained_edges == full_edges and cliques == full
        records.append({"N": N, "B": B, "active_faces": len(active), "full_faces": len(full),
                        "retained_center_edges": len(retained_edges), "full_center_edges": len(full_edges),
                        "retained_triangular_cliques": len(cliques),
                        "full_completion_forced_by_edge_and_clique_counts": forces,
                        "statement_requires_explicit_core_embedding": True,
                        "global_optimality_proved_by_this_audit": False})
        systems[N] = B, full, active
    # n24 has seven complement regions: six triangles and one pentagon;
    # exactly one unused center. Move that center among these regions.
    N = 24
    B, full, active = systems[N]
    regions = omitted_regions(full, active)
    free = tuple(sorted(set(range(N))-{v for f in active for v in f}))
    assert free == (19,)
    assert sorted(len(row["cycle"]) for row in regions) == [3]*6+[5]
    assert sorted(v for row in regions for v in row["interior"]) == [19]
    completions = set()
    counts = []
    for placement in range(len(regions)):
        choices = [triangulations(tuple(row["cycle"]), free if i == placement else ())
                   for i, row in enumerate(regions)]
        local_count = 0
        for replacements in product(*choices):
            proposed = frozenset(active).union(*replacements)
            assert active <= proposed and disk_check(N, B, proposed)
            completions.add(proposed)
            local_count += 1
        counts.append({"free_center_region": placement, "region_size": len(regions[placement]["cycle"]),
                       "constructed_completions": local_count})
    assert len(completions) == 51 and full in completions
    systempath = ROOT.parent / "evidence/n24/core-system.json"
    system = read(systempath)
    oldmap = {int(old): core for old, core in system["old_node_to_core"].items()}
    assert set(oldmap.values()) == set(range(system["G"]//2+1))
    old_by_core = {core: old for old, core in oldmap.items()}
    original_active = [tuple(sorted(f)) for f in system["active_faces"]]
    rod_transfers = []
    for proposed in sorted(completions, key=lambda x: sorted(x)):
        ordered_faces = sorted(proposed)
        face_index = {f: i for i, f in enumerate(ordered_faces)}
        injection = []
        for core in range(len(old_by_core)):
            old = old_by_core[core]
            injection.append(old if old < B+N else B+N+face_index[original_active[old-B-N]])
        assert len(set(injection)) == len(injection)
        complete_rods = {tuple(sorted((j, B+v))) for j in range(B) for v in (j, (j+1) % B)}
        complete_rods |= {tuple(sorted((B+N+i, B+v)))
                         for i, face in enumerate(ordered_faces) for v in face}
        images = {tuple(sorted((injection[a], injection[b]))) for a, b in system["edges"]}
        assert len(images) == len(system["edges"]) == 90 and images <= complete_rods
        assert injection[:B] == list(range(B))
        rod_transfers.append(injection)
    # Canonical code is used only to count distinct listed full graph types,
    # never to infer completeness of all completions or geometric feasibility.
    from group_catalog import canonical_full
    canonical_codes = {canonical_full(N, B, sorted(sum(1 << v for v in f) for f in proposed))
                       for proposed in completions}
    assert len(canonical_codes) == 25
    sources[str((ROOT / "group_catalog.py").resolve())] = sha(ROOT / "group_catalog.py")
    # This is an independent exact force/core theorem reference, not a new
    # proof by a numerical seed. Verify the saved core replay's source/tree
    # binding, but do not claim this audit replays all its mathematical leaves.
    replaypath = ROOT / "evidence/n24-core-replay-stdlib-resume2.json"
    if not replaypath.exists():
        replaypath = ROOT / "evidence/n24-core-replay-stdlib-resume1.json"
    replay = read(replaypath)
    assert replay["verified"] and replay["N"] == N and replay["B"] == B
    assert replay["source_sha256"] == sha(ROOT / "replay_candidate.py")
    treepath = ROOT / "evidence/n24-core-angle-resume2/core-angle-tree.json.gz"
    if sha(treepath) != replay["tree_sha256"]:
        treepath = ROOT / "evidence/n24-core-angle-resume1/core-angle-tree.json.gz"
    assert sha(treepath) == replay["tree_sha256"]
    with gzip.open(treepath, "rt", encoding="utf8") as stream:
        tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
    rootpath = systempath.parent / "core-root.json"
    localpath = systempath.parent / "local-isolation-certificate.json"
    constpath = ROOT.parent / "evidence/core-reduction/constants/n24.json"
    assert tree["complete"] and not tree["pending"]
    assert tree["system_sha256"] == sha(systempath)
    assert tree["root_sha256"] == sha(rootpath)
    assert tree["local_sha256"] == replay["local_certificate_sha256"] == sha(localpath)
    assert tree["constants_sha256"] == sha(constpath)
    assert replay["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
    for dependency in (rootpath, localpath, constpath, ROOT / "exact_graph.py"):
        sources[str(dependency.resolve())] = sha(dependency)
    sources[str(replaypath.resolve())] = sha(replaypath)
    sources[str(treepath.resolve())] = sha(treepath)
    sources[str((ROOT / "replay_candidate.py").resolve())] = sha(ROOT / "replay_candidate.py")
    result = {"verified": True, "skeleton_audits": records,
              "n24": {"N": N, "B": B, "unused_center": 19, "omitted_regions": regions,
                      "placement_counts": counts, "constructed_labeled_completions": len(completions),
                      "distinct_listed_full_canonical_codes": len(canonical_codes),
                      "completions": [sorted(map(list, f)) for f in sorted(completions, key=lambda x: sorted(x))],
                      "every_completion_simple_oriented_disk_checked": True,
                      "every_completion_contains_same_active_core_by_identity": True,
                      "every_completion_all_90_core_rods_and_15_anchors_injected": True,
                      "core_point_to_full_auxiliary_point_injections": rod_transfers,
                      "existing_core_tree_all_current_input_bindings_match": True,
                      "existing_core_theorem_applicable_after_original_input_bindings_are_paid": True,
                      "existing_core_replay_sha256": sha(replaypath),
                      "all_abstract_supergraph_completions_classified": False,
                      "geometric_feasibility_of_51_topologies_asserted": False,
                      "global_optimality_proved": False},
              "no_numeric_seed_or_optimizer_used": True,
              "source_sha256": sha(Path(__file__)), "files_absolute": sources,
              "global_optimality_proved": False,
              "scope": "exact skeleton/completion source lemmas; not full competing-family exclusion"}
    with args.output.open("x", encoding="utf8") as stream:
        json.dump(result, stream, indent=2)
    print("Positive-core synthesis PASS: n22/n23 skeletons force one completion;",
          "n24 has 51 checked constructed completions containing the same core", flush=True)


if __name__ == "__main__":
    main()
