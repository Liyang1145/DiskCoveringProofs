"""Fresh exact strict-force reuse under extra centers and smaller radii.

Tests explicit n23/24/25 triangulations retaining a paid n22 weak graph.
This is a portable exclusion primitive, not any target's global optimum.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter, defaultdict
from copy import deepcopy
import argparse
import gzip
import json
import sys
import exact_graph as exact
from audit_streamed_hierarchy import check_map
from stream_catalog import Catalog, sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
EV = ROOT / "evidence"
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def validate_disk(N, B, masks):
    assert masks == sorted(set(masks))
    faces = [exact.kernel.bits(mask) for mask in masks]
    assert len(faces) == 2*N-B-2
    assert all(len(face) == 3 and all(0 <= v < N for v in face) for face in faces)
    assert {v for face in faces for v in face} == set(range(N))
    incidence = defaultdict(list)
    links = defaultdict(list)
    for i, (a, b, c) in enumerate(faces):
        for u, v, w in ((a, b, c), (b, c, a), (c, a, b)):
            incidence[tuple(sorted((u, v)))].append(i)
            links[u].append((v, w))
    boundary = {tuple(sorted((i, (i+1) % B))) for i in range(B)}
    assert boundary <= set(incidence)
    assert all(len(fs) == (1 if edge in boundary else 2) for edge, fs in incidence.items())
    assert N-len(incidence)+len(faces) == 1
    dual = [set() for _ in faces]
    for pair in incidence.values():
        if len(pair) == 2:
            a, b = pair
            dual[a].add(b)
            dual[b].add(a)
    seen, todo = {0}, [0]
    while todo:
        for other in dual[todo.pop()]:
            if other not in seen:
                seen.add(other)
                todo.append(other)
    assert seen == set(range(len(faces)))
    for vertex, pairs in links.items():
        neighbors = defaultdict(set)
        for a, b in pairs:
            neighbors[a].add(b)
            neighbors[b].add(a)
        endpoints = {v for v, adj in neighbors.items() if len(adj) == 1}
        assert all(len(adj) in (1, 2) for adj in neighbors.values())
        assert endpoints == ({(vertex-1) % B, (vertex+1) % B} if vertex < B else set())
        seen, todo = {next(iter(neighbors))}, [next(iter(neighbors))]
        while todo:
            for other in neighbors[todo.pop()]:
                if other not in seen:
                    seen.add(other)
                    todo.append(other)
        assert seen == set(neighbors)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    B, originalN = 15, 22
    grouppath = EV / "n22-B15-pair-resume1/GROUPS.json"
    receiptpath = EV / "n22-B15-pair-root-resume1/SUMMARY.json"
    replaypath = EV / "n22-B15-pair-replay-resume1.json"
    catalogpath = EV / "n22-B15-dfs-resume1/N22-B15-dfs.json"
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n22.json"
    groups, receipt, paid, constants = map(read, (grouppath, receiptpath, replaypath, constantspath))
    assert groups["N"] == receipt["N"] == paid["N"] == originalN
    assert groups["B"] == receipt["B"] == paid["B"] == B
    assert paid["verified"] and paid["groups_sha256"] == receipt["groups_sha256"] == sha(grouppath)
    assert paid["receipt_sha256"] == sha(receiptpath)
    assert paid["source_sha256"] == sha(ROOT / "replay_group_stage.py")
    assert paid["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
    assert groups["catalog_sha256"] == sha(catalogpath)
    assert groups["threshold"] == 2
    outcomes = {r["group"]: r for r in receipt["outcomes"]}
    bindingpath = grouppath.parent / groups["bindings_file"]
    assert sha(bindingpath) == groups["bindings_sha256"] == paid["bindings_sha256"]
    binding = None
    with bindingpath.open(encoding="utf8") as stream:
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            if outcomes[row["group"]]["status"] == "excluded":
                binding = row
                break
    assert binding is not None
    group = groups["groups"][binding["group"]]
    catalog = Catalog(catalogpath)
    full = None
    for index, row in catalog.rows():
        if index == binding["index"]:
            full = row["faces"]
            catalog.stream.close()
            break
    assert full is not None
    validate_disk(originalN, B, full)
    check_map(originalN, B, group, binding["map"], set(full), 2)
    outcome = outcomes[group["id"]]
    treepath = receiptpath.parent / f"group-{group['id']:07}.json.gz"
    assert sha(treepath) == outcome["tree_sha256"]
    with gzip.open(treepath, "rt", encoding="utf8") as stream:
        tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
    assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
        originalN, B, group["centers"], group["faces"])
    assert tree["constants_sha256"] == sha(constantspath)
    assert tree["groups_sha256"] == sha(grouppath)
    fresh = exact.verify(B, group["centers"], group["faces"], tree["nodes"], constants)
    assert F(fresh["minimum_force_margin"]) > 0
    originalU = F(constants["radius_upper"])
    extensions = []
    target = set(full)
    for N in (23, 24, 25):
        # Subdivide a face not retained in the paid two-boundary-face graph.
        choices = [mask for mask in target if (mask & ((1 << B)-1)).bit_count() < 2]
        assert choices
        chosen = min(choices)
        a, b, c = exact.kernel.bits(chosen)
        new = N-1
        target.remove(chosen)
        target.update((1 << new) | (1 << u) | (1 << v)
                      for u, v in ((a, b), (b, c), (c, a)))
        masks = sorted(target)
        validate_disk(N, B, masks)
        check_map(N, B, group, binding["map"], target, 2)
        targetconstants = ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"
        const = read(targetconstants)
        assert const["verified"] and const["N"] == N and [B, N-B] in const["families"]
        U = F(const["radius_upper"])
        assert U <= originalU
        extensions.append({"N": N, "B": B, "faces": masks,
                           "source_graph_to_extension": binding["map"],
                           "radius_upper": str(U), "strict_radius_decrease": str(originalU-U),
                           "target_constants_sha256": sha(targetconstants),
                           "subdivided_face": chosen,
                           "strict_exclusion_transferred": True})
    rejected = []
    invalid = deepcopy(binding["map"])
    invalid["centers"][0] = invalid["centers"][1]
    invalids = [("noninjective-centers", invalid, target)]
    invalid = deepcopy(binding["map"])
    invalid["anchors"][0] = invalid["anchors"][1]
    invalids.append(("wrong-anchor-map", invalid, target))
    missing = set(target)
    image = sum(1 << binding["map"]["centers"][v] for v in exact.kernel.bits(group["faces"][0]))
    missing.remove(image)
    invalids.append(("lost-paid-face", binding["map"], missing))
    for label, mapping, faces in invalids:
        try:
            check_map(25, B, group, mapping, faces, 2)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("invalid cross-order transfer accepted", label))
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    report = {"verified": True, "source_N": originalN, "B": B,
              "source_catalog_index": binding["index"], "source_group": group["id"],
              "source_groups_sha256": sha(grouppath), "source_bindings_sha256": sha(bindingpath),
              "source_catalog_sha256": sha(catalogpath), "source_receipt_sha256": sha(receiptpath),
              "source_replay_sha256": sha(replaypath), "source_tree_sha256": sha(treepath),
              "source_constants_sha256": sha(constantspath), "fresh_source_tree_replay": fresh,
              "extensions": extensions, "negative_controls_rejected": rejected,
              "exact_checker_sha256": sha(ROOT / "exact_graph.py"),
              "mapping_checker_sha256": sha(ROOT / "audit_streamed_hierarchy.py"),
              "force_kernel_sha256": sha(ROOT.parent / "round2-grouped/partial_force_exact.py"),
              "source_sha256": sha(Path(__file__)), "no_optimizer_imported": True,
              "global_optimality_proved": False,
              "scope": "three explicitly embedded exclusions; not a complete target catalogue"}
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Cross-order strict-force reuse PASS: explicit n23/24/25 extensions excluded;",
          "three invalid transfers rejected; no target-global claim", flush=True)


if __name__ == "__main__":
    main()
