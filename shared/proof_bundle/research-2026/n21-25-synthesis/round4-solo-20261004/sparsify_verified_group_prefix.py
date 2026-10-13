"""Standalone sparse strict theorems from an independently paid finite prefix.

The deletion/reproof algorithm is the frozen sparsify_family_discovery algorithm.
Only its input adapter and proof cache are new. Neither a prefix nor its row ids
becomes a complete family premise. No running search input is changed.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from probe_groups import make
from group_catalog import canonical, validate
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"),
                      object_pairs_hook=no_duplicate_keys)


def source_gate(directory):
    """Recheck all finite source trees; do not accept a status flag as proof."""
    group_path = directory / "GROUPS.json"
    receipt_path = directory / "PROPOSALS/SUMMARY.json"
    replay_path = directory / "EXACT-REPLAY.json"
    verified_path = directory / "VERIFIED.json"
    data, receipt, replay, verified = map(
        read, (group_path, receipt_path, replay_path, verified_path))
    B = data["B"]
    assert (data["N"], data["threshold"]) == (25, 1) and B in (15, 16, 17)
    assert data["finite_selection_from_closed_slab_not_whole_family"]
    assert not data["full_selected_catalog_scanned"]
    assert verified["verified"]
    assert verified["schema"] == "finite-closed-origin-slab-prefix-exact-payments-v1"
    assert verified["not_a_complete_competitor_family_or_union"]
    assert verified["source_sha256"] == sha(ROOT / "prove_closed_slab_prefix.py")
    assert verified["groups_sha256"] == replay["groups_sha256"] == receipt["groups_sha256"] == sha(group_path)
    assert verified["receipt_sha256"] == replay["receipt_sha256"] == sha(receipt_path)
    assert verified["exact_replay_sha256"] == sha(replay_path)
    assert replay["verified"] and replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert replay["embedding_transfers_not_verified_here"]
    assert (receipt["N"], receipt["B"]) == (replay["N"], replay["B"]) == (25, B)
    assert (verified["N"], verified["B"]) == (25, B)
    assert receipt["requested_groups_complete"]
    count = data["group_count"]
    assert count == len(data["groups"]) == len(receipt["outcomes"]) > 0
    assert receipt["pending_groups"] == replay["pending_groups"] == verified["pending_rows"] == 0
    assert count == receipt["excluded_groups"] == replay["exact_groups_replayed"] == verified["strictly_excluded"]
    assert count == data["selected_types"] == verified["selected_source_rows"]
    assert count == receipt["catalog_members_excluded"] == replay["associated_member_count"]
    assert [g["id"] for g in data["groups"]] == list(range(count))
    assert [r["group"] for r in receipt["outcomes"]] == list(range(count))
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    assert constants["verified"] and constants["N"] == 25
    assert F(constants["radius_upper"]) == F(239146311738101, 10**15)
    bindings = directory / data["bindings_file"]
    assert sha(bindings) == data["bindings_sha256"] == replay["bindings_sha256"]
    source_slab = (ROOT / data["source_slab_relative_to_workspace"]).resolve()
    assert source_slab.is_relative_to(ROOT)
    assert sha(source_slab) == data["catalog_sha256"] == verified["source_slab_sha256"]
    files = {}

    def bind(path):
        path = path.resolve()
        assert path.is_relative_to(ROOT.parent)
        files[path.relative_to(ROOT.parent).as_posix()] = sha(path)

    for path in (group_path, receipt_path, replay_path, verified_path, bindings,
                 source_slab, constants_path, Path(__file__),
                 ROOT / "sparsify_family_discovery.py",
                 ROOT / "prove_closed_slab_prefix.py",
                 HIGH / "exact_graph.py", HIGH / "group_catalog.py",
                 HIGH / "probe_groups.py", HIGH / "replay_group_stage.py",
                 HIGH / "stream_catalog.py", HIGH / "candidate_domain.py"):
        bind(path)
    with bindings.open(encoding="ascii") as stream:
        rows = [json.loads(line, object_pairs_hook=no_duplicate_keys) for line in stream]
    assert len(rows) == count
    for index, (group, outcome, binding) in enumerate(zip(data["groups"], receipt["outcomes"], rows)):
        assert binding["index"] == binding["group"] == group["id"] == outcome["group"] == index
        centers, faces = group["centers"], group["faces"]
        assert B <= centers < 25 and group["members"] == outcome["members"] == 1
        assert faces == sorted(set(faces)) and faces
        assert all(type(mask) is int and 0 < mask < 1 << centers
                   and mask.bit_count() == 3 and mask & ((1 << B)-1) for mask in faces)
        code, mapping = canonical(centers, B, faces, 1)
        assert list(code) == faces and len(mapping["centers"]) == centers
        validate(centers, B, faces, binding["map"], faces)
        assert outcome["status"] == "excluded"
        tree_path = receipt_path.parent / f"group-{index:07}.json.gz"
        assert sha(tree_path) == outcome["tree_sha256"]
        with gzip.open(tree_path, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (25, B, centers, faces)
        assert tree["groups_sha256"] == sha(group_path)
        assert tree["constants_sha256"] == sha(constants_path)
        assert tree["radius_upper"] == constants["radius_upper"]
        assert all(n["kind"] in ("EMPTY", "SPLIT", "DUAL") for n in tree["nodes"])
        report = exact.verify(B, centers, faces, tree["nodes"], constants)
        assert report["nodes"] == outcome["nodes"] and report["counts"] == outcome["counts"]
        assert F(report["minimum_force_margin"]) > 0
        bind(tree_path)
    return data, constants, constants_path, files


def unchanged(files):
    for relative, digest in files.items():
        assert sha(ROOT.parent / relative) == digest, relative


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefix", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--count", type=int, default=64)
    ap.add_argument("--limit", type=int, default=1)
    args = ap.parse_args()
    args.prefix, args.output = args.prefix.resolve(), args.output.resolve()
    assert args.prefix.is_relative_to(ROOT) and args.output.is_relative_to(ROOT)
    assert not args.output.exists() and args.count > 0 and args.limit > 0
    data, constants, constants_path, files = source_gate(args.prefix)
    B = data["B"]
    parents = data["groups"][:args.count]
    assert len(parents) == args.count
    args.output.mkdir()
    codes, proofs, multiplicities, cache = {}, {}, Counter(), {}
    accepted_deletions = proposed_deletions = before_faces = after_faces = 0
    cache_hits = 0
    started = time.monotonic()

    def prove(code, centers):
        nonlocal cache_hits
        key = (centers, code)
        if key in cache:
            cache_hits += 1
            return cache[key]
        nodes, failure = make(B, centers, list(code), constants, args.limit, route_weak=True)
        if nodes is None:
            cache[key] = None
            return None
        report = exact.verify(B, centers, list(code), nodes, constants)
        assert all(node["kind"] in ("EMPTY", "SPLIT", "DUAL") for node in nodes)
        assert F(report["minimum_force_margin"]) > 0
        cache[key] = (nodes, report)
        return cache[key]

    with (args.output / "parent-maps.jsonl").open("x", encoding="utf8") as ledger:
        for index, parent in enumerate(parents):
            remaining = list(parent["faces"])
            code, mapping = canonical(parent["centers"], B, remaining, 1)
            theorem = prove(code, len(mapping["centers"]))
            assert theorem is not None
            before_faces += len(remaining)
            for remove in sorted(remaining, key=lambda m: ((m & ((1 << B)-1)).bit_count(), m)):
                trial = [m for m in remaining if m != remove]
                if not trial:
                    continue
                trial_code, trial_map = canonical(parent["centers"], B, trial, 1)
                proposed_deletions += 1
                candidate = prove(trial_code, len(trial_map["centers"]))
                if candidate is not None:
                    accepted_deletions += 1
                    remaining, code, mapping, theorem = trial, trial_code, trial_map, candidate
            validate(parent["centers"], B, code, mapping, parent["faces"])
            gid = codes.setdefault(code, len(codes))
            multiplicities[gid] += 1
            proofs.setdefault(code, (len(mapping["centers"]), theorem))
            after_faces += len(code)
            ledger.write(json.dumps({
                "index": index, "group": gid, "parent_prefix_group": parent["id"],
                "parent_centers": parent["centers"], "parent_faces": parent["faces"],
                "remaining_faces_in_parent_labels": remaining, "map": mapping,
                "all_retained_deletions_have_own_whole_domain_strict_proofs": True,
            }, separators=(",", ":"))+"\n")
            ledger.flush()
            print("Paid-prefix sparse obstacle", index+1, "->", len(codes), "distinct;",
                  len(parent["faces"]), "->", len(code), "faces;",
                  "seconds", round(time.monotonic()-started, 2), flush=True)
    groups = [None]*len(codes)
    for code, gid in codes.items():
        centers, theorem = proofs[code]
        groups[gid] = {"id": gid, "centers": centers, "faces": list(code),
                       "members": multiplicities[gid]}
    bindings = args.output / "bindings.jsonl"
    with (args.output / "parent-maps.jsonl").open(encoding="utf8") as source, bindings.open("x", encoding="utf8") as target:
        for line in source:
            entry = json.loads(line, object_pairs_hook=no_duplicate_keys)
            target.write(json.dumps({key: entry[key] for key in ("index", "group", "map")},
                                    separators=(",", ":"))+"\n")
    group_path = args.output / "GROUPS.json"
    group_path.write_text(json.dumps({
        "N": 25, "B": B, "threshold": 1, "groups": groups, "group_count": len(groups),
        "selected_types": len(parents), "catalog_types": len(parents),
        "catalog_sha256": sha(args.prefix / "GROUPS.json"),
        "bindings_file": bindings.name, "bindings_sha256": sha(bindings),
        "verified_embeddings_during_generation": True, "full_selected_catalog_scanned": False,
        "not_a_complete_family": True, "parents_are_finite_weak_graph_samples": True,
        "all_boundary_sites_preserved_by_implicit_anchor_rods": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    outcomes = []
    for group in groups:
        nodes, report = proofs[tuple(group["faces"])][1]
        treepath = args.output / f"group-{group['id']:07}.json.gz"
        with gzip.open(treepath, "xt", encoding="utf8") as stream:
            json.dump({
                "N": 25, "B": B, "partial_centers": group["centers"], "faces": group["faces"],
                "nodes": nodes, "groups_sha256": sha(group_path),
                "constants_sha256": sha(constants_path), "radius_upper": constants["radius_upper"],
            }, stream, separators=(",", ":"))
        outcomes.append({"group": group["id"], "status": "excluded", **report,
                         "members": group["members"], "tree_sha256": sha(treepath)})
    unchanged(files)
    (args.output / "SUMMARY.json").write_text(json.dumps({
        "N": 25, "B": B, "groups_sha256": sha(group_path), "outcomes": outcomes,
        "excluded_groups": len(groups), "pending_groups": 0,
        "catalog_members_excluded": len(parents), "requested_groups_complete": True,
        "source_sha256": sha(Path(__file__)), "source_files": files,
        "source_prefix_relative_to_round4": args.prefix.relative_to(ROOT).as_posix(),
        "source_prefix_groups_sha256": sha(args.prefix / "GROUPS.json"),
        "parent_maps_sha256": sha(args.output / "parent-maps.jsonl"),
        "parent_face_count": before_faces, "reduced_face_count": after_faces,
        "proposed_deletions": proposed_deletions, "accepted_deletions": accepted_deletions,
        "same_canonical_whole_domain_proof_cache_hits": cache_hits,
        "complete_family_coverage": False, "global_face_minimality_not_claimed": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
