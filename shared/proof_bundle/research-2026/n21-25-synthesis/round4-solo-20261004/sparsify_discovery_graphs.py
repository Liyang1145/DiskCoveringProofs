"""Reduce new discovery obstacles, re-proving each deletion on its own root.

This exports standalone strict theorems, not complete family coverage.
"""
from pathlib import Path
from collections import Counter
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--replay", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--count", type=int, default=32)
    ap.add_argument("--limit", type=int, default=301)
    args = ap.parse_args()
    snapshot, receipt, replay = map(read, (args.snapshot, args.receipt, args.replay))
    assert receipt["schema"] == "individually-paid-discovery-graphs-v1"
    assert receipt["snapshot_sha256"] == replay["snapshot_sha256"] == sha(args.snapshot)
    assert replay["verified"] and replay["receipt_sha256"] == sha(args.receipt)
    assert replay["source_sha256"] == sha(ROOT / "replay_collar_discovery.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert replay["no_optimizer_imported"]
    assert not args.output.exists() and args.count > 0 and args.limit > 0
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    assert constants["verified"] and constants["N"] == 25
    assert receipt["constants_sha256"] == replay["constants_sha256"] == sha(constants_path)
    parents = [row for row in receipt["outcomes"] if row["status"] == "excluded"][:args.count]
    assert parents
    args.output.mkdir(parents=True)
    codes, proofs, multiplicities = {}, {}, Counter()
    accepted_deletions = proposed_deletions = before_faces = after_faces = 0
    started = time.monotonic()

    def prove(code, centers):
        nodes, failure = make(14, centers, list(code), constants, args.limit, route_weak=True)
        if nodes is None:
            return None
        report = exact.verify(14, centers, list(code), nodes, constants)
        assert all(node["kind"] in ("EMPTY", "SPLIT", "DUAL") for node in nodes)
        return nodes, report

    with (args.output / "parent-maps.jsonl").open("x", encoding="utf8") as ledger:
        for index, parent in enumerate(parents):
            assert snapshot["weak_graphs"][parent["group"]]["faces"] == parent["faces"]
            remaining = list(parent["faces"])
            code, mapping = canonical(parent["centers"], 14, remaining, 1)
            theorem = prove(code, len(mapping["centers"]))
            assert theorem is not None
            before_faces += len(remaining)
            for remove in sorted(remaining, key=lambda m: ((m & ((1 << 14)-1)).bit_count(), m)):
                trial = [m for m in remaining if m != remove]
                if not trial:
                    continue
                trial_code, trial_map = canonical(parent["centers"], 14, trial, 1)
                proposed_deletions += 1
                candidate = prove(trial_code, len(trial_map["centers"]))
                if candidate is not None:
                    accepted_deletions += 1
                    remaining, code, mapping, theorem = trial, trial_code, trial_map, candidate
            validate(parent["centers"], 14, code, mapping, parent["faces"])
            gid = codes.setdefault(code, len(codes))
            multiplicities[gid] += 1
            proofs.setdefault(code, (len(mapping["centers"]), theorem))
            after_faces += len(code)
            ledger.write(json.dumps({
                "index": index, "group": gid, "parent_discovery_group": parent["group"],
                "parent_centers": parent["centers"], "parent_faces": parent["faces"],
                "remaining_faces_in_parent_labels": remaining, "map": mapping,
                "all_retained_deletions_have_fresh_whole_domain_proofs": True,
            }, separators=(",", ":"))+"\n")
            ledger.flush()
            print("New sparse obstacle", index+1, "->", len(codes), "distinct;",
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
            entry = json.loads(line)
            target.write(json.dumps({key: entry[key] for key in ("index", "group", "map")},
                                    separators=(",", ":"))+"\n")
    group_path = args.output / "GROUPS.json"
    group_path.write_text(json.dumps({
        "N": 25, "B": 14, "threshold": 1, "groups": groups,
        "group_count": len(groups), "selected_types": len(parents), "catalog_types": len(parents),
        "catalog_sha256": sha(args.snapshot), "bindings_file": bindings.name,
        "bindings_sha256": sha(bindings), "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": False, "parent_groups_sha256": None,
        "parent_proof_sha256": None, "not_a_complete_family": True,
        "members_are_discovery_graphs_not_actual_cover_types": True,
        "all_boundary_sites_preserved_by_implicit_anchor_rods": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    outcomes = []
    for group in groups:
        nodes, report = proofs[tuple(group["faces"])][1]
        treepath = args.output / f"group-{group['id']:07}.json.gz"
        with gzip.open(treepath, "xt", encoding="utf8") as stream:
            json.dump({
                "N": 25, "B": 14, "partial_centers": group["centers"], "faces": group["faces"],
                "nodes": nodes, "groups_sha256": sha(group_path),
                "constants_sha256": sha(constants_path), "radius_upper": constants["radius_upper"],
            }, stream, separators=(",", ":"))
        outcomes.append({"group": group["id"], "status": "excluded", **report,
                         "members": group["members"], "tree_sha256": sha(treepath)})
    (args.output / "SUMMARY.json").write_text(json.dumps({
        "N": 25, "B": 14, "groups_sha256": sha(group_path), "outcomes": outcomes,
        "excluded_groups": len(groups), "pending_groups": 0,
        "catalog_members_excluded": len(parents), "requested_groups_complete": True,
        "source_sha256": sha(Path(__file__)), "source_receipt_sha256": sha(args.receipt),
        "source_exact_replay_sha256": sha(args.replay),
        "parent_face_count": before_faces, "reduced_face_count": after_faces,
        "proposed_deletions": proposed_deletions, "accepted_deletions": accepted_deletions,
        "complete_family_coverage": False, "global_face_minimality_not_claimed": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
