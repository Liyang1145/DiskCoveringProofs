"""Bound a contiguous B15 adaptive receipt inventory against complete root.

This audits the disjoint certificate/replay chain, not new force mathematics
and not embeddings. It does not trust the batch runner's printed count.
Only completed, content-bound replay reports are paid. Active tail directories
are excluded by --through. Frozen inputs are never written.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import json
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
EV = ROOT / "evidence"
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"),
                      object_pairs_hook=no_duplicate_keys)


def batch_names(through):
    assert through >= 3000 and through % 500 == 0
    names = ["n22-B15-full-adaptive500",
             "n22-B15-full-adaptive-next500",
             "n22-B15-full-adaptive-prefix75000-next500",
             "n22-B15-full-adaptive-prefix100000-next500",
             "n22-B15-full-adaptive-prefix130000-next500",
             "n22-B15-full-adaptive-prefix160000-next500"]
    names += [f"n22-B15-full-adaptive-after{k}-next500"
              for k in range(3000, through, 500)]
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--through", type=int, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    grouppath = EV / "n22-B15-full-resume1/GROUPS.json"
    rootpath = EV / "n22-B15-full-root-resume1/SUMMARY.json"
    rootreplaypath = EV / "n22-B15-full-root-replay-resume1.json"
    groups, root, rootreplay = map(read, (grouppath, rootpath, rootreplaypath))
    digest = sha(grouppath)
    assert (groups["N"], groups["B"], groups["threshold"]) == (22, 15, 0)
    assert groups["full_selected_catalog_scanned"]
    assert (root["N"], root["B"], root["groups_sha256"]) == (22, 15, digest)
    assert rootreplay["verified"] and rootreplay["receipt_sha256"] == sha(rootpath)
    assert rootreplay["groups_sha256"] == digest
    assert rootreplay["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
    assert rootreplay["source_sha256"] == sha(ROOT / "replay_group_stage.py")
    assert F(rootreplay["minimum_force_margin"]) > 0
    old = {row["group"]: row for row in root["outcomes"]}
    assert len(old) == len(root["outcomes"]) == groups["group_count"]
    assert set(old) == set(range(groups["group_count"]))
    assert root["requested_groups_complete"]
    assert root["excluded_groups"] == rootreplay["exact_groups_replayed"] == 204567
    assert root["pending_groups"] == rootreplay["pending_groups"] == 110736
    unpaid = {gid for gid, row in old.items() if row["status"] == "pending"}
    assert len(unpaid) == 110736
    occupied, paid, reports = set(), set(), []
    counts = Counter()
    minimum = None
    for name in batch_names(args.through):
        folder = EV / (name+"-resume1")
        receiptpath = folder / "SUMMARY.json"
        replaypath = EV / (name+"-replay-resume1.json")
        receipt, replay = read(receiptpath), read(replaypath)
        assert (receipt["N"], receipt["B"], receipt["groups_sha256"]) == (22, 15, digest)
        assert (replay["N"], replay["B"], replay["groups_sha256"]) == (22, 15, digest)
        assert replay["verified"] and replay["partial_receipt_only"]
        assert replay["source_sha256"] == sha(ROOT / "replay_partial_groups.py")
        assert replay["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
        assert replay["receipt_sha256"] == sha(receiptpath)
        outcomes = receipt["outcomes"]
        ids = [row["group"] for row in outcomes]
        assert len(ids) == 500 and ids == sorted(set(ids))
        assert all(type(gid) is int and gid in unpaid and gid not in occupied for gid in ids)
        occupied.update(ids)
        excluded = set()
        members = 0
        localcounts = Counter()
        for row in outcomes:
            gid = row["group"]
            assert row["status"] in ("excluded", "pending")
            if row["status"] != "excluded":
                continue
            group = groups["groups"][gid]
            assert row["members"] == group["members"] == 1
            assert row["verified"] and row["nodes"] > 0
            assert F(row["minimum_force_margin"]) > 0
            path = folder / f"group-{gid:07}.json.gz"
            assert sha(path) == row["tree_sha256"]
            excluded.add(gid)
            members += row["members"]
            localcounts.update(row["counts"])
        assert len(excluded) == receipt["excluded_groups"] == replay["exact_excluded_groups_replayed"]
        assert len(ids)-len(excluded) == receipt["pending_groups"] == replay["pending_groups_in_receipt"]
        assert members == receipt["catalog_members_excluded"] == replay["associated_member_count"]
        assert dict(localcounts) == replay["node_counts"]
        if excluded:
            margin = F(replay["minimum_force_margin"])
            assert margin == min(F(row["minimum_force_margin"])
                                 for row in outcomes if row["status"] == "excluded")
            minimum = margin if minimum is None else min(minimum, margin)
        paid.update(excluded)
        counts.update(localcounts)
        reports.append({"receipt_path": receiptpath.relative_to(ROOT).as_posix(),
                        "receipt_sha256": sha(receiptpath),
                        "replay_path": replaypath.relative_to(ROOT).as_posix(),
                        "replay_sha256": sha(replaypath),
                        "attempted": len(ids), "paid": len(excluded), "members": members})
        if len(reports) % 20 == 0:
            print("B15 independently bound batches", len(reports),
                  "attempted", len(occupied), "paid", len(paid), flush=True)
    assert len(occupied) == args.through
    report = {"verified": True, "N": 22, "B": 15,
              "groups_sha256": digest, "root_receipt_sha256": sha(rootpath),
              "root_replay_sha256": sha(rootreplaypath),
              "attempted_adaptive_groups": len(occupied),
              "paid_adaptive_groups": len(paid),
              "pending_root_groups_not_paid": len(unpaid-paid),
              "pending_attempted_groups": len(occupied-paid),
              "unattempted_root_groups": len(unpaid-occupied),
              "root_plus_adaptive_strict_exclusion_groups": 204567+len(paid),
              "minimum_adaptive_margin": None if minimum is None else str(minimum),
              "node_counts": dict(counts), "batches": reports,
              "all_component_replays_hash_bound": True,
              "strict_certificate_byte_hashes_checked": True,
              "independent_disjoint_group_inventory_checked": True,
              "force_math_not_recomputed_here": True,
              "embeddings_not_checked_here": True,
              "global_optimality_proved": False, "source_sha256": sha(Path(__file__))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("B15 complete adaptive prefix inventory PASS:", len(occupied), "attempted;",
          len(paid), "paid;", len(unpaid-paid), "root groups remain", flush=True)


if __name__ == "__main__":
    main()
