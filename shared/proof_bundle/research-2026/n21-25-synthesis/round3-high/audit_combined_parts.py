"""Audit a complete-root + disjoint adaptive-part receipt merge.

Math acceptance is inherited only from independently replayed component
reports. This script checks that the final ledger is exactly their disjoint
union, with no status or member-count drift.
"""
from pathlib import Path
import argparse
import json
from collections import Counter
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--combined", type=Path, required=True)
    ap.add_argument("--root", type=Path, required=True)
    ap.add_argument("--root-replay", type=Path, required=True)
    ap.add_argument("--part", nargs=2, action="append", required=True,
                    metavar=("RECEIPT", "REPLAY"))
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    groups, combined, root, rootreplay = map(read, (args.groups, args.combined,
                                                      args.root, args.root_replay))
    digest = sha(args.groups)
    assert combined["groups_sha256"] == root["groups_sha256"] == digest
    assert (groups["N"], groups["B"]) == (combined["N"], combined["B"])
    expected = {row["group"]: row for row in root["outcomes"]}
    assert len(expected) == groups["group_count"] == len(root["outcomes"])
    assert rootreplay["verified"] and rootreplay["groups_sha256"] == digest
    assert rootreplay["receipt_sha256"] == sha(args.root)
    root_excluded = {row["group"] for row in root["outcomes"] if row["status"] == "excluded"}
    assert root_excluded == {row["group"] for row in combined["outcomes"]
                             if row["group"] in root_excluded}
    parts = []
    adaptive_excluded = set()
    adaptive_members = 0
    for receiptpath, replaypath in args.part:
        receipt, replay = read(Path(receiptpath)), read(Path(replaypath))
        assert receipt["groups_sha256"] == digest and replay["groups_sha256"] == digest
        assert replay["verified"] and replay["receipt_sha256"] == sha(Path(receiptpath))
        ids = {row["group"] for row in receipt["outcomes"]}
        assert ids and not ids & root_excluded and not ids & adaptive_excluded
        assert all(expected[gid]["status"] == "pending" for gid in ids)
        excluded = {row["group"] for row in receipt["outcomes"] if row["status"] == "excluded"}
        assert excluded <= ids and excluded.isdisjoint(adaptive_excluded)
        assert replay["exact_excluded_groups_replayed"] == len(excluded)
        assert replay["associated_member_count"] == receipt["catalog_members_excluded"]
        assert replay["source_sha256"] == sha(ROOT / "replay_partial_groups.py")
        adaptive_excluded |= excluded
        adaptive_members += replay["associated_member_count"]
        parts.append({"receipt_sha256": sha(Path(receiptpath)),
                      "replay_sha256": sha(Path(replaypath)),
                      "observed_groups": len(ids), "excluded_groups": len(excluded),
                      "associated_members": replay["associated_member_count"]})
    outcomes = {row["group"]: row for row in combined["outcomes"]}
    assert set(outcomes) == set(expected)
    assert {gid for gid, row in outcomes.items() if row["status"] == "excluded"} == root_excluded | adaptive_excluded
    assert root_excluded.isdisjoint(adaptive_excluded)
    assert combined["excluded_groups"] == len(root_excluded)+len(adaptive_excluded)
    assert combined["pending_groups"] == groups["group_count"]-combined["excluded_groups"]
    assert combined["catalog_members_excluded"] == sum(
        groups["groups"][gid]["members"] for gid in root_excluded | adaptive_excluded)
    assert combined["root_receipt_sha256"] == sha(args.root)
    report = {"verified": True, "N": groups["N"], "B": groups["B"],
              "groups_sha256": digest, "combined_receipt_sha256": sha(args.combined),
              "root_replay_sha256": sha(args.root_replay),
              "root_excluded_groups": len(root_excluded),
              "adaptive_excluded_groups": len(adaptive_excluded),
              "strict_excluded_groups": combined["excluded_groups"],
              "pending_groups": combined["pending_groups"],
              "associated_member_count": combined["catalog_members_excluded"],
              "component_adaptive_members": adaptive_members, "parts": parts,
              "disjoint_component_union_verified": True,
              "all_component_math_replayed": True,
              "embedding_transfers_not_verified_here": True,
              "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Combined component receipt partition PASS:",
          report["strict_excluded_groups"], "excluded,", report["pending_groups"], "pending", flush=True)


if __name__ == "__main__":
    main()
