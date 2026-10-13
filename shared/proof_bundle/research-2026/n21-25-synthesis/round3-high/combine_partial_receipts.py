"""Combine a COMPLETE root ledger with disjoint partial adaptive ledgers.

Unprocessed root-pending groups remain pending. No optimizer or mathematical
checker is imported: standalone force replay and transfer audits remain
mandatory. Unlike combine_receipts.py this does not require every pending
root group to have already been attempted by an adaptive producer.
"""
from pathlib import Path
import argparse
import json
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def merge(groups, root, refinements):
    assert (root["N"], root["B"]) == (groups["N"], groups["B"])
    old = {row["group"]: row for row in root["outcomes"]}
    assert len(old) == len(root["outcomes"]) == groups["group_count"]
    assert set(old) == set(range(groups["group_count"]))
    assert all(row["status"] in ("excluded", "pending") for row in old.values())
    new = {}
    for index, receipt in enumerate(refinements):
        assert (receipt["N"], receipt["B"]) == (groups["N"], groups["B"])
        assert receipt["groups_sha256"] == root["groups_sha256"]
        local = set()
        for row in receipt["outcomes"]:
            gid = row["group"]
            assert type(gid) is int and gid in old and old[gid]["status"] == "pending"
            assert gid not in local and gid not in new
            assert row["status"] in ("excluded", "pending")
            local.add(gid)
            new[gid] = (row, index)
    return old, new


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--root", type=Path, required=True)
    ap.add_argument("--refinement", type=Path, action="append", required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    groups, root = read(args.groups), read(args.root)
    digest = sha(args.groups)
    assert root["groups_sha256"] == digest
    refinements = [read(path) for path in args.refinement]
    old, new = merge(groups, root, refinements)
    outcomes = []
    for gid in range(groups["group_count"]):
        row, source = new[gid] if gid in new else (old[gid], None)
        row = dict(row)
        if row["status"] == "excluded":
            receiptpath = args.root if source is None else args.refinement[source]
            target = (receiptpath.parent / row["certificate_path_relative_to_receipt"]
                      if "certificate_path_relative_to_receipt" in row else
                      receiptpath.parent / f"group-{gid:07}.json.gz")
            assert sha(target) == row["tree_sha256"]
            row["certificate_path_relative_to_receipt"] = target.resolve().relative_to(
                args.output.parent.resolve()).as_posix()
        outcomes.append(row)
    report = {"N": groups["N"], "B": groups["B"], "groups_sha256": digest,
              "outcomes": outcomes, "root_receipt_sha256": sha(args.root),
              "refinement_receipts_sha256": [sha(p) for p in args.refinement],
              "adaptive_groups_observed": len(new),
              "excluded_groups": sum(r["status"] == "excluded" for r in outcomes),
              "pending_groups": sum(r["status"] == "pending" for r in outcomes),
              "catalog_members_excluded": sum(r.get("members", 0) for r in outcomes
                                              if r["status"] == "excluded"),
              "fresh_exact_acceptance": False, "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__))}
    args.output.write_text(json.dumps(report, separators=(",", ":")), encoding="utf8")
    print("Complete root + partial adaptive untrusted merge", report["excluded_groups"],
          "excluded groups,", report["pending_groups"], "pending", flush=True)


if __name__ == "__main__":
    main()
