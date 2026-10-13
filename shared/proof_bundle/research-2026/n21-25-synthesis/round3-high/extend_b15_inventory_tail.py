"""Bind the last 236 B15 adaptive groups to a fully audited 110500 prefix."""
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
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefix", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    prefix = read(args.prefix)
    assert prefix["verified"] and (prefix["N"], prefix["B"]) == (22, 15)
    assert prefix["source_sha256"] == sha(ROOT / "audit_b15_batch_inventory.py")
    assert prefix["attempted_adaptive_groups"] == prefix["paid_adaptive_groups"] == 110500
    assert prefix["pending_root_groups_not_paid"] == prefix["unattempted_root_groups"] == 236
    assert prefix["pending_attempted_groups"] == 0
    groupspath = EV / "n22-B15-full-resume1/GROUPS.json"
    rootpath = EV / "n22-B15-full-root-resume1/SUMMARY.json"
    groups, root = read(groupspath), read(rootpath)
    digest = sha(groupspath)
    assert prefix["groups_sha256"] == root["groups_sha256"] == digest
    assert prefix["root_receipt_sha256"] == sha(rootpath)
    assert prefix["root_replay_sha256"] == sha(EV / "n22-B15-full-root-replay-resume1.json")
    unpaid = {row["group"] for row in root["outcomes"] if row["status"] == "pending"}
    assert len(unpaid) == 110736
    seen = set()
    for batch in prefix["batches"]:
        receiptpath, replaypath = ROOT / batch["receipt_path"], ROOT / batch["replay_path"]
        assert sha(receiptpath) == batch["receipt_sha256"]
        assert sha(replaypath) == batch["replay_sha256"]
        receipt = read(receiptpath)
        assert receipt["groups_sha256"] == digest
        ids = [row["group"] for row in receipt["outcomes"]]
        assert len(ids) == 500 and len(set(ids)) == 500
        assert set(ids) <= unpaid and not seen & set(ids)
        assert all(row["status"] == "excluded" for row in receipt["outcomes"])
        seen.update(ids)
    assert len(seen) == 110500
    folder = EV / "n22-B15-full-adaptive-after110500-next236-resume1"
    receiptpath = folder / "SUMMARY.json"
    replaypath = EV / "n22-B15-full-adaptive-after110500-next236-replay-resume1.json"
    receipt, replay = read(receiptpath), read(replaypath)
    assert receipt["groups_sha256"] == replay["groups_sha256"] == digest
    assert replay["verified"] and replay["partial_receipt_only"]
    assert replay["source_sha256"] == sha(ROOT / "replay_partial_groups.py")
    assert replay["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
    assert replay["receipt_sha256"] == sha(receiptpath)
    outcomes = receipt["outcomes"]
    ids = [row["group"] for row in outcomes]
    assert len(ids) == 236 and ids == sorted(set(ids))
    assert set(ids) == unpaid-seen
    assert all(row["status"] == "excluded" for row in outcomes)
    counts = Counter()
    for row in outcomes:
        gid = row["group"]
        assert row["members"] == groups["groups"][gid]["members"] == 1
        assert row["verified"] and F(row["minimum_force_margin"]) > 0
        assert sha(folder / f"group-{gid:07}.json.gz") == row["tree_sha256"]
        counts.update(row["counts"])
    assert receipt["excluded_groups"] == replay["exact_excluded_groups_replayed"] == 236
    assert receipt["pending_groups"] == replay["pending_groups_in_receipt"] == 0
    assert receipt["catalog_members_excluded"] == replay["associated_member_count"] == 236
    assert dict(counts) == replay["node_counts"]
    assert F(replay["minimum_force_margin"]) == min(F(row["minimum_force_margin"]) for row in outcomes)
    report = dict(prefix)
    report.update(attempted_adaptive_groups=110736, paid_adaptive_groups=110736,
                  pending_root_groups_not_paid=0, unattempted_root_groups=0,
                  root_plus_adaptive_strict_exclusion_groups=315303,
                  prefix_inventory_path=args.prefix.resolve().relative_to(ROOT.resolve()).as_posix(),
                  prefix_inventory_sha256=sha(args.prefix),
                  source_sha256=sha(Path(__file__)),
                  adaptive_inventory_complete=True)
    report["batches"] = list(prefix["batches"])+[{
        "receipt_path": receiptpath.relative_to(ROOT).as_posix(),
        "receipt_sha256": sha(receiptpath),
        "replay_path": replaypath.relative_to(ROOT).as_posix(),
        "replay_sha256": sha(replaypath), "attempted": 236, "paid": 236, "members": 236}]
    report["minimum_adaptive_margin"] = str(min(F(prefix["minimum_adaptive_margin"]),
                                                F(replay["minimum_force_margin"])))
    totalcounts = Counter(prefix["node_counts"])
    totalcounts.update(counts)
    report["node_counts"] = dict(totalcounts)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("B15 full adaptive inventory PASS:", 110736, "all disjoint paid; no pending", flush=True)


if __name__ == "__main__":
    main()
