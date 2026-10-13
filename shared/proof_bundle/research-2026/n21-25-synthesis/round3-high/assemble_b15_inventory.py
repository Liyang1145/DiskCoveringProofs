"""Assemble only hash-bound B15 receipts listed in an audited inventory.

Calls the existing merge in-process to avoid Windows command-line limits
for hundreds of receipt arguments. Merge remains organizational: a fresh
complete exact replay and original hierarchy audit MUST follow.
"""
from pathlib import Path
import argparse
import json
import sys
import combine_partial_receipts as combine
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
EV = ROOT / "evidence"
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"),
                      object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inventory", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    inventory = read(args.inventory)
    assert inventory["verified"] and (inventory["N"], inventory["B"]) == (22, 15)
    if inventory.get("adaptive_inventory_complete"):
        assert inventory["source_sha256"] == sha(ROOT / "extend_b15_inventory_tail.py")
        prefixpath = (ROOT / inventory["prefix_inventory_path"]).resolve()
        assert prefixpath.is_relative_to(ROOT.resolve())
        assert sha(prefixpath) == inventory["prefix_inventory_sha256"]
        prefix = read(prefixpath)
        assert prefix["source_sha256"] == sha(ROOT / "audit_b15_batch_inventory.py")
        assert prefix["verified"]
    else:
        assert inventory["source_sha256"] == sha(ROOT / "audit_b15_batch_inventory.py")
    assert inventory["all_component_replays_hash_bound"]
    assert inventory["strict_certificate_byte_hashes_checked"]
    assert inventory["independent_disjoint_group_inventory_checked"]
    rootpath = EV / "n22-B15-full-root-resume1/SUMMARY.json"
    rootreplaypath = EV / "n22-B15-full-root-replay-resume1.json"
    grouppath = EV / "n22-B15-full-resume1/GROUPS.json"
    assert inventory["groups_sha256"] == sha(grouppath)
    assert inventory["root_receipt_sha256"] == sha(rootpath)
    assert inventory["root_replay_sha256"] == sha(rootreplaypath)
    command = ["combine_partial_receipts.py", "--groups", str(grouppath),
               "--root", str(rootpath), "--output", str(args.output)]
    attempted = paid = 0
    for row in inventory["batches"]:
        receiptpath = (ROOT / row["receipt_path"]).resolve()
        replaypath = (ROOT / row["replay_path"]).resolve()
        assert receiptpath.is_relative_to(ROOT.resolve())
        assert replaypath.is_relative_to(ROOT.resolve())
        assert sha(receiptpath) == row["receipt_sha256"]
        assert sha(replaypath) == row["replay_sha256"]
        attempted += row["attempted"]
        paid += row["paid"]
        command.extend(("--refinement", str(receiptpath)))
    assert attempted == inventory["attempted_adaptive_groups"]
    assert paid == inventory["paid_adaptive_groups"]
    old = sys.argv
    try:
        sys.argv = command
        combine.main()
    finally:
        sys.argv = old
    result = read(args.output)
    assert result["groups_sha256"] == inventory["groups_sha256"]
    assert result["excluded_groups"] == inventory["root_plus_adaptive_strict_exclusion_groups"]
    assert result["pending_groups"] == inventory["pending_root_groups_not_paid"]
    print("B15 audited-inventory assembly consistent; exact full replay and maps still required",
          flush=True)


if __name__ == "__main__":
    main()
