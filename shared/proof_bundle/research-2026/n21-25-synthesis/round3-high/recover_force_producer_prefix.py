"""Preserve a terminated producer's complete ledger prefix; route only unseen.

This is NOT mathematical acceptance. Every preserved tree still needs fresh
exact replay, and a suffix remains unpaid until final disjoint-map auditing.
"""
from pathlib import Path
import argparse
import json
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--producer", type=Path, required=True)
    ap.add_argument("--prefix-receipt", type=Path, required=True)
    ap.add_argument("--routing", type=Path, required=True)
    args = ap.parse_args()
    assert not args.prefix_receipt.exists() and not args.routing.exists()
    assert args.prefix_receipt.parent.resolve() == args.producer.resolve()
    groups = json.loads(args.groups.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)
    rows = []
    tail_not_accepted = False
    ledger = args.producer / "outcomes.jsonl"
    with ledger.open(encoding="utf8") as stream:
        for line in stream:
            if not line.endswith("\n"):
                tail_not_accepted = True
                break
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert row["group"] == len(rows)
            assert row["status"] in ("excluded", "pending")
            if row["status"] == "excluded":
                path = args.producer / f"group-{row['group']:07}.json.gz"
                assert path.is_file()
                # Byte checks are useful provenance, not exact tree math.
                assert sha(path) == row["tree_sha256"], ("damaged prefix tree", row["group"])
                assert row["members"] == groups["groups"][row["group"]]["members"]
            rows.append(row)
            if len(rows) % 10000 == 0:
                print("Terminated force ledger prefix byte-bound", len(rows), flush=True)
    assert rows and len(rows) <= groups["group_count"]
    paid = sum(row["status"] == "excluded" for row in rows)
    members = sum(row.get("members", 0) for row in rows if row["status"] == "excluded")
    digest = sha(args.groups)
    observed = len(rows)
    full_ledger = rows + [{"group": gid, "status": "pending", "not_attempted_or_not_safely_written": True}
                          for gid in range(observed, groups["group_count"])]
    receipt = {"N": groups["N"], "B": groups["B"], "groups_sha256": digest,
               "outcomes": full_ledger, "excluded_groups": paid,
               "pending_groups": groups["group_count"]-paid, "catalog_members_excluded": members,
               "requested_groups_complete": False,
               "observed_complete_ledger_prefix": observed,
               "producer_terminated_on_disk_full": True,
               "ledger_sha256": sha(ledger), "incomplete_tail_not_accepted": tail_not_accepted,
               "unobserved_suffix_not_certified": True,
               "byte_hashes_verified_but_mathematical_acceptance_not_done": True,
               "global_optimality_proved": False, "source_sha256": sha(Path(__file__))}
    args.prefix_receipt.write_text(json.dumps(receipt, separators=(",", ":")), encoding="utf8")
    # Existing pending prefix nodes remain paid-by-none too, even if none
    # currently occurs. Do not omit them from future work.
    pending = [row["group"] for row in rows if row["status"] == "pending"]
    pending += list(range(len(rows), groups["group_count"]))
    routing = {"N": groups["N"], "B": groups["B"], "groups_sha256": digest,
               "outcomes": [{"group": gid, "status": "pending"} for gid in pending],
               "preserved_prefix_groups": len(rows), "total_groups": groups["group_count"],
               "prefix_receipt_sha256": sha(args.prefix_receipt),
               "not_a_complete_ledger": True, "mathematical_acceptance": False,
               "global_optimality_proved": False, "source_sha256": sha(Path(__file__))}
    args.routing.write_text(json.dumps(routing, separators=(",", ":")), encoding="utf8")
    print("Terminated producer complete byte-bound prefix preserved:", len(rows),
          "groups;", len(pending), "unpaid groups routed; fresh math replay still required", flush=True)


if __name__ == "__main__":
    main()
