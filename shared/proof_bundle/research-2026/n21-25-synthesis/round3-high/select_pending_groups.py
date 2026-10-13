"""Create an untrusted pending-group routing receipt from a complete ledger."""
from pathlib import Path
import argparse
import json
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--exclude", type=int, action="append", default=[])
    args = ap.parse_args()
    assert not args.output.exists()
    source = json.loads(args.source.read_text(encoding="utf8"),
                        object_pairs_hook=no_duplicate_keys)
    excluded = set(args.exclude)
    outcomes = [{"group": row["group"], "status": "pending"}
                for row in source["outcomes"]
                if row["status"] == "pending" and row["group"] not in excluded]
    ids = [row["group"] for row in outcomes]
    assert ids == sorted(set(ids))
    report = {"N": source["N"], "B": source["B"],
              "groups_sha256": source["groups_sha256"], "outcomes": outcomes,
              "omitted_protected_groups": sorted(excluded),
              "source_receipt_sha256": sha(args.source), "routing_only": True,
              "mathematical_acceptance": False, "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, separators=(",", ":")), encoding="utf8")
    print("Pending routing receipt", len(outcomes), "groups; protected", sorted(excluded), flush=True)


if __name__ == "__main__":
    main()
