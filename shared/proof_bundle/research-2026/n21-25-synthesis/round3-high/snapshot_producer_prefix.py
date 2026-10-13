"""Copy a finished producer prefix for untrusted proposal routing only.

Does not interrupt or restart the live producer. Does not pay any certificate,
and does not infer anything about the unobserved suffix.
"""
from pathlib import Path
import argparse
import json
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--ledger", type=Path, required=True)
    ap.add_argument("--prefix", type=int, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists() and args.prefix > 0
    groups = json.loads(args.groups.read_text(), object_pairs_hook=no_duplicate_keys)
    assert args.prefix <= groups["group_count"]
    outcomes = []
    with args.ledger.open(encoding="utf8") as stream:
        for i in range(args.prefix):
            row = json.loads(stream.readline(), object_pairs_hook=no_duplicate_keys)
            assert row["group"] == i and row["status"] in ("excluded", "pending")
            outcomes.append(row)
    report = {"N": groups["N"], "B": groups["B"], "groups_sha256": sha(args.groups),
              "outcomes": outcomes, "observed_prefix": args.prefix,
              "total_groups": groups["group_count"], "whole_producer_complete": False,
              "mathematical_acceptance": False, "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, separators=(",", ":")), encoding="utf8")
    print("Untrusted live-producer prefix snapshot", args.prefix, "pending",
          sum(row["status"] == "pending" for row in outcomes), flush=True)


if __name__ == "__main__":
    main()
