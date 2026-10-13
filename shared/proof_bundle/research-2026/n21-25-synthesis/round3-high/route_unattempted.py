"""Untrusted routing: avoid attempting the same adaptive group twice.

This is not a complete mathematical ledger and must never be used as a
hierarchy parent proof. Only probe selection may consume its outcomes.
"""
from pathlib import Path
import argparse
import json
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def read(path):
    return json.loads(path.read_text(), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--attempted", type=Path, action="append", required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    source = read(args.source)
    pending = {r["group"] for r in source["outcomes"] if r["status"] == "pending"}
    attempted = set()
    for path in args.attempted:
        data = read(path)
        assert (data["N"], data["B"], data["groups_sha256"]) == (
            source["N"], source["B"], source["groups_sha256"])
        for row in data["outcomes"]:
            assert row["group"] in pending and row["group"] not in attempted
            assert row["status"] in ("pending", "excluded")
            attempted.add(row["group"])
    remaining = sorted(pending-attempted)
    report = {"N": source["N"], "B": source["B"], "groups_sha256": source["groups_sha256"],
              "outcomes": [{"group": gid, "status": "pending"} for gid in remaining],
              "omitted_attempted_groups": len(attempted),
              "routing_source_sha256": sha(args.source),
              "attempted_receipts_sha256": [sha(p) for p in args.attempted],
              "not_a_complete_ledger": True, "mathematical_acceptance": False,
              "global_optimality_proved": False, "source_sha256": sha(Path(__file__))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, separators=(",", ":")), encoding="utf8")
    print("Unattempted proposal routing", len(remaining), "groups", flush=True)


if __name__ == "__main__":
    main()
