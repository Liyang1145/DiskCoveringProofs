"""Pay discovered weak graphs from scratch; never assert complete family coverage."""
from pathlib import Path
from collections import Counter
import argparse
import gzip
import hashlib
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from probe_groups import make
from group_catalog import canonical

assert __debug__


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--count", type=int, default=32)
    ap.add_argument("--limit", type=int, default=1)
    args = ap.parse_args()
    data = json.loads(args.snapshot.read_text(encoding="utf8"))
    B = data["B"]
    assert B in (14, 15, 16, 17)
    assert data["schema"] == "incomplete-collar-discovery-v1"
    assert data["complete_necessary_outer_search"] is False
    assert data["global_optimality_proved"] is False
    assert data["N"] == 25 and data["B"] == B
    assert 0 < args.count and args.limit > 0
    assert data["weak_graph_count"] == len(data["weak_graphs"])
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    constpath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = json.loads(constpath.read_text(encoding="utf8"))
    assert constants["verified"] and constants["N"] == 25
    output.mkdir()
    outcomes = []
    totals = Counter()
    started = time.monotonic()
    rows = data["weak_graphs"][:args.count]
    with (output / "outcomes.jsonl").open("x", encoding="utf8") as ledger:
        for gid, row in enumerate(rows):
            centers, faces = row["centers"], row["faces"]
            code, mapping = canonical(centers, B, faces, 1)
            assert list(code) == faces and len(mapping["centers"]) == centers
            nodes, failure = make(B, centers, faces, constants, args.limit, route_weak=True)
            if nodes is None:
                outcome = {"group": gid, "centers": centers, "faces": faces,
                           "status": "pending", **failure}
            else:
                result = exact.verify(B, centers, faces, nodes, constants)
                treepath = output / f"discovered-{gid:07}.json.gz"
                with gzip.open(treepath, "xt", encoding="utf8") as stream:
                    json.dump({
                        "N": 25, "B": B, "partial_centers": centers, "faces": faces,
                        "nodes": nodes, "constants_sha256": sha(constpath),
                        "radius_upper": constants["radius_upper"],
                        "discovery_snapshot_sha256": sha(args.snapshot),
                        "does_not_assert_family_coverage": True,
                    }, stream, separators=(",", ":"))
                outcome = {"group": gid, "centers": centers, "faces": faces,
                           "status": "excluded", **result, "tree_sha256": sha(treepath)}
            totals[outcome["status"]] += 1
            outcomes.append(outcome)
            ledger.write(json.dumps(outcome, separators=(",", ":"))+"\n")
            ledger.flush()
            print("Discovery graph", gid, outcome["status"], "centers", centers,
                  "faces", len(faces), "seconds", round(time.monotonic()-started, 2),
                  flush=True)
    (output / "SUMMARY.json").write_text(json.dumps({
        "schema": "individually-paid-discovery-graphs-v1",
        "N": 25, "B": B, "snapshot_sha256": sha(args.snapshot),
        "constants_sha256": sha(constpath), "outcomes": outcomes,
        "totals": dict(totals), "source_sha256": sha(Path(__file__)),
        "source_make_sha256": sha(HIGH / "probe_groups.py"),
        "complete_family_coverage": False, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
