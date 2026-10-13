"""Independent standard-library-only replay of standalone discovery proofs."""
from pathlib import Path
from collections import Counter
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"),
                      object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    snapshot, receipt = map(read, (args.snapshot, args.receipt))
    assert receipt["schema"] == "individually-paid-discovery-graphs-v1"
    assert receipt["snapshot_sha256"] == sha(args.snapshot)
    assert receipt["complete_family_coverage"] is False
    assert receipt["source_sha256"] == sha(ROOT / "probe_collar_discovery.py")
    assert receipt["source_make_sha256"] == sha(HIGH / "probe_groups.py")
    constpath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constpath)
    assert receipt["constants_sha256"] == sha(constpath)
    assert constants["verified"] and constants["N"] == 25
    counts = Counter()
    nodes = Counter()
    for index, outcome in enumerate(receipt["outcomes"]):
        assert index == outcome["group"]
        row = snapshot["weak_graphs"][index]
        assert (outcome["centers"], outcome["faces"]) == (row["centers"], row["faces"])
        counts[outcome["status"]] += 1
        if outcome["status"] == "pending":
            continue
        assert outcome["status"] == "excluded"
        treepath = args.receipt.parent / f"discovered-{index:07}.json.gz"
        assert sha(treepath) == outcome["tree_sha256"]
        with gzip.open(treepath, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
            25, 14, row["centers"], row["faces"])
        assert tree["constants_sha256"] == sha(constpath)
        assert tree["radius_upper"] == constants["radius_upper"]
        assert tree["discovery_snapshot_sha256"] == sha(args.snapshot)
        assert tree["does_not_assert_family_coverage"] is True
        assert all(node["kind"] in ("EMPTY", "SPLIT", "DUAL") for node in tree["nodes"])
        result = exact.verify(14, row["centers"], row["faces"], tree["nodes"], constants)
        assert all(result[key] == outcome[key] for key in result)
        nodes.update(result["counts"])
    assert dict(counts) == receipt["totals"]
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    args.output.write_text(json.dumps({
        "verified": True, "schema": "discovery-graph-exact-replay-v1",
        "snapshot_sha256": sha(args.snapshot),
        "receipt_sha256": sha(args.receipt),
        "constants_sha256": sha(constpath),
        "exact_checker_sha256": sha(HIGH / "exact_graph.py"),
        "force_kernel_sha256": sha(HIGH.parent / "round2-grouped/partial_force_exact.py"),
        "source_sha256": sha(Path(__file__)),
        "totals": dict(counts), "node_counts": dict(nodes),
        "no_optimizer_imported": True,
        "complete_family_coverage": False, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    print("Independent stdlib discovery replay PASS:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
