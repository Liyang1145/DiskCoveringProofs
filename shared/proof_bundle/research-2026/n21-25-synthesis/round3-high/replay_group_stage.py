"""Stdlib-only exact group-force replay; embeddings need a separate audit."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import exact_graph as exact
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    data, receipt = (json.loads(p.read_text()) for p in (args.groups, args.receipt))
    digest = sha(args.groups)
    assert receipt["groups_sha256"] == digest
    N, B = data["N"], data["B"]
    assert (receipt["N"], receipt["B"]) == (N, B)
    assert [row["id"] for row in data["groups"]] == list(range(data["group_count"]))
    outcomes = {row["group"]: row for row in receipt["outcomes"]}
    assert len(outcomes) == len(receipt["outcomes"]) == data["group_count"]
    assert set(outcomes) == set(range(data["group_count"]))
    counts = Counter()
    bindingpath = args.groups.parent / data["bindings_file"]
    assert sha(bindingpath) == data["bindings_sha256"]
    previous = -1
    with bindingpath.open(encoding="utf8") as stream:
        for line in stream:
            binding = json.loads(line)
            assert type(binding["index"]) is int and previous < binding["index"] < data["catalog_types"]
            previous = binding["index"]
            assert type(binding["group"]) is int and binding["group"] in outcomes
            counts[binding["group"]] += 1
    assert sum(counts.values()) == data["selected_types"]
    assert all(counts[row["id"]] == row["members"] for row in data["groups"])
    constantspath = ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"
    constants = json.loads(constantspath.read_text())
    assert constants["verified"] and constants["N"] == N
    minimum = None
    nodecounts = Counter()
    accepted = members = 0
    for gid, group in enumerate(data["groups"]):
        outcome = outcomes[gid]
        assert outcome["status"] in ("excluded", "pending")
        if outcome["status"] == "pending":
            continue
        path = (args.receipt.parent / outcome["certificate_path_relative_to_receipt"]
                if "certificate_path_relative_to_receipt" in outcome else
                args.receipt.parent / f"group-{gid:07}.json.gz")
        assert sha(path) == outcome["tree_sha256"]
        with gzip.open(path, "rt", encoding="utf8") as stream:
            tree = json.load(stream)
        assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
            N, B, group["centers"], group["faces"])
        assert tree["groups_sha256"] == digest
        assert tree["constants_sha256"] == sha(constantspath)
        assert tree["radius_upper"] == constants["radius_upper"]
        result = exact.verify(B, group["centers"], group["faces"], tree["nodes"], constants)
        assert result["verified"] and result["nodes"] == outcome["nodes"]
        assert result["counts"] == outcome["counts"]
        margin = F(result["minimum_force_margin"])
        assert margin > 0
        minimum = margin if minimum is None else min(minimum, margin)
        nodecounts.update(result["counts"])
        assert outcome["members"] == group["members"]
        members += group["members"]
        accepted += 1
        if accepted % 5000 == 0:
            print("N", N, "B", B, "exact groups replayed", accepted, flush=True)
    assert accepted == receipt["excluded_groups"]
    assert members == receipt["catalog_members_excluded"]
    report = {"verified": True, "N": N, "B": B, "groups_sha256": digest,
              "receipt_sha256": sha(args.receipt), "bindings_sha256": sha(bindingpath),
              "exact_groups_replayed": accepted, "pending_groups": data["group_count"]-accepted,
              "associated_member_count": members,
              "minimum_force_margin": None if minimum is None else str(minimum),
              "node_counts": dict(nodecounts), "embedding_transfers_not_verified_here": True,
              "global_optimality_proved": False, "source_sha256": sha(Path(__file__)),
              "exact_checker_sha256": sha(ROOT / "exact_graph.py")}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N", N, "B", B, "stdlib group-force replay PASS:", accepted, flush=True)


if __name__ == "__main__":
    main()
