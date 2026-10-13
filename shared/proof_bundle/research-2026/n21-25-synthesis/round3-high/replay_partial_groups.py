"""Fresh exact replay of an intentionally partial adaptive group receipt.

This is a certificate check only. It does not certify unobserved groups,
partition coverage, or a complete hierarchy.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import gzip
import json
from collections import Counter
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    groups, receipt = read(args.groups), read(args.receipt)
    digest = sha(args.groups)
    assert (receipt["N"], receipt["B"], receipt["groups_sha256"]) == (
        groups["N"], groups["B"], digest)
    outcomes = receipt["outcomes"]
    ids = [row["group"] for row in outcomes]
    assert ids == sorted(set(ids)) and all(0 <= gid < groups["group_count"] for gid in ids)
    constants = ROOT.parent / f"evidence/core-reduction/constants/n{groups['N']}.json"
    const = read(constants)
    assert const["verified"] and const["N"] == groups["N"]
    minimum = None
    counts = Counter()
    members = 0
    for row in outcomes:
        assert row["status"] in ("excluded", "pending")
        if row["status"] == "pending":
            continue
        gid = row["group"]
        group = groups["groups"][gid]
        path = (args.receipt.parent / row["certificate_path_relative_to_receipt"]
                if "certificate_path_relative_to_receipt" in row else
                args.receipt.parent / f"group-{gid:07}.json.gz")
        assert sha(path) == row["tree_sha256"]
        with gzip.open(path, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
            groups["N"], groups["B"], group["centers"], group["faces"])
        assert tree["groups_sha256"] == digest
        assert tree["constants_sha256"] == sha(constants)
        assert tree["radius_upper"] == const["radius_upper"]
        result = exact.verify(groups["B"], group["centers"], group["faces"], tree["nodes"], const)
        assert result["verified"] and result["counts"] == row["counts"]
        margin = F(result["minimum_force_margin"])
        assert margin > 0
        minimum = margin if minimum is None else min(minimum, margin)
        counts.update(result["counts"])
        assert row["members"] == group["members"]
        members += row["members"]
    assert members == receipt["catalog_members_excluded"]
    assert members == sum(groups["groups"][gid]["members"] for gid in ids
                          if next(row for row in outcomes if row["group"] == gid)["status"] == "excluded")
    report = {"verified": True, "N": groups["N"], "B": groups["B"],
              "groups_sha256": digest, "receipt_sha256": sha(args.receipt),
              "exact_excluded_groups_replayed": sum(row["status"] == "excluded" for row in outcomes),
              "pending_groups_in_receipt": sum(row["status"] == "pending" for row in outcomes),
              "associated_member_count": members,
              "minimum_force_margin": None if minimum is None else str(minimum),
              "node_counts": dict(counts), "partial_receipt_only": True,
              "unobserved_groups_not_certified": True, "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__)),
              "exact_checker_sha256": sha(ROOT / "exact_graph.py")}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Partial group exact replay PASS", report["exact_excluded_groups_replayed"],
          "excluded groups", flush=True)


if __name__ == "__main__":
    main()
