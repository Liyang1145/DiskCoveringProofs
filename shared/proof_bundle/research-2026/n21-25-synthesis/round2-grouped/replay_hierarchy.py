"""Fresh stdlib replay and coverage audit for grouped n=21 certificates.

This deliberately does not trust the producer summaries: every stored tree is
opened, its graph is checked against GROUPS.json, and the exact force/tree
checker is run again.  It also verifies that the combined ledger partitions
all groups and that the reported membership counts agree with the bindings.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction
import argparse
import gzip
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
import partial_force_exact as exact


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def load_constants():
    p = ROOT.parent.parent / "n21-global" / "evidence" / "angle-constants.json"
    d = json.loads(p.read_text(encoding="utf8"))
    assert d["verified"] and d["N"] == 21
    return d, sha(p)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--B", type=int, choices=(13, 14), required=True)
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--combined", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.parent.mkdir(parents=True, exist_ok=True)

    groups = json.loads(args.groups.read_text(encoding="utf8"))
    combined = json.loads(args.combined.read_text(encoding="utf8"))
    assert groups["verified_embeddings"] and groups["B"] == args.B and groups["N"] == 21
    assert combined["B"] == args.B and combined["N"] == 21
    groups_sha = sha(args.groups)
    assert combined["groups_sha256"] == groups_sha
    assert groups["group_count"] == len(groups["groups"])
    assert len({row["id"] for row in groups["groups"]}) == groups["group_count"]
    assert sorted(row["id"] for row in groups["groups"]) == list(range(groups["group_count"]))

    membership = Counter(bind["group"] for bind in groups["bindings"])
    assert set(membership) <= set(range(groups["group_count"]))
    outcomes = combined["outcomes"]
    assert len(outcomes) == groups["group_count"]
    by_id = {row["group"]: row for row in outcomes}
    assert set(by_id) == set(range(groups["group_count"]))
    assert combined["excluded_group_count"] + combined["pending_group_count"] == groups["group_count"]
    assert all(row["status"] in ("excluded", "pending") for row in outcomes)

    constants, constants_sha = load_constants()
    assert combined.get("global_optimality_proved") is False
    checked = 0
    pending = 0
    minimum = None
    kind_counts = Counter()
    member_total = 0

    for gid in range(groups["group_count"]):
        row = by_id[gid]
        if row["status"] == "pending":
            pending += 1
            assert "certificate_path" not in row
            continue
        checked += 1
        member_total += row["checked_catalog_members"]
        assert row["checked_catalog_members"] == membership[gid]
        path = (ROOT / Path(row["certificate_path"]) if "certificate_path" in row
                else args.combined.parent / f"group-{gid:07}.json.gz")
        assert path.exists(), path
        assert sha(path) == row["tree_sha256"]
        with gzip.open(path, "rt", encoding="utf8") as stream:
            payload = json.load(stream)
        assert payload["B"] == args.B and payload["N"] == 21
        assert payload["constants_sha256"] == constants_sha
        assert payload["group_dataset_sha256"] == groups_sha
        assert payload["radius_upper"] == constants["radius_upper"]
        group = groups["groups"][gid]
        assert payload["partial_centers"] == group["centers"]
        assert payload["faces"] == group["faces"]
        result = exact.verify(
            args.B, payload["partial_centers"], payload["faces"],
            payload["nodes"], constants
        )
        assert result["verified"] and result["nodes"] == row["nodes"]
        assert result["counts"] == row["counts"]
        margin = Fraction(result["minimum_margin"])
        assert margin > 0
        minimum = margin if minimum is None else min(minimum, margin)
        kind_counts.update(result["counts"])
        if checked % 1000 == 0:
            print("B", args.B, "replayed", checked, "group", gid, flush=True)

    assert checked == combined["excluded_group_count"]
    assert pending == combined["pending_group_count"]
    assert member_total == combined["catalog_member_exclusions"]
    report = {
        "verified": True,
        "N": 21,
        "B": args.B,
        "groups_sha256": groups_sha,
        "combined_sha256": sha(args.combined),
        "constants_sha256": constants_sha,
        "group_count": groups["group_count"],
        "excluded_groups_replayed": checked,
        "pending_groups": pending,
        "catalog_member_exclusions_replayed": member_total,
        "minimum_margin": str(minimum),
        "node_kind_counts": dict(kind_counts),
        "global_optimality_proved": False,
    }
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
