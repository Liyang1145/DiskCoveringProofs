"""Disjoint union of independently replayed complete accounting ledgers.

Partial production is completed with PENDING entries, not paid claims.
Certificate paths are explicit absolute paths across volumes. Mathematical
acceptance comes from the immutable original exact replayer, not this merge.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import json
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(Path(path).read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def write_new(path, value):
    with Path(path).open("x", encoding="utf8") as stream:
        json.dump(value, stream, separators=(",", ":"), ensure_ascii=True)


def certificate_path(receiptpath, row):
    if "certificate_path_relative_to_receipt" in row:
        relative = Path(row["certificate_path_relative_to_receipt"])
        assert not relative.is_absolute(), "old relative field must actually be relative"
        return (Path(receiptpath).parent / relative).resolve()
    return (Path(receiptpath).parent / f"group-{row['group']:07}.json.gz").resolve()


def complete_ledger(groupspath, receiptpath, output):
    """Keep a component on its own volume for the unchanged exact replayer."""
    groupspath, receiptpath, output = map(Path, (groupspath, receiptpath, output))
    assert output.parent.resolve() == receiptpath.parent.resolve()
    groups, receipt = read(groupspath), read(receiptpath)
    digest = sha(groupspath)
    assert (receipt["N"], receipt["B"], receipt["groups_sha256"]) == (groups["N"], groups["B"], digest)
    ids = [row["group"] for row in receipt["outcomes"]]
    assert ids == sorted(set(ids))
    assert all(type(gid) is int and 0 <= gid < groups["group_count"] for gid in ids)
    assert all(row["status"] in ("pending", "excluded") for row in receipt["outcomes"])
    observed = {row["group"]: dict(row) for row in receipt["outcomes"]}
    excluded = [row for row in observed.values() if row["status"] == "excluded"]
    assert len(excluded) == receipt["excluded_groups"]
    assert len(observed)-len(excluded) == receipt["pending_groups"]
    for row in excluded:
        assert row["members"] == groups["groups"][row["group"]]["members"]
        assert sha(certificate_path(receiptpath, row)) == row["tree_sha256"]
    assert sum(row["members"] for row in excluded) == receipt["catalog_members_excluded"]
    full = [observed.get(gid, {"group": gid, "status": "pending", "not_in_this_component": True})
            for gid in range(groups["group_count"])]
    result = {"N": groups["N"], "B": groups["B"], "groups_sha256": digest,
              "outcomes": full, "excluded_groups": len(excluded),
              "pending_groups": groups["group_count"]-len(excluded),
              "catalog_members_excluded": receipt["catalog_members_excluded"],
              "original_component_absolute_path": str(receiptpath.resolve()),
              "original_component_sha256": sha(receiptpath), "observed_groups": len(observed),
              "unobserved_entries_filled_pending_only": True,
              "fresh_exact_acceptance": False, "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__))}
    write_new(output, result)
    return result


def build_union(groupspath, components, *, check_tree_bytes=False):
    groupspath = Path(groupspath)
    groups = read(groupspath)
    digest = sha(groupspath)
    assert [g["id"] for g in groups["groups"]] == list(range(groups["group_count"]))
    bindingpath = groupspath.parent / groups["bindings_file"]
    assert sha(bindingpath) == groups["bindings_sha256"]
    paid, reports = {}, []
    minimum = None
    counts = Counter()
    for receiptpath, replaypath in components:
        receiptpath, replaypath = map(Path, (receiptpath, replaypath))
        receipt, replay = read(receiptpath), read(replaypath)
        assert (receipt["N"], receipt["B"]) == (groups["N"], groups["B"])
        assert (replay["N"], replay["B"]) == (groups["N"], groups["B"])
        assert receipt["groups_sha256"] == replay["groups_sha256"] == digest
        assert replay["verified"] and replay["receipt_sha256"] == sha(receiptpath)
        assert replay["bindings_sha256"] == groups["bindings_sha256"]
        assert replay["source_sha256"] == sha(ROOT / "replay_group_stage.py")
        assert replay["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
        rows = receipt["outcomes"]
        assert [row["group"] for row in rows] == list(range(groups["group_count"]))
        assert all(row["status"] in ("pending", "excluded") for row in rows)
        excluded = [row for row in rows if row["status"] == "excluded"]
        assert len(excluded) == receipt["excluded_groups"] == replay["exact_groups_replayed"]
        assert groups["group_count"]-len(excluded) == receipt["pending_groups"] == replay["pending_groups"]
        members = 0
        for row in excluded:
            gid = row["group"]
            assert gid not in paid, "component exclusions must be disjoint"
            assert row["members"] == groups["groups"][gid]["members"]
            path = certificate_path(receiptpath, row)
            if check_tree_bytes:
                assert sha(path) == row["tree_sha256"]
            normalized = {key: value for key, value in row.items()
                          if key != "certificate_path_relative_to_receipt"}
            normalized["certificate_absolute_path"] = str(path)
            paid[gid] = normalized
            members += row["members"]
        assert members == receipt["catalog_members_excluded"] == replay["associated_member_count"]
        if excluded:
            margin = F(replay["minimum_force_margin"])
            assert margin > 0
            minimum = margin if minimum is None else min(minimum, margin)
        counts.update(replay["node_counts"])
        reports.append({"receipt_absolute_path": str(receiptpath.resolve()),
                        "replay_absolute_path": str(replaypath.resolve()),
                        "receipt_sha256": sha(receiptpath), "replay_sha256": sha(replaypath),
                        "excluded_groups": len(excluded), "associated_members": members})
    assert len(reports) >= 2
    outcomes = [paid.get(gid, {"group": gid, "status": "pending"})
                for gid in range(groups["group_count"])]
    return {"verified": True, "schema": "replayed-disjoint-group-union-v1",
            "N": groups["N"], "B": groups["B"], "groups_sha256": digest,
            "bindings_sha256": groups["bindings_sha256"], "outcomes": outcomes,
            "components": reports, "excluded_groups": len(paid),
            "pending_groups": groups["group_count"]-len(paid),
            "catalog_members_excluded": sum(row["members"] for row in paid.values()),
            "minimum_force_margin": None if minimum is None else str(minimum),
            "node_counts": dict(counts), "all_components_original_exact_replayed": True,
            "disjoint_component_union_verified": True,
            "certificate_paths_are_explicit_absolute_paths": True,
            "embedding_transfers_not_verified_here": True, "global_optimality_proved": False,
            "source_sha256": sha(Path(__file__))}


def checked_union_report(groupspath, reportpath):
    report = read(reportpath)
    assert report["schema"] == "replayed-disjoint-group-union-v1"
    assert report["source_sha256"] == sha(Path(__file__))
    components = [(row["receipt_absolute_path"], row["replay_absolute_path"])
                  for row in report["components"]]
    assert build_union(groupspath, components) == report
    return report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--complete-component", type=Path)
    ap.add_argument("--component", nargs=2, action="append")
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    if args.complete_component:
        assert not args.component
        result = complete_ledger(args.groups, args.complete_component, args.output)
        print("Accounting completed with pending entries only; fresh exact replay required:",
              result["excluded_groups"], "excluded entries", flush=True)
    else:
        assert args.component
        result = build_union(args.groups, args.component, check_tree_bytes=True)
        write_new(args.output, result)
        print("Independently replayed disjoint receipt union PASS:", result["excluded_groups"],
              "strict groups;", result["pending_groups"], "pending; no transfer/global claim", flush=True)


if __name__ == "__main__":
    main()
