"""Organize complete root/tree group ledgers; organization is not acceptance."""
from pathlib import Path
import argparse
import json
from stream_catalog import sha

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--root", type=Path, required=True)
    ap.add_argument("--trees", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    groups, root, trees = (json.loads(p.read_text()) for p in (args.groups, args.root, args.trees))
    digest = sha(args.groups)
    assert root["groups_sha256"] == trees["groups_sha256"] == digest
    old = {row["group"]: row for row in root["outcomes"]}
    new = {row["group"]: row for row in trees["outcomes"]}
    assert len(old) == len(root["outcomes"]) == groups["group_count"]
    assert set(old) == set(range(groups["group_count"]))
    assert len(new) == len(trees["outcomes"])
    assert set(new) == {gid for gid, row in old.items() if row["status"] == "pending"}
    outcomes = []
    for gid in range(groups["group_count"]):
        row = dict(new[gid] if gid in new else old[gid])
        assert row["status"] in ("excluded", "pending")
        if row["status"] == "excluded":
            folder = args.trees.parent if gid in new else args.root.parent
            target = folder / f"group-{gid:07}.json.gz"
            assert sha(target) == row["tree_sha256"]
            row["certificate_path_relative_to_receipt"] = target.resolve().relative_to(
                args.output.parent.resolve()).as_posix()
        outcomes.append(row)
    report = {"N": groups["N"], "B": groups["B"], "groups_sha256": digest, "outcomes": outcomes,
              "excluded_groups": sum(row["status"] == "excluded" for row in outcomes),
              "pending_groups": sum(row["status"] == "pending" for row in outcomes),
              "catalog_members_excluded": sum(row.get("members", 0) for row in outcomes if row["status"] == "excluded"),
              "fresh_exact_acceptance": False, "global_optimality_proved": False}
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Merged untrusted receipts", report["N"], report["B"], report["excluded_groups"],
          "groups excluded,", report["pending_groups"], "pending", flush=True)


if __name__ == "__main__":
    main()
