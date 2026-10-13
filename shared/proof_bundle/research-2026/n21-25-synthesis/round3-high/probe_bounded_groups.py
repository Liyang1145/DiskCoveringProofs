"""Root-only new norm-supported actual-cover group exclusions."""
from pathlib import Path
import argparse
import gzip
import json
import bounded_exact as E
import exact_graph as exact
from bounded_proposals import Solver
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--only-pending-from", type=Path)
    ap.add_argument("--count", type=int)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    controls = json.loads((ROOT / "evidence/bounded-format-controls-resume1.json").read_text())
    assert controls["verified"] and controls["bounded_checker_sha256"] == sha(ROOT / "bounded_exact.py")
    data = json.loads(args.groups.read_text())
    digest = sha(args.groups)
    chosen = data["groups"]
    if args.only_pending_from:
        old = json.loads(args.only_pending_from.read_text())
        assert old["groups_sha256"] == digest
        unpaid = {row["group"] for row in old["outcomes"] if row["status"] == "pending"}
        chosen = [row for row in chosen if row["id"] in unpaid]
    if args.count:
        chosen = chosen[:args.count]
    outcomes = []
    for group in chosen:
        solver = Solver(data["N"], data["B"], group["centers"], group["faces"])
        matrix = exact.kernel.angle_bounds(data["B"], group["centers"], solver.faces, solver.constants)
        lo, hi = exact.rootbox(matrix, solver.constants["angle_scale"])
        lo, hi = exact.kernel.tighten(matrix, lo, hi, solver.constants["angle_scale"])
        force, x = solver.solve(lo, hi)
        if force is None:
            outcome = {"group": group["id"], "status": "pending"}
        else:
            nodes = [{"kind": "BDUAL", "certificate": force}]
            report = E.verify(data["N"], data["B"], group["centers"], group["faces"], nodes)
            path = args.output / f"group-{group['id']:07}.json.gz"
            payload = {"N": data["N"], "B": data["B"], "partial_centers": group["centers"],
                       "faces": group["faces"], "nodes": nodes, "groups_sha256": digest,
                       "norm_premise": report["norm_premise"],
                       "scope": "actual covers only after U normalization"}
            with gzip.open(path, "wt", encoding="utf8") as stream:
                json.dump(payload, stream, separators=(",", ":"))
            outcome = {"group": group["id"], "status": "excluded", "members": group["members"],
                       **report, "tree_sha256": sha(path)}
        outcomes.append(outcome)
        if len(outcomes) % 500 == 0:
            print("Bounded groups", data["N"], data["B"], len(outcomes),
                  "excluded", sum(r["status"] == "excluded" for r in outcomes), flush=True)
    report = {"N": data["N"], "B": data["B"], "groups_sha256": digest, "outcomes": outcomes,
              "excluded_groups": sum(r["status"] == "excluded" for r in outcomes),
              "pending_groups": sum(r["status"] == "pending" for r in outcomes),
              "catalog_members_excluded": sum(r.get("members", 0) for r in outcomes if r["status"] == "excluded"),
              "new_premise": "ACTUAL-NORM-BOUNDS.md", "fresh_all_member_embedding_audit": False,
              "global_optimality_proved": False, "source_sha256": sha(Path(__file__))}
    (args.output / "SUMMARY.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Bounded actual-cover root proposals finished", data["N"], data["B"],
          report["excluded_groups"], report["pending_groups"], flush=True)


if __name__ == "__main__":
    main()
