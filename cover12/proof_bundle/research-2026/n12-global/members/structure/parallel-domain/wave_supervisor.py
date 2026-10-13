"""Generic safe wave supervisor for the n12 k10 domain waves.

Purpose: replace the repeated manual re-planning.  Given an immutable wave plan
and a directory of its branch checkpoints (written by the Lead's parameterized
workers), and GIVEN THAT THE LEAD HAS ALREADY STOPPED THOSE WORKERS, this script

  1. discovers the branch checkpoints in <branch-dir> (files branch-*.json),
  2. requires every branch of <old-plan> to be present,
  3. optionally re-reads all checkpoints after a short gap and refuses if any
     changed (cheap heuristic only; the real "no writer" guarantee is the
     Lead's PID check),
  4. runs the strict merge (same code path as merge_branches: single read per
     file, metadata/base-hash/root pinning, canonical widest-dimension tree
     coverage, counts consistency, cross-branch disjointness, volume identity)
     and refuses if ANY problem is reported,
  5. exports the frozen merged state as <prefix>-base.json in the original
     domain-manifest format (status partial is allowed),
  6. builds the next plan with make_plan(deep=0) - one branch root per pending -
     as <prefix>-plan.json, verifies it with check_plan, and refuses the plan on
     any problem,
  7. writes <prefix>-manifest.json and prints the new source/plan hashes, the
     counts and the new roots.

Safety rules
  * never overwrites: if <prefix>-base.json, <prefix>-plan.json or
    <prefix>-manifest.json exists, the script refuses and writes nothing;
  * the old plan and all checkpoints are opened read-only;
  * the final base and plan are placed with os.replace from a temp file in the
    same directory, so a partial write can never be observed;
  * the script never starts, stops or restarts a worker; stopping is the
    caller's responsibility (recorded in the report and provenance);
  * --dry-run performs every check, prints the same summary plus the hash the
    plan WOULD have, and writes nothing.

Usage:
  py -3 wave_supervisor.py <old-plan.json> <branch-dir> <output-prefix>
                           [--dry-run] [--no-stability-check]
                           [--stability-gap SECONDS]
"""
import argparse
import hashlib
import json
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import boxlib as BX                     # noqa: E402
import plan_branches as PB              # noqa: E402
import merge_branches as MB             # noqa: E402


def discover(branch_dir):
    d = Path(branch_dir)
    if not d.is_dir():
        return None, "branch directory not found: %s" % branch_dir
    files = sorted(p for p in d.glob("branch-*.json") if p.is_file())
    if not files:
        return None, "no branch-*.json checkpoints in %s" % branch_dir
    return files, None


def stability_probe(files, gap):
    """(unchanged, changed_list).  Heuristic only - see module docstring."""
    def snap():
        return {str(p): (p.stat().st_size, BX.file_sha256(str(p)))
                for p in files}
    a = snap()
    if gap > 0:
        time.sleep(gap)
    b = snap()
    changed = sorted(k for k in a if a[k] != b.get(k))
    return (not changed), changed


def main(argv=None):
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("old_plan")
    ap.add_argument("branch_dir")
    ap.add_argument("output_prefix")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--no-stability-check", action="store_true")
    ap.add_argument("--stability-gap", type=float, default=1.5)
    args = ap.parse_args(argv)

    base_path = Path(str(args.output_prefix) + "-base.json")
    plan_path = Path(str(args.output_prefix) + "-plan.json")
    man_path = Path(str(args.output_prefix) + "-manifest.json")
    report = dict(mode="dry-run" if args.dry_run else "freeze",
                  old_plan=str(args.old_plan), branch_dir=str(args.branch_dir),
                  output_prefix=str(args.output_prefix),
                  outputs=["%s (base)" % base_path, "%s (plan)" % plan_path,
                           "%s (manifest)" % man_path])
    refuse = []

    clashes = [str(p) for p in (base_path, plan_path, man_path) if p.exists()]
    if clashes:
        report.update(status="refused",
                      reason="refusing to overwrite existing outputs",
                      clashes=clashes, wrote_nothing=True)
        print(json.dumps(report, indent=1))
        return 1
    if not Path(args.old_plan).is_file():
        report.update(status="refused", reason="old plan not found",
                      wrote_nothing=True)
        print(json.dumps(report, indent=1))
        return 1

    plan, plan_sha = MB.load_plan(args.old_plan)
    planned = [b["id"] for b in plan.get("branches", [])]
    report["old_plan_sha256"] = plan_sha
    report["branches_in_plan"] = planned

    files, err = discover(args.branch_dir)
    if err:
        report.update(status="refused", reason=err, wrote_nothing=True)
        print(json.dumps(report, indent=1))
        return 1
    report["branch_files"] = len(files)

    if not args.no_stability_check:
        stable, changed = stability_probe(files, args.stability_gap)
        if not stable:
            report.update(status="refused",
                          reason="checkpoints still changing (workers not "
                                 "stopped?)", changed=changed,
                          wrote_nothing=True)
            print(json.dumps(report, indent=1))
            return 1

    probe = MB.merge(str(args.old_plan), [str(f) for f in files])
    if probe["problems"]:
        report.update(status="refused", reason="strict merge reported problems",
                      problems=probe["problems"], wrote_nothing=True)
        print(json.dumps(report, indent=1))
        return 1
    report["merge_status"] = probe["status"]
    report["counts"] = probe["counts"]["totals"]

    # ---- build everything in a temp file next to the final base
    tmp_base = Path(str(base_path) + ".tmp")
    try:
        res = MB.export(str(args.old_plan), [str(f) for f in files],
                        str(tmp_base))
        if not res.get("exported"):
            report.update(status="refused", reason="export refused",
                          problems=res.get("problems"), wrote_nothing=True)
            print(json.dumps(report, indent=1))
            return 1
        doc = json.loads(tmp_base.read_text())
        base_sha = res["sha256"]

        newplan = PB.make_plan(str(tmp_base), deep=0)
        base_abs = str(base_path.resolve())
        newplan["source"] = dict(newplan["source"], path=base_abs)
        problems, _snap = PB.check_plan(newplan, str(tmp_base))
        if problems:
            report.update(status="refused",
                          reason="new plan failed check_plan",
                          problems=problems, wrote_nothing=True)
            print(json.dumps(report, indent=1))
            return 1

        roots = [dict(id=b["id"], parent=b["parent_index"],
                      root_sha256=b["root_sha256"],
                      widths=[str(w) for w in BX.widths(BX.decode(b["root"]))])
                 for b in newplan["branches"]]
        plan_text = json.dumps(newplan, indent=1)
        plan_sha = hashlib.sha256(plan_text.encode("utf8")).hexdigest()

        if not args.dry_run:
            os.replace(tmp_base, base_path)
            tmp_plan = Path(str(plan_path) + ".tmp")
            # write bytes so the placed file's hash equals the reported hash
            # (Path.write_text would translate \n to os.linesep on Windows)
            tmp_plan.write_bytes(plan_text.encode("utf8"))
            os.replace(tmp_plan, plan_path)
            man = dict(merge=probe,
                       next_plan=dict(path=str(plan_path), sha256=plan_sha,
                                      branch_count=newplan["branch_count"]))
            tmp_man = Path(str(man_path) + ".tmp")
            tmp_man.write_bytes(json.dumps(man, indent=1).encode("utf8"))
            os.replace(tmp_man, man_path)
            placed = True
        else:
            placed = False

        report.update(
            status="ok" if not args.dry_run else "dry-run-ok",
            base=dict(path=str(base_path), sha256=base_sha,
                      status=doc.get("status"), counts=doc.get("counts"),
                      leaves=len(doc.get("leaves", [])),
                      pending=len(doc.get("pending", []))),
            next_plan=dict(path=str(plan_path), sha256=plan_sha,
                           branch_count=newplan["branch_count"],
                           roots=roots),
            domain_structurally_complete=(len(newplan["branches"]) == 0),
            placement="placed atomically" if placed else "not written (dry-run)",
            wrote_nothing=(not placed),
            note=("a full-domain claim still requires the four-conjunct premise: "
                  "empty stack, complete exact partition, validated infeasible "
                  "leaves, integer-replayed atomic leaves"))
        print(json.dumps(report, indent=1))
        return 0
    finally:
        if tmp_base.exists() and not (not args.dry_run and
                                      base_path.exists()):
            try:
                tmp_base.unlink()
            except OSError:
                pass


if __name__ == "__main__":
    sys.exit(main())
