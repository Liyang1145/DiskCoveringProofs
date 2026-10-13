"""Real exact-force controls for C/E disjoint ledger composition."""
from pathlib import Path
import argparse
import json
import os
import shutil
import subprocess
import sys
from certified_receipt_union import complete_ledger, build_union, checked_union_report, write_new, read
from audit_composite_hierarchy import CompositeStage
from audit_streamed_hierarchy import Stage
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def rejects(action):
    try:
        action()
    except (AssertionError, OSError):
        return
    raise AssertionError("invalid union accepted")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    groupspath = ROOT / "evidence/n23-B13-paid-run0-outer-prototypes-resume1/GROUPS.json"
    originalpath = ROOT / "evidence/n23-B13-paid-run0-outer-prototype-force-resume1/SUMMARY.json"
    groups, original = read(groupspath), read(originalpath)
    assert groups["group_count"] == 95 and original["groups_sha256"] == sha(groupspath)
    registry = read(ROOT / "LARGE-OUTPUT-LOCATION.json")
    other = Path(registry["large_output_root"]) / "certified-receipt-union-controls-resume1"
    assert not other.exists()
    other.mkdir()
    components = []
    for index, folder in enumerate((args.output.resolve(), other.resolve())):
        rows = []
        for originalrow in original["outcomes"]:
            if originalrow["group"] % 2 != index:
                continue
            row = dict(originalrow)
            source = originalpath.parent / f"group-{row['group']:07}.json.gz"
            if index:
                target = folder / source.name
                shutil.copyfile(source, target)
                assert sha(target) == row["tree_sha256"]
            else:
                row["certificate_path_relative_to_receipt"] = os.path.relpath(source, folder)
            rows.append(row)
        partial = {"N": groups["N"], "B": groups["B"], "groups_sha256": sha(groupspath),
                   "outcomes": rows, "excluded_groups": len(rows), "pending_groups": 0,
                   "catalog_members_excluded": sum(row["members"] for row in rows),
                   "global_optimality_proved": False}
        partialpath = folder / "PARTIAL.json"
        completepath = folder / "COMPLETE-PENDING-FILLED.json"
        replaypath = folder / "EXACT-REPLAY.json"
        write_new(partialpath, partial)
        result = complete_ledger(groupspath, partialpath, completepath)
        assert result["pending_groups"] == 95-len(rows)
        assert result["unobserved_entries_filled_pending_only"]
        subprocess.run([sys.executable, str(ROOT / "replay_group_stage.py"), "--groups", str(groupspath),
                        "--receipt", str(completepath), "--output", str(replaypath)],
                       cwd=ROOT, check=True, capture_output=True)
        components.append((completepath, replaypath))
    union = build_union(groupspath, components, check_tree_bytes=True)
    assert union["excluded_groups"] == 95 and union["pending_groups"] == 0
    assert union["catalog_members_excluded"] == 100000
    assert {Path(row["certificate_absolute_path"]).drive for row in union["outcomes"]} == {"C:", "E:"}
    unionpath = args.output / "UNION.json"
    write_new(unionpath, union)
    assert checked_union_report(groupspath, unionpath) == union
    negatives = []
    rejects(lambda: build_union(groupspath, [components[0], components[0]]))
    negatives.append("overlapping-original-exact-components")
    rejects(lambda: build_union(groupspath, [components[0]]))
    negatives.append("missing-second-component")
    for label, key, value in (("wrong-total", "catalog_members_excluded", 99999),
                               ("wrong-source", "source_sha256", "0"*64),
                               ("unpaid-entry-marked-paid", "pending_groups", 1)):
        proposal = dict(union)
        proposal[key] = value
        path = args.output / f"bad-{label}.json"
        write_new(path, proposal)
        rejects(lambda path=path: checked_union_report(groupspath, path))
        negatives.append(label)
    badreport = read(components[0][1])
    badreport["source_sha256"] = "0"*64
    badpath = args.output / "bad-exact-source.json"
    write_new(badpath, badreport)
    rejects(lambda: build_union(groupspath, [(components[0][0], badpath), components[1]]))
    negatives.append("unrecognized-force-acceptor")
    rejects(lambda: complete_ledger(groupspath, args.output / "PARTIAL.json", other / "bad-volume.json"))
    negatives.append("component-normalization-on-wrong-volume")
    # The composition layer must not replace or weaken any original map,
    # selected-type stream, duplicate rejection, or final member-count rule.
    assert CompositeStage.consume is Stage.consume
    assert CompositeStage.advance is Stage.advance
    assert CompositeStage.finish is Stage.finish
    result = {"verified": True, "real_original_exact_replays": 2,
              "strict_groups": 95, "associated_members": 100000,
              "both_C_and_E_certificate_paths_tested": True,
              "unobserved_component_entries_filled_pending_only": True,
              "original_map_stream_and_finish_methods_unchanged": True,
              "negative_controls_rejected": negatives,
              "union_control_sha256": sha(unionpath), "groups_sha256": sha(groupspath),
              "source_sha256": sha(Path(__file__)),
              "union_source_sha256": sha(ROOT / "certified_receipt_union.py"),
              "hierarchy_source_sha256": sha(ROOT / "audit_composite_hierarchy.py"),
              "original_auditor_sha256": sha(ROOT / "audit_streamed_hierarchy.py"),
              "original_force_acceptor_sha256": sha(ROOT / "replay_group_stage.py"),
              "global_optimality_proved": False,
              "scope": "cross-volume force-certificate composition controls, not complete catalogue proof"}
    write_new(args.output / "VERIFIED.json", result)
    print("Cross-volume exact-receipt union controls PASS: 95 force graphs, two original replays;",
          len(negatives), "invalid compositions rejected", flush=True)


if __name__ == "__main__":
    main()
