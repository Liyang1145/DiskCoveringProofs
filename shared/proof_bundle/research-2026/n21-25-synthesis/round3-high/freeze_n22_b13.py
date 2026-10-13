"""Freeze exactly the paid n22 B13 recorded-catalogue branch, not global n22."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
from stream_catalog import sha
from audit_streamed_hierarchy import read

ROOT = Path(__file__).resolve().parent
SYN = ROOT.parent
WORK = SYN.parent.parent
EV = ROOT / "evidence"
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    auditpath = EV / "n22-B13-hierarchy-audit-complete-resume1.json"
    audit = read(auditpath)
    assert audit["verified"] and audit["coverage_partition_complete"]
    assert audit["disjoint_hierarchy_partition_verified"]
    assert (audit["N"], audit["B"], audit["catalog_types"]) == (22, 13, 1791859)
    assert audit["strict_exclusion_types_with_replayed_certificates"] == 1791859
    assert audit["pending_types"] == 0
    assert audit["source_sha256"] == sha(ROOT / "audit_streamed_hierarchy.py")
    assert audit["stream_reader_sha256"] == sha(ROOT / "stream_catalog.py")
    pendingpath = EV / audit["pending_indices_file"]
    assert pendingpath.stat().st_size == 0 and sha(pendingpath) == audit["pending_indices_sha256"]
    controls = EV / "independent-transfer-controls-resume1.json"
    control = read(controls)
    assert control["verified"] and control["positive_controls"] == 2
    assert len(control["negative_controls_rejected"]) == 11
    assert control["auditor_sha256"] == sha(ROOT / "audit_streamed_hierarchy.py")
    files = {auditpath, pendingpath, controls}
    files |= {ROOT / name for name in (
        "N22-B13-CATALOGUE-CLOSURE.md", "freeze_n22_b13.py",
        "audit_streamed_hierarchy.py", "audit_transfer_controls.py",
        "stream_catalog.py", "exact_graph.py", "replay_group_stage.py")}
    constants = SYN / "evidence/core-reduction/constants/n22.json"
    const = read(constants)
    assert const["verified"] and F(const["radius_upper"]) == F("0.253251459835093")
    assert const["angle_scale"] == 10**7 and const["angle_caps"] == [815002, 1690622, 2746810]
    catalogdir = EV / "n22-B13-dfs-resume1"
    catpath = catalogdir / "N22-B13-dfs.json"
    catsummary = read(catalogdir / "SUMMARY.json")
    assert catsummary["complete"] and catsummary["orbits"] == 1791859
    assert catsummary["catalog_sha256"] == audit["catalog_sha256"] == sha(catpath)
    assert catsummary["source_sha256"] == sha(SYN / "peel_synthesis.cpp")
    assert catsummary["constants_sha256"] == sha(constants)
    files |= {catpath, catalogdir / "SUMMARY.json", SYN / "peel_synthesis.cpp", constants,
              SYN / "core_reduction.py", SYN / "SHARED-CORE-REDUCTION.md",
              SYN / "round2-grouped/partial_force_exact.py",
              WORK / "research-2026/disk-cover-proof-library/external/pinned/cover20/proof_bundle/core/exact_arcs.py"}
    for info, stage, receiptname, replayname in zip(
            audit["stages"],
            ("pair", "outer", "full"),
            ("n22-B13-pair-root-resume1/SUMMARY.json",
             "n22-B13-outer-combined-resume1.json",
             "n22-B13-full-root-resume1/SUMMARY.json"),
            ("n22-B13-pair-replay-resume1.json",
             "n22-B13-outer-replay-resume1.json",
             "n22-B13-full-replay-resume1.json")):
        grouppath = EV / f"n22-B13-{stage}-resume1/GROUPS.json"
        groups = read(grouppath)
        receiptpath, replaypath = EV / receiptname, EV / replayname
        receipt, replay = read(receiptpath), read(replaypath)
        assert sha(grouppath) == info["groups_sha256"] == replay["groups_sha256"] == receipt["groups_sha256"]
        assert sha(replaypath) == info["force_replay_sha256"]
        assert replay["verified"] and replay["receipt_sha256"] == sha(receiptpath)
        assert replay["associated_member_count"] == info["paid_types"]
        assert F(replay["minimum_force_margin"]) > 0
        assert replay["source_sha256"] == sha(ROOT / "replay_group_stage.py")
        assert replay["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
        bindingpath = grouppath.parent / groups["bindings_file"]
        assert sha(bindingpath) == groups["bindings_sha256"] == info["bindings_sha256"]
        files |= {grouppath, bindingpath, receiptpath, replaypath}
        for row in receipt["outcomes"]:
            if row["status"] != "excluded":
                continue
            path = (receiptpath.parent / row["certificate_path_relative_to_receipt"]
                    if "certificate_path_relative_to_receipt" in row else
                    receiptpath.parent / f"group-{row['group']:07}.json.gz")
            assert sha(path) == row["tree_sha256"]
            files.add(path)
    digests = {}
    for index, path in enumerate(sorted(files)):
        digests[path.resolve().relative_to(WORK.resolve()).as_posix()] = sha(path)
        if (index+1) % 10000 == 0:
            print("Branch files bound", index+1, flush=True)
    report = {"verified": True, "N": 22, "B": 13, "catalog_types": 1791859,
              "recorded_catalogue_branch_closed": True,
              "strict_exclusion_types_with_replayed_certificates": 1791859,
              "global_optimality_proved": False,
              "scope": "complete B13 recorded-catalogue exclusion, not whole n22 proof",
              "file_count": len(digests), "files": digests}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N22 B13 catalogue branch SNAPSHOT PASS:", len(digests), "files", flush=True)


if __name__ == "__main__":
    main()
