"""Whole selected-inventory reference audit for a C/E exact-replay union.

The four real full triangulations form a test inventory, NOT an exhaustive
necessary family. Their standalone weak force trees are rechecked by the
unchanged original acceptor after rebinding only inventory bookkeeping.
"""
from pathlib import Path
import argparse
import gzip
import json
import os
import shutil
import subprocess
import sys
from certified_receipt_union import read, write_new, complete_ledger, build_union
from audit_composite_hierarchy import audit
from paid_binary_residual import BinaryRows
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def original_replay(groups, receipt, output):
    subprocess.run([sys.executable, str(ROOT / "replay_group_stage.py"),
                    "--groups", str(groups), "--receipt", str(receipt), "--output", str(output)],
                   cwd=ROOT, check=True, capture_output=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    folder = args.output.resolve()
    registry = read(ROOT / "LARGE-OUTPUT-LOCATION.json")
    other = Path(registry["large_output_root"]) / f"composite-hierarchy-controls-{args.output.name}"
    assert not other.exists()
    other.mkdir()
    originalgroups = ROOT / "evidence/n23-B13-paid-run0-outer-prototypes-resume1/GROUPS.json"
    prototypes = read(originalgroups)
    chosen = {}
    with (originalgroups.parent / prototypes["bindings_file"]).open(encoding="utf8") as stream:
        for line in stream:
            binding = json.loads(line)
            chosen.setdefault(binding["group"], binding["index"])
            if len(chosen) == 4:
                break
    assert len(chosen) == 4
    selected = set(chosen.values())
    rawpath = ROOT / "evidence/n23-B13-paid-streamed-resume1/N23-B13-paid-residual.bin.runs/run-0.bin"
    rows = []
    for index, row in BinaryRows(rawpath, run=True).rows():
        if index in selected:
            rows.append(row)
        if index == max(selected):
            break
    assert len(rows) == 4
    catalogpath = folder / "FOUR-REAL-TYPES-CONTROL-INVENTORY.json"
    write_new(catalogpath, {"N": 23, "B": 13, "complete": True, "orbits": 4,
                           "global_optimality_proved": False,
                           "scope": "complete four-type test inventory only; not a necessary family",
                           "survivors": rows})
    groupfolder = folder / "groups"
    subprocess.run([sys.executable, str(ROOT / "group_catalog.py"), "--catalog", str(catalogpath),
                    "--threshold", "1", "--output", str(groupfolder)],
                   cwd=ROOT, check=True, capture_output=True)
    groupspath = groupfolder / "GROUPS.json"
    groups = read(groupspath)
    assert groups["group_count"] == 4 and groups["selected_types"] == 4
    known = {tuple(group["faces"]): group for group in prototypes["groups"]}
    originalreceiptpath = ROOT / "evidence/n23-B13-paid-run0-outer-prototype-force-resume1/SUMMARY.json"
    originalreceipt = read(originalreceiptpath)
    oldoutcomes = {row["group"]: row for row in originalreceipt["outcomes"]}
    referencefolder = folder / "reference"
    referencefolder.mkdir()
    outcomes = []
    for group in groups["groups"]:
        oldgroup = known[tuple(group["faces"])]
        oldrow = oldoutcomes[oldgroup["id"]]
        assert oldrow["status"] == "excluded"
        oldtreepath = originalreceiptpath.parent / f"group-{oldgroup['id']:07}.json.gz"
        assert sha(oldtreepath) == oldrow["tree_sha256"]
        with gzip.open(oldtreepath, "rt", encoding="utf8") as stream:
            tree = json.load(stream)
        assert tree["faces"] == group["faces"] and tree["partial_centers"] == group["centers"]
        tree["groups_sha256"] = sha(groupspath)
        target = referencefolder / f"group-{group['id']:07}.json.gz"
        with gzip.open(target, "wt", encoding="utf8") as stream:
            json.dump(tree, stream, separators=(",", ":"))
        row = dict(oldrow, group=group["id"], members=group["members"], tree_sha256=sha(target))
        outcomes.append(row)
    reference = {"N": 23, "B": 13, "groups_sha256": sha(groupspath),
                 "outcomes": outcomes, "excluded_groups": 4, "pending_groups": 0,
                 "catalog_members_excluded": 4, "global_optimality_proved": False}
    referencepath = referencefolder / "SUMMARY.json"
    referencereplay = referencefolder / "EXACT-REPLAY.json"
    write_new(referencepath, reference)
    original_replay(groupspath, referencepath, referencereplay)
    components = []
    for part, componentfolder in enumerate((folder, other)):
        componentrows = []
        for originalrow in outcomes:
            if originalrow["group"] % 2 != part:
                continue
            row = dict(originalrow)
            source = referencefolder / f"group-{row['group']:07}.json.gz"
            if part:
                shutil.copyfile(source, componentfolder / source.name)
            else:
                row["certificate_path_relative_to_receipt"] = os.path.relpath(source, componentfolder)
            componentrows.append(row)
        receipt = dict(reference, outcomes=componentrows, excluded_groups=2,
                       catalog_members_excluded=2)
        partialpath = componentfolder / "PARTIAL.json"
        completepath = componentfolder / "COMPLETE-PENDING-FILLED.json"
        replaypath = componentfolder / "EXACT-REPLAY.json"
        write_new(partialpath, receipt)
        complete_ledger(groupspath, partialpath, completepath)
        original_replay(groupspath, completepath, replaypath)
        components.append((completepath, replaypath))
    unionpath = folder / "UNION.json"
    write_new(unionpath, build_union(groupspath, components, check_tree_bytes=True))
    originalauditpath = folder / "ORIGINAL-HIERARCHY.json"
    subprocess.run([sys.executable, str(ROOT / "audit_streamed_hierarchy.py"),
                    "--catalog", str(catalogpath), "--stage", str(groupspath), str(referencepath),
                    str(referencereplay), "--output", str(originalauditpath)],
                   cwd=ROOT, check=True, capture_output=True)
    compositepath = folder / "COMPOSITE-HIERARCHY.json"
    composite = audit(catalogpath, [(str(groupspath), str(unionpath), "COMPOSITE")], compositepath)
    original = read(originalauditpath)
    keys = ("N", "B", "catalog_sha256", "catalog_types", "pending_types",
            "strict_exclusion_types_with_replayed_certificates", "pending_indices_sha256",
            "disjoint_hierarchy_partition_verified", "coverage_partition_complete")
    assert all(original[key] == composite[key] for key in keys)
    for key in ("groups_sha256", "bindings_sha256", "threshold", "maps_checked", "paid_types",
                "remaining_types"):
        assert original["stages"][0][key] == composite["stages"][0][key]
    assert composite["catalog_types"] == 4 and composite["pending_types"] == 0
    assert not composite["catalog_completeness_proved_here"] and not composite["global_optimality_proved"]
    result = {"verified": True, "all_four_real_full_types_mapped": True,
              "original_and_cross_volume_composite_audits_identical_accounting": True,
              "three_fresh_original_force_replays": True,
              "test_inventory_not_complete_necessary_family": True,
              "source_sha256": sha(Path(__file__)),
              "union_source_sha256": sha(ROOT / "certified_receipt_union.py"),
              "hierarchy_source_sha256": sha(ROOT / "audit_composite_hierarchy.py"),
              "original_auditor_sha256": sha(ROOT / "audit_streamed_hierarchy.py"),
              "original_exact_replayer_sha256": sha(ROOT / "replay_group_stage.py"),
              "reference_audit_sha256": sha(originalauditpath),
              "composite_audit_sha256": sha(compositepath), "global_optimality_proved": False}
    write_new(folder / "VERIFIED.json", result)
    print("Composite full-inventory controls PASS: all four real full types mapped;",
          "old and C/E composite audits have identical paid/unpaid accounting", flush=True)


if __name__ == "__main__":
    main()
