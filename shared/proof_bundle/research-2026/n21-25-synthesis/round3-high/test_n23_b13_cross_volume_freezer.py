"""Scope/count gates and independent cross-volume snapshot byte controls."""
from pathlib import Path
from copy import deepcopy
from io import StringIO
import argparse
import json
import subprocess
import sys
from freeze_n23_b13_cross_volume import check_hierarchy
from multiroot_snapshot import Bindings, relative_key
from audit_multiroot_snapshot import audit
from certified_receipt_union import read, write_new
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def rejects(action):
    try:
        action()
    except (AssertionError, OSError):
        return
    raise AssertionError("incorrect completion/path accepted")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    folder = args.output.resolve()
    registry = read(ROOT / "LARGE-OUTPUT-LOCATION.json")
    bulk = Path(registry["large_output_root"])
    other = bulk / "n23-b13-freezer-controls-resume1"
    assert not other.exists()
    other.mkdir()
    # Positive unit predicate control only: no force/certificate acceptance or
    # necessary-catalogue completeness is claimed by this synthetic dictionary.
    accounting = {"verified": True, "coverage_partition_complete": True,
                  "disjoint_hierarchy_partition_verified": True,
                  "N": 23, "B": 13, "catalog_types": 1530509,
                  "strict_exclusion_types_with_replayed_certificates": 1530509,
                  "pending_types": 0, "global_optimality_proved": False,
                  "source_sha256": sha(ROOT / "audit_composite_hierarchy.py"),
                  "original_map_auditor_sha256": sha(ROOT / "audit_streamed_hierarchy.py"),
                  "composite_union_auditor_sha256": sha(ROOT / "certified_receipt_union.py"),
                  "stream_reader_sha256": sha(ROOT / "stream_catalog.py"),
                  "stages": [{"threshold": 1, "maps_checked": 1530509, "paid_types": 872204,
                              "remaining_types": 658305},
                             {"threshold": 0, "maps_checked": 658305, "paid_types": 658305,
                              "remaining_types": 0}]}
    check_hierarchy(accounting)
    negative = []
    mutations = [
        ("not-verified", "verified", False), ("not-covered", "coverage_partition_complete", False),
        ("not-disjoint", "disjoint_hierarchy_partition_verified", False),
        ("wrong-N", "N", 24), ("wrong-B", "B", 14), ("wrong-inventory", "catalog_types", 4),
        ("unpaid-types", "pending_types", 1),
        ("missing-paid-type", "strict_exclusion_types_with_replayed_certificates", 1530508),
        ("false-global-scope", "global_optimality_proved", True),
        ("wrong-composite-source", "source_sha256", "0"*64),
        ("legacy-transfer-source", "original_map_auditor_sha256", "0"*64),
        ("wrong-union-source", "composite_union_auditor_sha256", "0"*64),
    ]
    for label, key, value in mutations:
        bad = deepcopy(accounting)
        bad[key] = value
        rejects(lambda bad=bad: check_hierarchy(bad))
        negative.append(label)
    bad = deepcopy(accounting)
    bad["stages"][1]["paid_types"] -= 1
    rejects(lambda: check_hierarchy(bad))
    negative.append("incomplete-second-stage")
    # The actual production entrypoint must reject both a real partial audit
    # and the four-type complete CONTROL inventory before writing any manifest.
    audits = [
        bulk / "n23-B13-outer-and-full-prefix-hierarchy-audit-resume1.json",
        ROOT / "evidence/composite-hierarchy-controls-resume2/COMPOSITE-HIERARCHY.json",
    ]
    for i, report in enumerate(audits):
        target = other / f"must-not-publish-{i}.json"
        result = subprocess.run([sys.executable, str(ROOT / "freeze_n23_b13_cross_volume.py"),
                                "--hierarchy", str(report), "--union", str(other / "missing-union.json"),
                                "--output", str(target)], cwd=ROOT, capture_output=True)
        assert result.returncode != 0 and not target.exists()
        assert not Path(str(target)+".building").exists()
        negative.append("production-refuses-"+("partial" if i == 0 else "control-inventory"))
    # Bind actual bytes in two distinct filesystem roots. Then relocate one
    # root using the independent reader and test content corruption detection.
    first = folder / "C-CONTROL-DATA.json"
    second = other / "E-CONTROL-DATA.json"
    write_new(first, {"exact": "workspace control"})
    write_new(second, {"exact": "bulk control"})
    storage = StringIO()
    storage.write('{\n  "files": {\n')
    binding = Bindings(storage, {"workspace": folder, "bulk": other})
    binding.add(first, sha(first))
    binding.add(second, sha(second))
    binding.add(first, sha(first))
    assert binding.count == 2
    storage.write('\n  },\n')
    footer = {"schema": "disk-cover-multiroot-snapshot-v1",
              "roots": {"workspace": str(folder), "bulk": str(other)},
              "file_count": 2, "global_optimality_proved": False,
              "scope": "two-file byte storage control only"}
    storage.write(json.dumps(footer, indent=2)[1:])
    manifest = folder / "TWO-FILE-CONTROL-SNAPSHOT.json"
    with manifest.open("x", encoding="utf8") as stream:
        stream.write(storage.getvalue())
    accepted = audit(manifest)
    assert accepted["verified"] and accepted["file_count"] == 2
    relocated = other / "relocated-root"
    relocated.mkdir()
    (relocated / second.name).write_bytes(second.read_bytes())
    assert audit(manifest, {"bulk": relocated})["verified"]
    (relocated / second.name).write_bytes(b"modified control, never a real proof file")
    bad = audit(manifest, {"bulk": relocated})
    assert not bad["verified"] and len(bad["mismatches"]) == 1
    negative.append("independent-reader-detects-relocated-corruption")
    rejects(lambda: Bindings(StringIO(), {"workspace": folder}).add(second))
    negative.append("file-outside-declared-roots")
    rejects(lambda: Bindings(StringIO(), {"workspace": folder}).add(first, "0"*64))
    negative.append("wrong-file-hash")
    for key in ("workspace/../escape", "workspace/C:/absolute", "/workspace/data", "bulk\\data"):
        rejects(lambda key=key: relative_key(key))
        negative.append("unsafe-alias-key-"+key)
    result = {"verified": True, "synthetic_accounting_gate_only_not_math_acceptance": True,
              "production_refuses_real_partial_and_small_control_inventory": True,
              "two_root_bytes_and_relocation_checked_independently": True,
              "negative_controls_rejected": negative,
              "freezer_sha256": sha(ROOT / "freeze_n23_b13_cross_volume.py"),
              "bindings_source_sha256": sha(ROOT / "multiroot_snapshot.py"),
              "independent_integrity_source_sha256": sha(ROOT / "audit_multiroot_snapshot.py"),
              "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
              "scope": "freezer refusal/publication and byte-storage controls, not branch closure"}
    write_new(folder / "VERIFIED.json", result)
    print("N23 B13 cross-volume freezer controls PASS:", len(negative),
          "bad scope/path/byte controls; real partial and four-type inventories not published", flush=True)


if __name__ == "__main__":
    main()
