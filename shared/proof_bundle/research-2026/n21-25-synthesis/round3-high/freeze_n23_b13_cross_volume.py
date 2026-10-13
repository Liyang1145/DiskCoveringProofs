"""Content-gate the entire n23 B13 branch across unchanged C/E assets."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import time
from audit_streamed_hierarchy import Stage
from certified_receipt_union import read, checked_union_report, certificate_path
from audit_composite_hierarchy import CompositeStage
from paid_binary_residual import BinaryRows
from multiroot_snapshot import Bindings
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
SYN = ROOT.parent
WORK = ROOT.parents[2].resolve()
EV = ROOT / "evidence"
assert __debug__


def check_hierarchy(report):
    assert report["verified"] and report["coverage_partition_complete"]
    assert report["disjoint_hierarchy_partition_verified"]
    assert (report["N"], report["B"], report["catalog_types"]) == (23, 13, 1530509)
    assert report["strict_exclusion_types_with_replayed_certificates"] == 1530509
    assert report["pending_types"] == 0 and report["global_optimality_proved"] is False
    assert report["source_sha256"] == sha(ROOT / "audit_composite_hierarchy.py")
    assert report["original_map_auditor_sha256"] == sha(ROOT / "audit_streamed_hierarchy.py")
    assert report["composite_union_auditor_sha256"] == sha(ROOT / "certified_receipt_union.py")
    assert report["stream_reader_sha256"] == sha(ROOT / "stream_catalog.py")
    assert len(report["stages"]) == 2
    assert [s["threshold"] for s in report["stages"]] == [1, 0]
    assert [s["maps_checked"] for s in report["stages"]] == [1530509, 658305]
    assert [s["paid_types"] for s in report["stages"]] == [872204, 658305]
    assert [s["remaining_types"] for s in report["stages"]] == [658305, 0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hierarchy", type=Path, required=True)
    ap.add_argument("--union", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    registry = read(ROOT / "LARGE-OUTPUT-LOCATION.json")
    bulk = Path(registry["large_output_root"]).resolve()
    output = args.output.resolve()
    temporary = Path(str(output)+".building")
    assert output.is_relative_to(bulk) and output != bulk
    assert output.parent.exists() and not output.exists() and not temporary.exists()
    audit = read(args.hierarchy)
    check_hierarchy(audit)
    controls = read(EV / "n23-B13-cross-volume-freezer-controls-resume1/VERIFIED.json")
    assert controls["verified"] and controls["freezer_sha256"] == sha(Path(__file__))
    assert controls["source_sha256"] == sha(ROOT / "test_n23_b13_cross_volume_freezer.py")
    document = ROOT / "N23-B13-CATALOGUE-CLOSURE.md"
    text = document.read_text(encoding="utf8")
    assert "记录必要目录全部排除" in text and "1,530,509" in text
    assert "不是完整 n23 全局最优性证明" in text
    constants = SYN / "evidence/core-reduction/constants/n23.json"
    const = read(constants)
    assert const["verified"] and const["N"] == 23
    assert F(const["radius_upper"]) == F("249953776586051/1000000000000000")
    assert const["angle_scale"] == 10**7 and const["angle_caps"] == [804156, 1666328, 2698800]
    catalogdir = EV / "n23-B13-paid-streamed-resume1"
    catalogpath = catalogdir / "N23-B13-full-lossless-view.json"
    nativepath = catalogdir / "N23-B13-paid-residual.bin"
    viewpath = catalogdir / "N23-B13-full-lossless-view.view-audit.json"
    summarypath = catalogdir / "SUMMARY.json"
    view, summary = read(viewpath), read(summarypath)
    assert view["verified"] and view["complete_necessary_catalogue_view"]
    assert view["paid_branches_removed"] == 0 and view["all_rows_losslessly_compared"]
    assert view["orbits"] == 1530509 and (view["N"], view["B"]) == (23, 13)
    assert view["output_sha256"] == audit["catalog_sha256"] == sha(catalogpath)
    assert view["input_sha256"] == summary["catalog_sha256"] == sha(nativepath)
    assert view["summary_sha256"] == sha(summarypath)
    assert view["source_sha256"] == sha(ROOT / "materialize_unpruned_paid.py")
    assert summary["verified"] and summary["complete_residual_family_search"]
    assert summary["all_sorted_run_union_equality_verified"]
    assert summary["pruned_recursive_states_not_orbit_count"] == summary["payment_samples_independently_mapped"] == 0
    assert summary["residual_orbits"] == 1530509 and summary["run_count"] == 134
    assert summary["source_sha256"] == sha(ROOT / "enumerate_paid_family.py")
    native = BinaryRows(nativepath)
    assert native.header["proof_prunes"] == 0 and native.header["proof_payments"] == []
    assert native.header["calls"] == summary["calls"] == 694677316
    native.stream.close()
    outergroups = EV / "n23-B13-all-outer-groups-resume1/GROUPS.json"
    outerreceipt = EV / "n23-B13-all-outer-root-force-resume1/SUMMARY.json"
    outerreplay = EV / "n23-B13-all-outer-root-replay-resume1.json"
    fullgroups = EV / "n23-B13-rest-full-groups-resume1/GROUPS.json"
    first = Stage((outergroups, outerreceipt, outerreplay), 23, 13, audit["catalog_sha256"], 1530509)
    second = CompositeStage(fullgroups, args.union, 23, 13, audit["catalog_sha256"], 1530509)
    assert first.digest == audit["stages"][0]["groups_sha256"]
    assert second.digest == audit["stages"][1]["groups_sha256"]
    assert first.data["parent_groups_sha256"] is None and first.data["parent_proof_sha256"] is None
    assert second.data["parent_groups_sha256"] == first.digest
    assert second.data["parent_proof_sha256"] == sha(outerreceipt)
    assert len(first.paid) == 3242 and len(second.paid) == 658305
    assert audit["stages"][0]["force_replay_sha256"] == sha(outerreplay)
    assert audit["stages"][1]["force_replay_sha256"] == sha(args.union)
    assert first.data["bindings_sha256"] == audit["stages"][0]["bindings_sha256"]
    assert second.data["bindings_sha256"] == audit["stages"][1]["bindings_sha256"]
    first.stream.close()
    second.stream.close()
    union = checked_union_report(fullgroups, args.union)
    assert union["excluded_groups"] == union["catalog_members_excluded"] == 658305
    assert union["pending_groups"] == 0 and F(union["minimum_force_margin"]) > 0
    pendingpath = args.hierarchy.parent / audit["pending_indices_file"]
    assert pendingpath.stat().st_size == 0 and sha(pendingpath) == audit["pending_indices_sha256"]
    started = time.monotonic()
    with temporary.open("x", encoding="utf8") as stream:
        stream.write('{\n  "files": {\n')
        bindings = Bindings(stream, {"workspace": WORK, "bulk": bulk})
        basic = [
            Path(__file__), document, args.hierarchy, args.union, pendingpath, constants,
            catalogpath, nativepath, viewpath, summarypath,
            outergroups, outerreceipt, outerreplay, fullgroups,
            outergroups.parent / first.data["bindings_file"],
            fullgroups.parent / second.data["bindings_file"],
            catalogdir / "INPUT-BINDINGS.json",
            EV / "n23-B13-cross-volume-freezer-controls-resume1/VERIFIED.json",
            EV / "certified-receipt-union-controls-resume1/VERIFIED.json",
            EV / "composite-hierarchy-controls-resume2/VERIFIED.json",
        ]
        basic += [ROOT / name for name in (
            "test_n23_b13_cross_volume_freezer.py", "multiroot_snapshot.py", "audit_multiroot_snapshot.py",
            "test_certified_receipt_union.py", "test_composite_hierarchy.py",
            "audit_composite_hierarchy.py", "certified_receipt_union.py", "audit_streamed_hierarchy.py",
            "replay_group_stage.py", "exact_graph.py", "stream_catalog.py", "paid_binary_residual.py",
            "materialize_unpruned_paid.py", "group_catalog.py", "probe_groups.py",
            "recover_force_producer_prefix.py", "CROSS-VOLUME-CERTIFICATE-COMPOSITION.md",
            "PROOF-AWARE-PEELING.md")]
        basic += [SYN / "SHARED-CORE-REDUCTION.md", SYN / "core_reduction.py",
                  SYN / "round2-grouped/partial_force_exact.py"]
        for path in basic:
            bindings.add(path)
        launch = read(catalogdir / "INPUT-BINDINGS.json")
        assert summary["input_bindings_sha256"] == sha(catalogdir / "INPUT-BINDINGS.json")
        assert launch["files"] == summary["files"]
        for relative, expected in launch["files"].items():
            path = (WORK / relative).resolve()
            assert path.is_relative_to(WORK)
            bindings.add(path, expected)
        for name, expected in summary["run_sha256"].items():
            assert Path(name).name == name
            bindings.add(Path(str(nativepath)+".runs") / name, expected)
        for row in read(outerreceipt)["outcomes"]:
            if row["status"] == "excluded":
                bindings.add(certificate_path(outerreceipt, row), row["tree_sha256"])
        for component in union["components"]:
            receiptpath = Path(component["receipt_absolute_path"])
            replaypath = Path(component["replay_absolute_path"])
            bindings.add(receiptpath, component["receipt_sha256"])
            bindings.add(replaypath, component["replay_sha256"])
        for row in union["outcomes"]:
            assert row["status"] == "excluded"
            bindings.add(Path(row["certificate_absolute_path"]), row["tree_sha256"])
        stream.write('\n  },\n')
        footer = {"schema": "disk-cover-multiroot-snapshot-v1",
                  "roots": {"workspace": str(WORK), "bulk": str(bulk)},
                  "verified": True, "N": 23, "B": 13, "catalog_types": 1530509,
                  "recorded_catalogue_branch_closed": True,
                  "strict_exclusion_types_with_replayed_certificates": 1530509,
                  "file_count": bindings.count, "global_optimality_proved": False,
                  "scope": "entire n23 B13 recorded necessary-catalogue branch only",
                  "independent_all_file_integrity_still_required": True,
                  "source_sha256": sha(Path(__file__)),
                  "seconds": time.monotonic()-started}
        stream.write(json.dumps(footer, indent=2)[1:])
    assert not output.exists()
    temporary.rename(output)
    print("N23 B13 cross-volume branch snapshot PASS:", bindings.count,
          "files; independent all-file integrity still required; not whole n23 optimality", flush=True)


if __name__ == "__main__":
    main()
