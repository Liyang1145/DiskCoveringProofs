"""Gate and content-bind the COMPLETE n22 unrestricted source-proof chain.

This refuses incomplete or weak-replay hierarchy reports. It writes a
temporary streaming manifest and publishes it only after every mathematical
interface, component binding and required certificate file passes.
The written topology/peeling proof is not machine formalization.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import os
import time
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
SYN = ROOT.parent
WORK = ROOT.parents[2]
EV = ROOT / "evidence"
WORK_CANONICAL = WORK.resolve()
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


class Bindings:
    def __init__(self, stream):
        self.stream = stream
        self.seen = set()
        self.parent_cache = {}
        self.count = 0
        self.started = time.monotonic()

    def add(self, path, expected=None):
        path = Path(path)
        key = str(path.parent.absolute())
        if key not in self.parent_cache:
            self.parent_cache[key] = path.parent.resolve()
        canonical = self.parent_cache[key] / path.name
        assert canonical.is_relative_to(WORK_CANONICAL)
        assert not canonical.is_symlink(), ("unresolved file symlink", str(path))
        digest = sha(canonical)
        assert expected is None or digest == expected, ("changed proof input", str(path))
        relative = canonical.relative_to(WORK_CANONICAL).as_posix()
        if relative not in self.seen:
            if self.count:
                self.stream.write(",\n")
            self.stream.write("    "+json.dumps(relative)+": "+json.dumps(digest))
            self.seen.add(relative)
            self.count += 1
            if self.count % 10000 == 0:
                self.stream.flush()
                print("N22 accepted files bound", self.count,
                      "seconds", round(time.monotonic()-self.started, 1), flush=True)
        return digest


def check_stage(B, info, stage, receiptpath, replaypath, bindings):
    grouppath = EV / f"n22-B{B}-{stage}-resume1/GROUPS.json"
    groups, receipt, replay = map(read, (grouppath, receiptpath, replaypath))
    digest = bindings.add(grouppath, info["groups_sha256"])
    assert (groups["N"], groups["B"]) == (receipt["N"], receipt["B"]) == (
        replay["N"], replay["B"]) == (22, B)
    assert groups["full_selected_catalog_scanned"]
    assert groups["threshold"] == info["threshold"] == {"pair": 2, "outer": 1, "full": 0}[stage]
    assert groups["selected_types"] == info["maps_checked"]
    assert groups["bindings_sha256"] == info["bindings_sha256"] == replay["bindings_sha256"]
    assert replay["verified"] and replay["groups_sha256"] == receipt["groups_sha256"] == digest
    assert replay["source_sha256"] == sha(ROOT / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
    assert replay["receipt_sha256"] == bindings.add(receiptpath)
    assert info["force_replay_sha256"] == bindings.add(replaypath)
    assert replay["associated_member_count"] == info["paid_types"]
    assert replay["exact_groups_replayed"] == receipt["excluded_groups"]
    assert replay["pending_groups"] == receipt["pending_groups"]
    assert receipt["catalog_members_excluded"] == replay["associated_member_count"]
    assert F(replay["minimum_force_margin"]) > 0
    bindings.add(grouppath.parent / groups["bindings_file"], groups["bindings_sha256"])
    assert [row["id"] for row in groups["groups"]] == list(range(groups["group_count"]))
    outcomes = receipt["outcomes"]
    assert sorted(row["group"] for row in outcomes) == list(range(groups["group_count"]))
    members = paid = 0
    for row in outcomes:
        assert row["status"] in ("excluded", "pending")
        if row["status"] != "excluded":
            continue
        group = groups["groups"][row["group"]]
        assert row["members"] == group["members"]
        path = (receiptpath.parent / row["certificate_path_relative_to_receipt"]
                if "certificate_path_relative_to_receipt" in row else
                receiptpath.parent / f"group-{row['group']:07}.json.gz")
        bindings.add(path, row["tree_sha256"])
        members += row["members"]
        paid += 1
    assert paid == replay["exact_groups_replayed"]
    assert members == replay["associated_member_count"]
    assert members + info["remaining_types"] == info["maps_checked"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--preflight-only", action="store_true",
                    help="Validate completion interfaces without writing or hashing all tree files.")
    args = ap.parse_args()
    out = args.output.resolve()
    temporary = out.with_suffix(out.suffix+".building")
    assert out.parent.is_relative_to(EV.resolve())
    assert not out.exists() and not temporary.exists()
    # Refuse before creating even a temporary completion record.
    proofpath = ROOT / "N22-GLOBAL-PROOF.md"
    proof = proofpath.read_text(encoding="utf8")
    assert "本稿是已经闭合的计算机辅助源证明" in proof
    assert "r_D(22)=sqrt(t_*)" in proof
    assert "N22-GLOBAL-SNAPSHOT" in proof
    constants = SYN / "evidence/core-reduction/constants/n22.json"
    reductionpath = EV / "n22-reduction-stdlib-resume1.json"
    reduction = read(reductionpath)
    assert reduction["verified"] and reduction["N"] == 22
    assert reduction["source_sha256"] == sha(ROOT / "n22_reduction_stdlib.py")
    assert reduction["constants_sha256"] == sha(constants)
    assert reduction["families"] == [[13, 9], [14, 8], [15, 7]]
    assert F(reduction["strict_core_gap"]) > 0
    assert F(reduction["circle_capacity_sine_gap"]) > 0
    interfacepath = EV / "n22-interfaces-resume1/INTERFACES.json"
    interfaces = read(interfacepath)
    assert interfaces["verified"] and interfaces["N"] == 22 and interfaces["dimension"] == 252
    assert interfaces["same_root_entire_closed_disk_upper"]
    assert interfaces["root_and_geometric_isolation_freshly_replayed"]
    assert interfaces["source_sha256"] == sha(ROOT / "replay_n22_interfaces.py")
    interfacefolder = interfacepath.parent / "evidence/n22"
    rootpath = interfacefolder / "algebraic-check1/root-verified.json"
    upperpath = interfacefolder / "algebraic-check1/upper-verified.json"
    localpath = interfacefolder / "local-isolation-certificate.json"
    root, upper, isolation = map(read, (rootpath, upperpath, localpath))
    assert all(row["verified"] for row in (root, upper, isolation))
    assert interfaces["root_report_sha256"] == reduction["root_report_sha256"] == sha(rootpath)
    assert interfaces["upper_report_sha256"] == sha(upperpath)
    assert interfaces["local_certificate_sha256"] == sha(localpath)
    assert root["root_sha256"] == upper["root_sha256"] == isolation["root_sha256"] == interfaces["root_sha256"]
    assert root["system_sha256"] == interfaces["system_sha256"]
    assert root["shared_evaluator_sha256"] == sha(SYN.parent / "n21-global/root_certificate.py")
    assert (root["N"], root["D"], root["G"], root["B"], root["M"]) == (22, 252, 126, 14, 112)
    assert [F(row["rho"]) for row in root["boxes"]] == [F(1, 10**60), F(1, 10**80)]
    assert all(0 <= F(row["inclusion"]) < 1 and 0 <= F(row["contraction"]) < 1
               for row in root["boxes"])
    assert F(root["r_strict_interval"][1]) < F(reduction["radius_upper"])
    freshroot = interfacefolder / "core-root.json"
    freshsystem = interfacefolder / "core-system.json"
    assert sha(freshroot) == root["root_sha256"]
    assert sha(freshsystem) == root["system_sha256"]
    assert sha(interfacefolder / "candidate-numeric.json") == sha(SYN / "evidence/n22/candidate-numeric.json")
    assert (upper["vertices"], upper["edges"], upper["triangles"], upper["caps"]) == (36, 91, 56, 14)
    assert upper["same_core_root_entire_disk_upper"] and upper["cover_radius_equals_core_radius"]
    assert isolation["positive_leading_principal_minors"] == isolation["geometry_dimension"] == 126
    assert F(isolation["isolation_margin"]) == F(7, 50000)
    assert (isolation["gamma"], F(isolation["lambda"]), F(isolation["nu"]),
            F(isolation["anchor_radius"])) == (500, F(1, 2000), F(1, 100), F(3, 50))
    assert interfaces["root_acceptor_sha256"] == root["source_sha256"] == sha(SYN / "algebraic_roots.py")
    assert interfaces["local_acceptor_sha256"] == isolation["source_sha256"] == sha(SYN / "local_certificates.py")
    scalarpath = EV / "n22-symmetry-cubic-replay-resume1.json"
    scalar = read(scalarpath)
    assert scalar["verified"] and scalar["candidate_symmetry_D7_certified"]
    assert scalar["source_sha256"] == sha(ROOT / "n22_symmetry_link.py")
    assert scalar["root_sha256"] == root["root_sha256"]
    assert scalar["system_sha256"] == root["system_sha256"]
    originalrootreport = SYN / "evidence/n22/algebraic-check1/root-verified.json"
    assert scalar["paid_unique_root_report_sha256"] == sha(originalrootreport)
    assert read(originalrootreport) == root
    assert scalar["linked_radius_square_polynomial_ascending"] == [-1, 19, -55, 29]
    assert scalar["radius_square_isolating_interval"] == ["641/10000", "321/5000"]
    sixpath = EV / "six-lower-stdlib-resume1.json"
    six = read(sixpath)
    assert six["verified"] and six["source_sha256"] == sha(ROOT / "replay_six_stdlib.py")
    assert reduction["six_report_sha256"] == sha(sixpath)
    assert F(six["radius"]) == F(2771, 5000) and six["topology_orbits"] == 3
    assert six["independently_enumerated_fixed_boundary_types"] == 14
    assert six["force_kernel_sha256"] == sha(SYN / "round2-grouped/partial_force_exact.py")
    trigpath = WORK / "research-2026/disk-cover-proof-library/external/pinned/cover20/proof_bundle/core/exact_arcs.py"
    assert six["trig_source_sha256"] == reduction["trig_source_sha256"] == sha(trigpath)
    b14path = EV / "N22-B14-CATALOGUE-CLOSURE-strict-resume2.json"
    b14 = read(b14path)
    assert b14["verified"] and b14["all_components_hash_bound"]
    assert b14["source_sha256"] == sha(ROOT / "close_n22_b14_catalogue.py")
    assert b14["strict_exclusion_types"] == 3080857 and b14["attaining_core_types"] == 1
    assert not b14["pending_catalog_indices"]
    assert b14["fresh_interfaces_sha256"] == sha(interfacepath)
    assert b14["radius_link_report_sha256"] == sha(scalarpath)
    corepath = EV / "n22-full-attaining-core-strict-replay-resume2.json"
    core = read(corepath)
    assert core["verified"] and b14["core_case_sha256"] == sha(corepath)
    assert core["source_sha256"] == sha(ROOT / "n22_core_case.py")
    assert core["root_sha256"] == root["root_sha256"]
    assert core["system_sha256"] == root["system_sha256"]
    assert core["root_report_sha256"] == sha(originalrootreport)
    assert core["local_certificate_sha256"] == sha(localpath)
    assert core["catalog_index"] == 3080857 and core["full_group"] == 384769
    assert core["counts"] == {"SPLIT": 2210, "DUAL": 2186, "LOCAL": 25}
    assert core["nodes"] == 4421 and F(core["minimum_local_margin"]) > 0
    assert F(core["minimum_force_margin"]) > 0
    assert core["transfer_checker_sha256"] == sha(ROOT / "audit_streamed_hierarchy.py")
    assert core["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
    assert core["force_kernel_sha256"] == sha(SYN / "round2-grouped/partial_force_exact.py")
    assert core["constants_sha256"] == sha(constants)
    assert core["tree_sha256"] == sha(EV / "n22-core-angle-resume2/core-angle-tree.json.gz")
    assert sha(SYN / "evidence/n22/core-root.json") == root["root_sha256"]
    assert sha(SYN / "evidence/n22/core-system.json") == root["system_sha256"]
    assert sha(SYN / "evidence/n22/local-isolation-certificate.json") == sha(localpath)
    controls = EV / "independent-transfer-controls-restored-resume2.json"
    ctrl = read(controls)
    assert ctrl["verified"] and ctrl["positive_controls"] == 2
    assert len(ctrl["negative_controls_rejected"]) == 11
    assert ctrl["auditor_sha256"] == sha(ROOT / "audit_streamed_hierarchy.py")
    assert ctrl["source_sha256"] == sha(ROOT / "audit_transfer_controls.py")
    required_audits = {
        13: EV / "n22-B13-hierarchy-audit-complete-resume1.json",
        14: EV / "n22-B14-hierarchy-audit-strict-final-resume2.json",
        15: EV / "n22-B15-hierarchy-audit-strict-final-resume2.json",
    }
    totals = {}
    for B, expected in ((13, 1791859), (14, 3080858), (15, 2047149)):
        audit = read(required_audits[B])
        assert audit["verified"] and audit["disjoint_hierarchy_partition_verified"]
        assert audit["source_sha256"] == sha(ROOT / "audit_streamed_hierarchy.py")
        assert audit["stream_reader_sha256"] == sha(ROOT / "stream_catalog.py")
        assert (audit["N"], audit["B"], audit["catalog_types"]) == (22, B, expected)
        pendingpath = required_audits[B].parent / audit["pending_indices_file"]
        assert sha(pendingpath) == audit["pending_indices_sha256"]
        pending = [json.loads(line)["index"] for line in pendingpath.open(encoding="utf8")]
        assert pending == ([3080857] if B == 14 else [])
        assert audit["pending_types"] == len(pending)
        assert audit["strict_exclusion_types_with_replayed_certificates"] == expected-len(pending)
        assert B == 14 or audit["coverage_partition_complete"]
        assert all(info["force_replay_sha256"] is not None for info in audit["stages"])
        assert [info["threshold"] for info in audit["stages"]] == [2, 1, 0]
        assert sum(info["paid_types"] for info in audit["stages"]) + len(pending) == expected
        if B == 14:
            assert b14["hierarchy_audit_sha256"] == sha(required_audits[B])
            assert b14["pending_indices_sha256"] == sha(pendingpath)
            assert b14["full_force_replay_sha256"] == audit["stages"][-1]["force_replay_sha256"]
            assert core["catalog_sha256"] == audit["catalog_sha256"]
            assert core["groups_sha256"] == audit["stages"][-1]["groups_sha256"]
            assert core["bindings_sha256"] == audit["stages"][-1]["bindings_sha256"]
        totals[str(B)] = {"catalogue_types": expected, "strict_excluded": expected-len(pending),
                          "core_lower_bound": len(pending), "unpaid_after_core": 0,
                          "stage_paid_types": [info["paid_types"] for info in audit["stages"]]}
    assert sum(t["catalogue_types"] for t in totals.values()) == 6919866
    assert sum(t["strict_excluded"] for t in totals.values()) == 6919865
    if args.preflight_only:
        print("N22 completion interface preflight PASS; no snapshot written; tree-byte binding remains", flush=True)
        return
    freezercontrolpath = EV / "n22-global-freezer-controls-final-resume1.json"
    freezercontrols = read(freezercontrolpath)
    assert freezercontrols["verified"] and freezercontrols["positive_controls"] == 2
    assert len(freezercontrols["negative_controls_rejected"]) == 14
    assert freezercontrols["source_sha256"] == sha(ROOT / "test_freeze_n22_global.py")
    assert freezercontrols["freezer_sha256"] == sha(ROOT / "freeze_n22_global.py")
    assert not freezercontrols["frozen_inputs_modified"] and not freezercontrols["snapshot_written"]
    out.parent.mkdir(parents=True, exist_ok=True)
    with temporary.open("x", encoding="utf8") as stream:
        stream.write('{\n  "files": {\n')
        bindings = Bindings(stream)
        for path in (proofpath, constants, reductionpath, interfacepath, rootpath,
                     upperpath, localpath, scalarpath, sixpath, b14path, corepath, controls,
                     freezercontrolpath):
            bindings.add(path)
        for path in interfacefolder.rglob("*"):
            if path.is_file():
                bindings.add(path)
        # Original root geometry is an input of core/scalar replays.
        for name in ("core-system.json", "core-root.json", "local-isolation-certificate.json",
                     "candidate-numeric.json"):
            bindings.add(SYN / "evidence/n22" / name)
        bindings.add(SYN / "evidence/n22/algebraic-check1/root-verified.json")
        bindings.add(ROOT / "evidence/n22-core-angle-resume2/core-angle-tree.json.gz", core["tree_sha256"])
        for path in (
            ROOT / "freeze_n22_global.py", ROOT / "n22_reduction_stdlib.py",
            ROOT / "replay_n22_interfaces.py", ROOT / "replay_six_stdlib.py",
            ROOT / "replay_group_stage.py", ROOT / "exact_graph.py",
            ROOT / "audit_streamed_hierarchy.py", ROOT / "audit_transfer_controls.py",
            ROOT / "stream_catalog.py", ROOT / "close_n22_b14_catalogue.py",
            ROOT / "n22_core_case.py", ROOT / "replay_candidate.py",
            ROOT / "n22_symmetry_link.py", ROOT / "N22-RADIUS-LINK.md",
            ROOT / "N22-GLOBAL-REQUIREMENTS-AUDIT.md",
            ROOT / "audit_snapshot_files.py", ROOT / "test_freeze_n22_global.py",
            SYN / "SHARED-CORE-REDUCTION.md",
            SYN / "algebraic_roots.py", SYN / "local_certificates.py",
            SYN / "peel_synthesis.cpp", ROOT / "peel_high.exe",
            SYN / "round2-grouped/partial_force_exact.py",
            SYN.parent / "n21-global/root_certificate.py",
            SYN.parent / "n13-global/independent_checks.py",
            WORK / "research-2026/disk-cover-proof-library/external/pinned/cover20/proof_bundle/core/exact_arcs.py",
        ):
            bindings.add(path)
        sixfolder = SYN.parent / "n21-global/evidence"
        bindings.add(sixfolder / "peeling-round1/N6-B6-noscreen.json", six["six_census_sha256"])
        assert len(six["trees"]) == 3 and sorted(row["index"] for row in six["trees"]) == [0, 1, 2]
        for row in six["trees"]:
            assert row["verified"] and F(row["minimum_margin"]) > 0
            bindings.add(sixfolder / f"six-core-exclusion/hexagon-{row['index']}.json.gz",
                         row["tree_sha256"])
        for B in (13, 14, 15):
            auditpath = required_audits[B]
            audit = read(auditpath)
            bindings.add(auditpath)
            bindings.add(auditpath.parent / audit["pending_indices_file"], audit["pending_indices_sha256"])
            cataloguefolder = EV / f"n22-B{B}-dfs-resume1"
            cataloguepath = cataloguefolder / f"N22-B{B}-dfs.json"
            summarypath = cataloguefolder / "SUMMARY.json"
            summary = read(summarypath)
            assert summary["complete"] and summary["N"] == 22 and summary["B"] == B
            assert summary["orbits"] == totals[str(B)]["catalogue_types"]
            assert summary["source_sha256"] == sha(SYN / "peel_synthesis.cpp")
            assert summary["binary_sha256"] == sha(ROOT / "peel_high.exe")
            assert summary["constants_sha256"] == sha(constants)
            bindings.add(summarypath)
            bindings.add(cataloguepath, summary["catalog_sha256"])
            assert summary["catalog_sha256"] == audit["catalog_sha256"]
            receipts = (
                EV / f"n22-B{B}-pair-root-resume1/SUMMARY.json",
                EV / ("n22-B13-outer-combined-resume1.json" if B == 13 else
                      f"n22-B{B}-outer-root-resume1/SUMMARY.json"),
                EV / ("n22-B13-full-root-resume1/SUMMARY.json" if B == 13 else
                      "n22-B14-full-combined-final-resume1.json" if B == 14 else
                      "n22-B15-full-combined-final-strict-resume2.json"),
            )
            replays = (
                EV / f"n22-B{B}-pair-replay-resume1.json",
                EV / f"n22-B{B}-outer-replay-resume1.json",
                EV / ("n22-B13-full-replay-resume1.json" if B == 13 else
                      "n22-B14-full-final-replay-strict-resume1.json" if B == 14 else
                      "n22-B15-full-final-replay-strict-resume2.json"),
            )
            for info, stage, receiptpath, replaypath in zip(audit["stages"],
                                                           ("pair", "outer", "full"), receipts, replays):
                check_stage(B, info, stage, receiptpath, replaypath, bindings)
        stream.write("\n  },\n")
        metadata = {
            "schema": "n22-unrestricted-written-and-exact-certificate-proof-v1",
            "verified": True,
            "N": 22, "global_optimality_source_proof_completed": True,
            "written_arbitrary_cover_and_peeling_argument": "N22-GLOBAL-PROOF.md",
            "mathematical_argument_is_not_machine_formalized": True,
            "formalization_completed": False, "third_party_peer_review_completed": False,
            "r_strict_interval": root["r_strict_interval"],
            "radius_square_polynomial_ascending": [-1, 19, -55, 29],
            "radius_square_isolating_interval": ["641/10000", "321/5000"],
            "type_closure": totals, "file_count": bindings.count,
            "remaining_five_target_global_proofs": [25, 23, 24],
        }
        tail = json.dumps(metadata, indent=2)[1:]
        stream.write(tail)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    assert not out.exists()
    temporary.rename(out)
    print("N22 COMPLETE unrestricted source-proof snapshot published:", bindings.count,
          "files; five-target goal remains active", flush=True)


if __name__ == "__main__":
    main()
