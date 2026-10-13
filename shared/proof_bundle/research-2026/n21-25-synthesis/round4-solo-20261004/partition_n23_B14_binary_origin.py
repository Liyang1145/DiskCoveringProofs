"""Two-process full original-binary-family actual-cover origin partition."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import json
import random
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from paid_binary_residual import BinaryRows
from n25_outer_search import read, publish

assert __debug__
N, B, TOTAL = 23, 14, 8277632
UPPER = F(249953776586051, 10**15)


def source_gate(path):
    report = read(path)
    assert report["verified"]
    assert report["schema"] == "restored-N23-B14-historical-complete-source-and-fresh-union-gates-v1"
    assert report["source_sha256"] == sha(ROOT / "accept_n23_B14_restored_source.py")
    assert (report["N"], report["B"], report["residual_orbits"]) == (N, B, TOTAL)
    assert report["complete_recorded_necessary_family"]
    assert report["all_8726_original_launch_dependencies_explicitly_remapped_and_rehashed"]
    assert report["original_production_math_library_storage_and_launcher_gates_freshly_checked"]
    assert report["historical_actual_native_zero_terminal_phase_and_source_order_checked"]
    assert report["all_original_and_layer_inputs_fresh_complete_union_verified"]
    catalogpath = (ROOT / report["catalog_relative_to_round4"]).resolve()
    assert catalogpath.is_relative_to(ROOT) and sha(catalogpath) == report["catalog_sha256"]
    for item, digest in report["frozen_files"].items():
        assert sha(item) == digest
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constantspath)
    assert constants["verified"] and constants["N"] == N and F(constants["radius_upper"]) == UPPER
    assert 0 < UPPER < F(1, 4) and 1-3*UPPER > UPPER
    controlpath = ROOT / "n23-n24-cover-origin-necessity-controls-20261005-v1/VERIFIED.json"
    control = read(controlpath)
    assert control["verified"] and control["schema"] == "N23-N24-actual-cover-origin-necessity-controls-v1"
    assert control["source_sha256"] == sha(ROOT / "test_small_order_cover_origin.py")
    for item, digest in control["files_relative_to_workspace"].items():
        workpath = ROOT.parents[2] / item
        assert sha(workpath) == digest
    localcontrolpath = ROOT / "n23-B14-binary-origin-face-controls-20261005-v1/VERIFIED.json"
    localcontrol = read(localcontrolpath)
    assert localcontrol["verified"]
    assert localcontrol["schema"] == "N23-B14-binary-origin-functional-face-controls-v1"
    assert localcontrol["source_sha256"] == sha(ROOT / "test_n23_B14_binary_origin.py")
    assert localcontrol["partition_and_acceptor_source_sha256"] == sha(Path(__file__))
    assert localcontrol["all_exposed_positive_and_pure_inner_hidden_label_retained"]
    catalog = BinaryRows(catalogpath)
    assert (catalog.header["N"], catalog.header["B"], catalog.header["orbits"]) == (N, B, TOTAL)
    assert catalog.header["proof_prunes"] == 0 and catalog.header["proof_payments"] == []
    assert catalog.header["scale"] == constants["angle_scale"] and catalog.header["caps"] == constants["angle_caps"]
    catalog.stream.close()
    frozen = {
        str(item): sha(item) for item in (
            path, catalogpath, constantspath, controlpath, localcontrolpath, Path(__file__).resolve(),
            ROOT / "N23-N24-UNEXPOSED-ORIGIN-SOURCE.md", HIGH / "paid_binary_residual.py",
            HIGH / "stream_catalog.py")
    }
    return catalogpath, frozen


def independent_mask(faces):
    boundary = (1 << B)-1
    assert faces and faces == sorted(set(faces))
    exposure, all_labels = set(range(B)), set(range(B))
    for triangle in faces:
        assert type(triangle) is int and 0 < triangle < 1 << N and triangle.bit_count() == 3
        labels = [v for v in range(N) if triangle >> v & 1]
        all_labels.update(labels)
        if triangle & boundary:
            exposure.update(labels)
    assert all_labels == set(range(N)), "full source type must use all N labels"
    return sum(1 << vertex for vertex in exposure)


def header(kind, digest):
    return {"schema": "full-original-N23-B14-binary-origin-partition-ledger-v1",
            "N": N, "B": B, "catalog_sha256": digest, "kind": kind,
            "actual_cover_necessity_not_graph_geometry": True}


def audit(sourcepath, proposalpath, output):
    assert not output.exists()
    catalogpath, frozen = source_gate(sourcepath)
    proposal = read(proposalpath)
    assert proposal["schema"] == "full-original-N23-B14-binary-origin-proposal-v1"
    assert proposal["source_report_sha256"] == sha(sourcepath)
    assert proposal["source_sha256"] == sha(Path(__file__))
    assert proposal["catalog_sha256"] == sha(catalogpath)
    assert (proposal["N"], proposal["B"], proposal["source_types"]) == (N, B, TOTAL)
    paidpath, pendingpath = proposalpath.parent / "ORIGIN-OBSTRUCTIONS.jsonl", proposalpath.parent / "PENDING.jsonl"
    assert sha(paidpath) == proposal["obstructions_sha256"] and sha(pendingpath) == proposal["pending_sha256"]
    output.mkdir()
    seen = paid = pending = 0
    counts = Counter()
    started = time.monotonic()
    catalog = BinaryRows(catalogpath)
    with paidpath.open(encoding="ascii") as obstructions, pendingpath.open(encoding="ascii") as residual:
        assert json.loads(next(obstructions), object_pairs_hook=no_duplicate_keys) == header(
            "actual-cover-origin-obstruction", sha(catalogpath))
        assert json.loads(next(residual), object_pairs_hook=no_duplicate_keys) == header(
            "not-paid-by-origin-condition", sha(catalogpath))
        for index, row in catalog.rows():
            assert index == seen
            mask = independent_mask(row["faces"])
            obstruction = mask == (1 << N)-1
            stream = obstructions if obstruction else residual
            actual = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
            assert actual == {"index": index, "exposed_mask": mask}
            assert type(actual["index"]) is int and type(actual["exposed_mask"]) is int
            paid += obstruction
            pending += not obstruction
            seen += 1
            counts[mask.bit_count()] += 1
            if seen % 250000 == 0:
                print("N23/B14 independently audited", seen, "origin obstructions", paid,
                      "pending", pending, "seconds", round(time.monotonic()-started, 1), flush=True)
        assert not obstructions.read(1) and not residual.read(1)
    assert catalog.finished and seen == TOTAL == paid+pending
    assert paid == proposal["origin_obstructions"] and pending == proposal["pending_types"]
    assert dict(counts) == {int(key): value for key, value in proposal["exposure_histogram"].items()}
    for item, digest in frozen.items():
        assert sha(item) == digest
    assert sha(paidpath) == proposal["obstructions_sha256"] and sha(pendingpath) == proposal["pending_sha256"]
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "refine_collar_origin"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "independent-complete-original-N23-B14-origin-partition-v1",
        "N": N, "B": B, "source_types": seen, "origin_obstructions": paid,
        "pending_types": pending, "exposure_histogram": dict(sorted(counts.items())),
        "every_original_full_type_and_partition_index_freshly_scanned": True,
        "all_actual_exposed_faces_independently_recomputed": True,
        "binary_order_stabilizers_labels_counts_and_end_of_file_checked": True,
        "pure_internal_faces_do_not_expose_their_labels": True,
        "radius_upper": str(UPPER), "strict_gap_1_minus_4U": str(1-4*UPPER),
        "source_report_sha256": sha(sourcepath), "catalog_sha256": sha(catalogpath),
        "proposal_sha256": sha(proposalpath), "obstructions_sha256": sha(paidpath),
        "pending_sha256": sha(pendingpath), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "actual_cover_auxiliary_rod_interface_required_not_standalone_geometry": True,
        "remaining_lower_bounds_other_boundary_families_and_exact_upper_still_required": True,
        "global_optimality_proved": False,
    })
    print("Complete N23/B14 origin partition independently accepted:", paid, "obstructions;",
          pending, "still pending", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--proposal", type=Path)
    args = ap.parse_args()
    sourcepath, output = args.source.resolve(), args.output.resolve()
    assert sourcepath.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    if args.proposal:
        assert args.proposal.resolve().is_relative_to(ROOT)
        audit(sourcepath, args.proposal.resolve(), output)
        return
    from refine_collar_origin import exposed_mask
    catalogpath, frozen = source_gate(sourcepath)
    # Functional parameter controls use original boundary B14, not B15.
    rng = random.Random(23141005)
    for _ in range(100):
        faces = sorted({sum(1 << v for v in rng.sample(range(N), 3)) for _ in range(50)})
        used = 0
        for mask in faces:
            used |= mask
        if used == (1 << N)-1:
            assert independent_mask(faces) == exposed_mask(N, B, faces)
    output.mkdir()
    paidpath, pendingpath = output / "ORIGIN-OBSTRUCTIONS.jsonl", output / "PENDING.jsonl"
    seen = paid = pending = 0
    counts = Counter()
    catalog = BinaryRows(catalogpath)
    started = time.monotonic()
    with paidpath.open("x", encoding="ascii") as obstructions, pendingpath.open("x", encoding="ascii") as residual:
        for stream, kind in ((obstructions, "actual-cover-origin-obstruction"),
                             (residual, "not-paid-by-origin-condition")):
            stream.write(json.dumps(header(kind, sha(catalogpath)), separators=(",", ":"))+"\n")
        for index, row in catalog.rows():
            assert index == seen
            mask = exposed_mask(N, B, row["faces"])
            obstruction = mask == (1 << N)-1
            (obstructions if obstruction else residual).write(
                json.dumps({"index": index, "exposed_mask": mask}, separators=(",", ":"))+"\n")
            seen += 1
            paid += obstruction
            pending += not obstruction
            counts[mask.bit_count()] += 1
            if seen % 250000 == 0:
                print("N23/B14 origin proposals", seen, "obstructions", paid,
                      "pending", pending, "seconds", round(time.monotonic()-started, 1), flush=True)
    assert catalog.finished and seen == TOTAL == paid+pending
    for item, digest in frozen.items():
        assert sha(item) == digest
    proposalpath = output / "PROPOSAL.json"
    publish(proposalpath, {
        "schema": "full-original-N23-B14-binary-origin-proposal-v1",
        "N": N, "B": B, "source_types": seen, "origin_obstructions": paid, "pending_types": pending,
        "exposure_histogram": dict(sorted(counts.items())),
        "source_report_sha256": sha(sourcepath), "catalog_sha256": sha(catalogpath),
        "obstructions_sha256": sha(paidpath), "pending_sha256": sha(pendingpath),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "not_accepted_until_separate_fresh_full_scan": True, "global_optimality_proved": False,
    })
    with (output / "AUDIT-STDOUT.log").open("xb") as stdout, (output / "AUDIT-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen([
            sys.executable, "-u", str(Path(__file__).resolve()), "--source", str(sourcepath),
            "--proposal", str(proposalpath), "--output", str(output / "ACCEPTED")],
            stdout=stdout, stderr=stderr, cwd=str(ROOT),
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "AUDIT-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid,
        "source_sha256": sha(Path(__file__)), "independent_process_terminal_observed": True,
    })
    assert code == 0
    print("N23/B14 full binary origin proposal and independent full acceptance ended", flush=True)


if __name__ == "__main__":
    main()
