"""More-than-512-file union, real native quota failure, and bad-input controls."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import os
import struct
import subprocess
from paid_binary_residual import BinaryRows, verify_merge
from merge_paid_runs_bounded import finalize_runs, phase_metadata, check_union, producer_is_active
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists() and not args.output.is_absolute() and args.output.as_posix().isascii()
    assert producer_is_active(os.getpid()), "live-process negative gate not working"
    args.output.mkdir(parents=True)
    seed = ROOT / "evidence/paid-stream-storage-controls-resume2/N9-B8-noscreen-small-block.bin"
    header, _ = verify_merge(seed)
    rows = [row for _, row in BinaryRows(seed).rows()]
    assert len(rows) == 91
    N, B, F = 9, 8, 8
    assert F == 2*N-B-2
    runfolder = args.output / "520-runs"
    runfolder.mkdir()
    paths = []
    for i in range(520):
        path = runfolder / f"run-{i}.bin"
        row = rows[(i*37) % len(rows)]
        encoded = struct.pack("<"+"I"*(F+1), row["stabilizer"], *row["faces"])
        path.write_bytes(b"PAIDRUN1"+struct.pack("<IIIQ", N, B, F, 1)+encoded)
        paths.append(path)
    metadata = {key: value for key, value in header.items() if key != "orbits"}
    metadata.update(run_count=len(paths), rows_to_runs=len(paths), mode="dfs")
    target, report = finalize_runs(paths, metadata, args.output / "union520", fan_in=16)
    assert report["verified"] and report["residual_orbits"] == 91
    assert [row for _, row in BinaryRows(target).rows()] == rows
    assert len({entry for receipt in report["batch_receipts"] if receipt["layer"] == 0
                for entry in receipt["input_files"]}) == 520
    empty_metadata = dict(metadata, run_count=0, rows_to_runs=0)
    empty, emptyreport = finalize_runs([], empty_metadata, args.output / "empty", fan_in=16)
    assert emptyreport["residual_orbits"] == 0 and list(BinaryRows(empty).rows()) == []
    one, onereport = finalize_runs(paths[:1], dict(metadata, run_count=1, rows_to_runs=1),
                                  args.output / "one", fan_in=16)
    assert onereport["residual_orbits"] == 1
    negative = []
    mutations = [
        ("wrong-aggregate-count", paths, dict(metadata, rows_to_runs=521)),
        ("missing-run", paths[:-1], metadata),
        ("duplicate-run-path", paths[:-1]+paths[:1], metadata),
    ]
    for label, inputs, meta in mutations:
        try:
            finalize_runs(inputs, meta, args.output / f"invalid-{label}", fan_in=16)
        except AssertionError:
            negative.append(label)
        else:
            raise AssertionError(("invalid run union accepted", label))
    badfiles = []
    raw = paths[0].read_bytes()
    for label, badbytes in [
        ("truncated-record", raw[:-1]),
        ("extra-tail", raw+b"\0"),
        ("wrong-graph-dimensions", raw[:8]+struct.pack("<I", 10)+raw[12:]),
        ("zero-stabilizer", raw[:28]+b"\0"*4+raw[32:]),
    ]:
        badpath = args.output / f"bad-{label}.bin"
        badpath.write_bytes(badbytes)
        badfiles.append(badpath)
        try:
            finalize_runs([badpath], dict(metadata, run_count=1, rows_to_runs=1),
                          args.output / f"invalid-{label}", fan_in=16)
        except AssertionError:
            negative.append(label)
        else:
            raise AssertionError(("invalid binary accepted", label))
    wrongstab = args.output / "wrong-stabilizer-conflict.bin"
    source_stab = struct.unpack_from("<I", raw, 28)[0]
    replacement = 2 if source_stab != 2 else 1
    wrongstab.write_bytes(raw[:28]+struct.pack("<I", replacement)+raw[32:])
    try:
        finalize_runs([paths[0], wrongstab], dict(metadata, run_count=2, rows_to_runs=2),
                      args.output / "invalid-stabilizer-conflict", fan_in=16)
    except AssertionError:
        negative.append("duplicate-code-conflicting-stabilizers")
    else:
        raise AssertionError("stabilizer disagreement accepted")
    # Source header is a phase indicator, not proof by flag. Its exact format
    # and no-partial-rows condition are separately tested.
    phase = args.output / "synthetic-phase-only.building"
    encoded = json.dumps(metadata, separators=(",", ":")).encode("ascii")
    phase.write_bytes(b"PAIDRSV1"+struct.pack("<IIIIQ", N, B, F, len(encoded), 0)+encoded)
    assert phase_metadata(phase) == metadata
    for label, value in [
        ("partial-output-body", phase.read_bytes()+b"\0"),
        ("completed-count-not-premerge", phase.read_bytes()[:24]+struct.pack("<Q", 91)+phase.read_bytes()[32:]),
    ]:
        badpath = args.output / f"bad-phase-{label}.building"
        badpath.write_bytes(value)
        try:
            phase_metadata(badpath)
        except AssertionError:
            negative.append(label)
        else:
            raise AssertionError(("invalid repair phase accepted", label))
    # An actual native small-block exhaustive search commonly exceeds the
    # static CRT's file-stream quota. Its search is not rerun for recovery.
    native = args.output / "native-N11-B8.bin"
    proc = subprocess.Popen([str(ROOT / "peel_paid_stream_small.exe"), "11", "8", str(native),
                             "10000000", "2000000", "4200000", "4800000", "0", "dfs", "-"],
                            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = proc.communicate()
    assert not producer_is_active(proc.pid), "terminal process gate not working"
    (args.output / "native-stdout.log").write_bytes(stdout)
    (args.output / "native-stderr.log").write_bytes(stderr)
    nativecontrol = {"pid": proc.pid, "exit_code": proc.returncode, "search_restarted": False}
    if proc.returncode:
        assert stderr.rstrip().endswith(b"REJECTED run header")
        assert not native.exists()
        ph = phase_metadata(Path(str(native)+".building"))
        runpaths = [Path(str(native)+".runs") / f"run-{i}.bin" for i in range(ph["run_count"])]
        assert ph["run_count"] > 500
        restored, recovered = finalize_runs(runpaths, ph, args.output / "real-native-recovery", fan_in=16)
        reference = args.output / "native-N11-B8-old-reference.json"
        subprocess.run([str(ROOT / "peel_degree.exe"), "11", "8", str(reference),
                        "10000000", "2000000", "4200000", "4800000", "0", "dfs"],
                       cwd=ROOT, check=True, stderr=subprocess.DEVNULL)
        old = json.loads(reference.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)
        assert [row for _, row in BinaryRows(restored).rows()] == old["survivors"]
        nativecontrol.update(native_file_quota_failure_reproduced=True,
                             run_count=ph["run_count"], recovered_complete_orbits=recovered["residual_orbits"],
                             full_reference_set_equality=True,
                             phase_sha256=sha(Path(str(native)+".building")),
                             independent_reference_sha256=sha(reference),
                             recovered_sha256=sha(restored))
    else:
        ph, _ = verify_merge(native)
        nativecontrol.update(native_file_quota_failure_reproduced=False, run_count=ph["run_count"],
                             native_completed_without_recovery=True)
    result = {"verified": True, "520_input_runs_complete_union_compared": True,
              "positive_controls": 4, "negative_controls_rejected": negative,
              "all_fixture_inputs_preserved": True, "native_control": nativecontrol,
              "synthetic_520_run_merge": report, "source_sha256": sha(Path(__file__)),
              "merge_source_sha256": sha(ROOT / "merge_paid_runs_bounded.py"),
              "native_small_binary_sha256": sha(ROOT / "peel_paid_stream_small.exe"),
              "global_optimality_proved": False,
              "scope": "bounded exact finalization and real failure controls only"}
    (args.output / "VERIFIED.json").write_text(json.dumps(result, indent=2), encoding="utf8")
    print("Bounded finalization controls PASS:", len(negative), "bad inputs rejected;",
          "520-file union exact;", nativecontrol, flush=True)


if __name__ == "__main__":
    main()
