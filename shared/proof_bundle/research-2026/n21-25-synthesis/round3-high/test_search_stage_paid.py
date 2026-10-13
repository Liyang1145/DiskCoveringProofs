"""Fresh complete-set checks for both staged paid search binaries."""
from pathlib import Path
import argparse
import json
import struct
import subprocess
from merge_paid_runs_bounded import phase_metadata, finalize_runs
from paid_binary_residual import BinaryRows
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(Path(path).read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def run_stage(binary, N, B, target, table, *, mode="dfs", prefix="-", count=0,
              caps=(804156, 1666328, 2698800)):
    return subprocess.run(
        [str(ROOT / binary), str(N), str(B), str(target), "10000000",
         *map(str, caps), "0", mode, str(table), str(prefix), str(count)],
        cwd=ROOT, capture_output=True)


def finish(target, output):
    assert not target.exists()
    metadata = phase_metadata(Path(str(target)+".building"))
    paths = [Path(str(target)+".runs") / f"run-{i}.bin" for i in range(metadata["run_count"])]
    final, receipt = finalize_runs(paths, metadata, output, fan_in=16)
    assert receipt["every_batch_complete_union_equality_verified"]
    return metadata, [row for _, row in BinaryRows(final).rows()]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    basepath = ROOT / "evidence/search-stage-controls-resume1/VERIFIED.json"
    base = read(basepath)
    assert base["verified"] and base["source_sha256"] == sha(ROOT / "test_search_stage.py")
    for name, digest in base["native_sources_sha256"].items():
        assert sha(ROOT / name) == digest
    reports = []
    cases = [
        ("pair", 19, 13, "peel_search_stage.exe",
         ROOT / "evidence/n22-portable-strict-obstacles-resume1/OBSTACLES.tsv",
         ROOT / "evidence/paid-N19-B13-residual-resume1.bin",
         ROOT / "evidence/paid-N19-B13-full-partition-resume1.json"),
        ("outer", 20, 13, "peel_outer_search_stage.exe",
         ROOT / "evidence/n23-portable-outer-obstacles-resume1/OBSTACLES.tsv",
         ROOT / "evidence/outer-paid-controls-resume1/N20-B13-paid.bin",
         ROOT / "evidence/outer-paid-controls-resume1/VERIFIED.json"),
    ]
    for tag, N, B, binary, table, reference, proof in cases:
        verified = read(proof)
        assert verified["verified"]
        reference_key = "residual_sha256"
        assert sha(reference) == verified[reference_key]
        old = BinaryRows(reference)
        expected = [row for _, row in old.rows()]
        target = args.output / f"{tag}.bin"
        process = run_stage(binary, N, B, target, table, caps=old.header["caps"])
        assert process.returncode == 0, process.stderr
        metadata, actual = finish(target, args.output / f"{tag}-finalized")
        assert actual == expected
        for key in ("calls", "prunes", "rooted", "rows_to_runs", "run_count",
                    "proof_prunes", "paid_match_queries", "proof_payments"):
            assert metadata[key] == old.header[key], (tag, key)
        assert metadata["proof_prunes"] > 0
        reports.append({"variant": tag, "N": N, "B": B, "residual_orbits": len(actual),
                        "full_set_and_stabilizers_match": True,
                        "all_native_search_counters_and_payments_match": True,
                        "old_independent_missing_type_payments_sha256": sha(proof),
                        "reference_sha256": sha(reference)})
    # Exercise the outer binary's nonempty storage path, not only its empty
    # paid regression. This is a graph/storage control, not n11 formalization.
    target = args.output / "outer-empty-library.bin"
    proc = run_stage("peel_outer_search_stage.exe", 11, 8, target, "-",
                     caps=(2000000, 4200000, 4800000))
    assert proc.returncode == 0, proc.stderr
    meta, actual = finish(target, args.output / "outer-empty-library-finalized")
    expectedpath = ROOT / "evidence/bounded-run-merge-controls-final-resume1/native-N11-B8-old-reference.json"
    assert actual == read(expectedpath)["survivors"] and actual
    # Same-length prefix corruptions must be detected, not just truncations.
    raw = (args.output / "pair.bin.runs/run-0.bin").read_bytes()
    bad = []
    for label, offset, value in (("wrong-N", 8, 20), ("wrong-stabilizer", 28, 999),
                                  ("wrong-first-face", 32, 1)):
        folder = args.output / f"bad-{label}"
        folder.mkdir()
        changed = bytearray(raw)
        struct.pack_into("<I", changed, offset, value)
        (folder / "run-0.bin").write_bytes(changed)
        target = args.output / f"reject-{label}.bin"
        proc = run_stage("peel_search_stage.exe", 19, 13, target, cases[0][4],
                         prefix=folder, count=1, caps=(815002, 1690622, 2746810))
        assert proc.returncode != 0 and not Path(str(target)+".building").exists()
        bad.append(label)
    result = {"verified": True, "base_controls_sha256": sha(basepath),
              "both_paid_variants_complete_regression": reports,
              "outer_nonempty_storage_full_reference_match": True,
              "outer_nonempty_reference_sha256": sha(expectedpath),
              "negative_controls_rejected": bad,
              "source_sha256": sha(Path(__file__)),
              "binary_sha256": {name: sha(ROOT / name) for name in
                                ("peel_search_stage.exe", "peel_outer_search_stage.exe")},
              "global_optimality_proved": False,
              "scope": "paid staged search complete-set and bad-prefix controls only"}
    (args.output / "VERIFIED.json").write_text(json.dumps(result, indent=2), encoding="utf8")
    print("Paid search-stage controls PASS: both full paid sets, counters and payments equal;",
          "outer nonempty storage and three same-length corruptions checked", flush=True)


if __name__ == "__main__":
    main()
