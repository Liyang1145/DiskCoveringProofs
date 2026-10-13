"""Complete external-merge checks with forced small blocks and bad-file controls."""
from pathlib import Path
import argparse
import json
import shutil
import struct
import subprocess
from paid_binary_residual import BinaryRows, verify_merge
from stream_catalog import Catalog, sha, no_duplicate_keys
from test_paid_matcher import check_derivation

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def check_stream_derivation():
    check_derivation()
    old = (ROOT / "peel_paid_kernel.inc").read_text(encoding="utf8")
    changes = [
        ('#include "paid_matcher.inc"', '#include "paid_matcher.inc"\n#include "paid_stream_storage.inc"'),
        ('<<" residual="<<survivors.size()<<" proof_prunes="<<proof_prunes',
         '<<" residual_block="<<survivors.size()<<" rows_to_runs="<<rows_to_runs<<" proof_prunes="<<proof_prunes'),
        ('if(!fresh&&iterator->second!=stabilizer)throw runtime_error("inconsistent stabilizer");',
         'if(!fresh&&iterator->second!=stabilizer)throw runtime_error("inconsistent stabilizer");\n  if(survivors.size()>=SURVIVOR_BLOCK)flush_paid_run();'),
        ('load_obstacles(argv[10]);', 'load_obstacles(argv[10]);\n initialize_paid_storage(output);'),
    ]
    for before, after in changes:
        assert old.count(before) == 1
        old = old.replace(before, after, 1)
    begin = old.index(' ofstream f(output);')
    end = old.index(' return 0;', begin)
    old = old[:begin]+(
        ' auto unique_count=merge_paid_runs(mode);\n'
        ' cerr<<"RESIDUAL COMPLETE B="<<b<<" calls="<<calls<<" orbits="<<unique_count<<" proof_prunes="<<proof_prunes<<"\\n";\n'
    )+old[end:]
    assert old == (ROOT / "peel_paid_stream_kernel.inc").read_text(encoding="utf8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists() and not args.output.is_absolute() and args.output.as_posix().isascii()
    args.output.mkdir(parents=True)
    check_stream_derivation()
    prior = read(ROOT / "evidence/paid-matcher-controls-resume1/VERIFIED.json")
    assert prior["verified"] and prior["binary_sha256"] == sha(ROOT / "peel_paid.exe")
    for name, digest in prior["native_sources_sha256"].items():
        assert sha(ROOT / name) == digest
    comparisons = []
    crossed_duplicates = False
    negatives = []
    corrupt_source = None
    for B, I in ((3, 0), (3, 1), (3, 4), (6, 0), (6, 2), (8, 1)):
        N = B+I
        for mode in ("noscreen", "audit-noscreen"):
            reference = ROOT / "evidence/paid-matcher-controls-resume1" / f"N{N}-B{B}-{mode}-reference.json"
            old = read(reference)
            for variant in ("production", "small-block"):
                binary = ROOT / ("peel_paid_stream.exe" if variant == "production" else
                                 "peel_paid_stream_small.exe")
                output = args.output / f"N{N}-B{B}-{mode}-{variant}.bin"
                subprocess.run([str(binary), str(N), str(B), str(output), "10000000",
                                "815002", "1690622", "2746810", "0", mode, "-"],
                               cwd=ROOT, check=True, stderr=subprocess.DEVNULL)
                header, runs = verify_merge(output)
                catalogue = BinaryRows(output)
                assert [row for _, row in catalogue.rows()] == old["survivors"]
                assert header["survivor_block_size"] == (100000 if variant == "production" else 7)
                if header["rows_to_runs"] > header["orbits"] and header["run_count"] > 1:
                    crossed_duplicates = True
                    corrupt_source = output
                try:
                    Catalog(output)
                except (AssertionError, ValueError, UnicodeError):
                    negatives.append(f"N{N}-B{B}-{mode}-{variant}-not-full")
                else:
                    raise AssertionError("binary residual incorrectly treated as a full catalogue")
                comparisons.append({"N": N, "B": B, "mode": mode, "variant": variant,
                                    "orbits": header["orbits"], "run_count": header["run_count"],
                                    "rows_to_runs": header["rows_to_runs"], "output_sha256": sha(output),
                                    "run_sha256": [sha(row.path) for row in runs]})
    assert crossed_duplicates and corrupt_source is not None
    empty = args.output / "initial-negative-cycle-empty.bin"
    subprocess.run([str(ROOT / "peel_paid_stream.exe"), "3", "3", str(empty), "10000000",
                    "1", "2", "3", "0", "dfs", "-"], cwd=ROOT, check=True, stderr=subprocess.DEVNULL)
    header, _ = verify_merge(empty)
    assert header["orbits"] == header["run_count"] == header["rows_to_runs"] == 0
    limited = args.output / "node-limit-no-final.bin"
    result = subprocess.run([str(ROOT / "peel_paid_stream.exe"), "23", "13", str(limited),
                             "10000000", "804156", "1666328", "2698800", "1", "dfs", "-"],
                            cwd=ROOT, capture_output=True)
    assert result.returncode != 0 and not limited.exists()
    negatives.append("node-limit-no-final-output")
    raw = corrupt_source.read_bytes()
    length = struct.unpack_from("<I", raw, 20)[0]
    start = 32+length
    fixtures = [("truncated-record", raw[:-1]),
                ("extra-tail", raw+b"\x00"),
                ("wrong-count", raw[:24]+struct.pack("<Q", 1)+raw[32:]),
                ("zero-stabilizer", raw[:start]+b"\x00"*4+raw[start+4:])]
    for name, data in fixtures:
        path = args.output / f"invalid-{name}.bin"
        path.write_bytes(data)
        try:
            list(BinaryRows(path).rows())
        except (AssertionError, ValueError):
            negatives.append(name)
        else:
            raise AssertionError(("bad binary accepted", name))
    # A valid-sized but inconsistent run must fail the complete equality audit.
    inconsistent = args.output / "invalid-run-payment.bin"
    shutil.copy2(corrupt_source, inconsistent)
    shutil.copytree(Path(str(corrupt_source)+".runs"), Path(str(inconsistent)+".runs"))
    runpath = Path(str(inconsistent)+".runs") / "run-0.bin"
    runbytes = runpath.read_bytes()
    runpath.write_bytes(runbytes[:28]+b"\x00"*4+runbytes[32:])
    try:
        verify_merge(inconsistent)
    except AssertionError:
        negatives.append("inconsistent-run-record")
    else:
        raise AssertionError("changed run accepted")
    report = {"verified": True, "stream_kernel_derivation_verified": True,
              "whole_set_controls": comparisons, "forced_cross_run_duplicates_checked": True,
              "empty_catalogue_checked": True, "negative_controls_rejected": negatives,
              "source_sha256": sha(Path(__file__)),
              "native_sources_sha256": {name: sha(ROOT / name) for name in
                  ("peel_paid_stream.cpp", "peel_paid_stream_kernel.inc", "paid_stream_storage.inc",
                   "paid_matcher.inc", "peel_paid_kernel.inc", "peel_degree.cpp")},
              "binary_sha256": sha(ROOT / "peel_paid_stream.exe"),
              "small_block_binary_sha256": sha(ROOT / "peel_paid_stream_small.exe"),
              "reader_sha256": sha(ROOT / "paid_binary_residual.py"),
              "matcher_controls_sha256": sha(ROOT / "evidence/paid-matcher-controls-resume1/VERIFIED.json"),
              "frozen_inputs_modified": False, "global_optimality_proved": False,
              "scope": "bounded-storage exact run-union equality; no new target lower bound"}
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Paid streaming controls PASS:", len(comparisons), "complete sets;",
          len(negatives), "invalid inputs; cross-run duplicates and empty set checked", flush=True)


if __name__ == "__main__":
    main()
