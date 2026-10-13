"""Complete screened controls for B15/16/17 with sparse payments disabled."""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from paid_binary_residual import BinaryRows, verify_merge
from group_catalog import canonical
from test_outer_collar import collar_codes, run_collar
from test_sparse_collar import run_sparse, mechanical_derivation

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    mechanical_derivation()
    constants = json.loads((ROOT.parent / "evidence/core-reduction/constants/n25.json").read_text())
    base = json.loads((ROOT / "outer-collar-controls-v3-deep-internal/VERIFIED.json").read_text())
    assert base["verified"] and base["all_full_reference_outer_restrictions_present"]
    assert base["native_source_sha256"] == sha(ROOT / "peel_outer_collar.cpp")
    assert base["frozen_degree_source_sha256"] == sha(HIGH / "peel_degree.cpp")
    output.mkdir()
    cases = []
    for B in (15, 16, 17):
        for N in (B, B+1, B+2):
            fullpath = output / f"N{N}-B{B}-full-reference.bin"
            reference = subprocess.run([
                str(HIGH / "peel_outer_stream.exe"), str(N), str(B),
                os.path.relpath(fullpath, HIGH).replace("\\", "/"),
                str(constants["angle_scale"]), *map(str, constants["angle_caps"]), "0", "dfs", "-",
            ], cwd=HIGH, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
            assert reference.returncode == 0, (reference.returncode, reference.stdout, reference.stderr)
            fullheader, _ = verify_merge(fullpath)
            expected = {canonical(N, B, row["faces"], 1)[0] for _, row in BinaryRows(fullpath).rows()}
            baseline = output / f"N{N}-B{B}-collar-baseline.json"
            result = run_collar(N, B, baseline, "dfs", caps=constants["angle_caps"])
            assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
            _, basecodes = collar_codes(baseline, N, B)
            assert expected <= basecodes
            for mode in ("dfs", "audit"):
                target = output / f"N{N}-B{B}-no-sparse-{mode}.json"
                result = run_sparse(N, B, target, "-", mode=mode)
                assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
                header, actual = collar_codes(target, N, B)
                assert actual == basecodes
                assert header["sparse_patterns_loaded"] == header["paid_patterns_loaded"] == 0
                cases.append({
                    "N": N, "B": B, "mode": mode, "full_reference_graphs": fullheader["orbits"],
                    "full_reference_outer_graphs": len(expected), "collar_graphs": len(actual),
                    "full_reference_outer_restrictions_present": True,
                    "same_complete_collar_set_with_guards_disabled": True,
                    "full_reference_sha256": sha(fullpath), "collar_sha256": sha(target),
                })
        print("New family complete controls PASS: B", B, flush=True)
    negatives = []
    for label, N, B, limit in (("node-limit", 25, 15, 1), ("bad-N", 26, 16, 0), ("bad-B", 14, 17, 0)):
        target = output / (label+".json")
        result = run_sparse(N, B, target, "-", limit=limit)
        assert result.returncode != 0 and not target.exists()
        negatives.append(label)
    (output / "VERIFIED.json").write_text(json.dumps({
        "verified": True, "schema": "n25-family-no-payment-collar-controls-v1",
        "source_sha256": sha(Path(__file__)), "native_source_sha256": sha(ROOT / "peel_sparse_outer_collar.cpp"),
        "native_binary_sha256": sha(ROOT / "peel_sparse_outer_collar-linux"),
        "frozen_degree_source_sha256": sha(HIGH / "peel_degree.cpp"),
        "full_reference_binary_sha256": sha(HIGH / "peel_outer_stream.exe"),
        "base_controls_sha256": sha(ROOT / "outer-collar-controls-v3-deep-internal/VERIFIED.json"),
        "mechanical_source_derivation_sha256": sha(ROOT / "sparse-collar-source-derivation.json"),
        "cases": cases, "negative_controls_rejected": negatives,
        "all_complete_reference_outer_restrictions_present": True,
        "guards_disabled_complete_collar_sets_equal": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
