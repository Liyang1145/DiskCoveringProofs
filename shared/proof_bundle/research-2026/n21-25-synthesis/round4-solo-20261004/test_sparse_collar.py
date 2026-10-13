"""Gate the new sparse guard using complete small B14 necessary searches."""
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
from group_catalog import validate
from test_outer_collar import linux_path, WSL, run_collar, collar_codes, source_derivation
from test_sparse_outer_match import independent_injection

assert __debug__


def run_sparse(n, b, output, sparse, *, limit=0, mode="dfs", exact_table="-"):
    output = os.path.relpath(Path(output).resolve(), ROOT).replace("\\", "/")
    if sparse != "-":
        sparse = os.path.relpath(Path(sparse).resolve(), ROOT).replace("\\", "/")
    if exact_table != "-":
        exact_table = os.path.relpath(Path(exact_table).resolve(), ROOT).replace("\\", "/")
    assert all(p.isascii() for p in (output, sparse, exact_table))
    const = json.loads((ROOT.parent / "evidence/core-reduction/constants/n25.json").read_text())
    return subprocess.run(
        [WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
         "./peel_sparse_outer_collar-linux", str(n), str(b), output,
         str(const["angle_scale"]), *map(str, const["angle_caps"]), str(limit), mode, exact_table, sparse],
        capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)


def mechanical_derivation():
    source_derivation()
    report = json.loads((ROOT / "sparse-collar-source-derivation.json").read_text())
    assert report["base_source_sha256"] == sha(ROOT / "peel_outer_collar.cpp")
    assert report["derived_source_sha256"] == sha(ROOT / "peel_sparse_outer_collar.cpp")
    assert report["generator_sha256"] == sha(ROOT / "derive_sparse_collar.py")
    text = (ROOT / "peel_outer_collar.cpp").read_text(encoding="utf8")
    for old, new in report["changes"]:
        assert text.count(old) == 1
        text = text.replace(old, new, 1)
    assert text == (ROOT / "peel_sparse_outer_collar.cpp").read_text(encoding="utf8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    mechanical_derivation()
    library = json.loads(args.library.read_text())
    assert library["verified"] and library["schema"] == "strict-sparse-outer-obstacle-library-v1"
    table = args.library.parent / "OBSTACLES.tsv"
    assert library["pattern_table_sha256"] == sha(table)
    maps = json.loads((ROOT / "n25-B14-sparse-match-controls-v1/VERIFIED.json").read_text())
    assert maps["verified"] and maps["library_sha256"] == sha(args.library)
    assert maps["matcher_include_sha256"] == sha(ROOT / "sparse_outer_matcher.inc")
    assert maps["source_sha256"] == sha(ROOT / "test_sparse_outer_match.py")
    args.output.mkdir(parents=True)
    const = json.loads((ROOT.parent / "evidence/core-reduction/constants/n25.json").read_text())
    cases = []
    byid = {o["id"]: o for o in library["obstacles"]}
    for n in (17, 18, 19, 20, 21):
        baseline = args.output / f"N{n}-B14-baseline.json"
        result = run_collar(n, 14, baseline, "dfs", caps=const["angle_caps"])
        assert result.returncode == 0, result.stderr
        original, allcodes = collar_codes(baseline, n, 14)
        for mode in ("dfs", "audit"):
            target = args.output / f"N{n}-B14-sparse-{mode}.json"
            result = run_sparse(n, 14, target, table, mode=mode)
            assert result.returncode == 0, result.stderr
            (args.output / f"N{n}-B14-sparse-{mode}.stderr").write_bytes(result.stderr)
            header, residual = collar_codes(target, n, 14)
            assert residual <= allcodes, "sparse guard cannot add necessary weak graphs"
            removed = allcodes-residual
            independent_paid = 0
            for code in removed:
                assert any(independent_injection(o, n, code) for o in library["obstacles"])
                independent_paid += 1
            for payment in header["sparse_payments"]:
                pattern = byid[payment["obstacle"]]
                mapping = {k: payment[k] for k in ("centers", "anchors", "orientation", "shift")}
                validate(n, 14, pattern["faces"], mapping, payment["sample_faces"])
            cases.append({
                "N": n, "B": 14, "mode": mode, "necessary_baseline_weak_graphs": len(allcodes),
                "residual_weak_graphs": len(residual), "all_removed_weak_graphs_independently_paid": True,
                "independent_removed_maps": independent_paid, "sparse_recursive_prunes_not_type_count": header["sparse_proof_prunes"],
                "explicit_payment_samples": len(header["sparse_payments"]),
                "baseline_sha256": sha(baseline), "residual_sha256": sha(target),
            })
        print("Sparse complete collar partition PASS:", n, 14, len(allcodes), "baseline graphs", flush=True)
    # No-pruning derivation regression and fail-closed publication.
    target = args.output / "N20-B14-no-sparse.json"
    result = run_sparse(20, 14, target, "-")
    assert result.returncode == 0, result.stderr
    _, actual = collar_codes(target, 20, 14)
    _, expected = collar_codes(args.output / "N20-B14-baseline.json", 20, 14)
    assert actual == expected
    negatives = []
    for label, n, b, limit in (("node-limit", 25, 14, 1), ("bad-N", 26, 14, 0), ("bad-B", 14, 15, 0)):
        target = args.output / (label + ".json")
        result = run_sparse(n, b, target, table, limit=limit)
        assert result.returncode != 0 and not target.exists()
        negatives.append(label)
    report = {
        "verified": True, "source_sha256": sha(Path(__file__)),
        "native_source_sha256": sha(ROOT / "peel_sparse_outer_collar.cpp"),
        "native_binary_sha256": sha(ROOT / "peel_sparse_outer_collar-linux"),
        "base_collar_source_sha256": sha(ROOT / "peel_outer_collar.cpp"),
        "source_derivation_sha256": sha(ROOT / "sparse-collar-source-derivation.json"),
        "sparse_guard_sha256": sha(ROOT / "sparse_outer_matcher.inc"),
        "library_sha256": sha(args.library), "proper_matching_controls_sha256": sha(ROOT / "n25-B14-sparse-match-controls-v1/VERIFIED.json"),
        "all_baseline_minus_residual_graphs_independently_paid": True, "cases": cases,
        "no_sparse_guard_full_set_equal": True, "negative_controls_rejected": negatives,
        "native_platform": "WSL Ubuntu2204 static g++11.4; separate from frozen Windows kernel",
        "full_n25_production_search_not_done_here": True, "global_optimality_proved": False,
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Sparse production guard controls PASS:", len(cases), "complete partitions;",
          len(negatives), "fail-closed controls", flush=True)


if __name__ == "__main__":
    main()
