"""Exact input-gated native outer-obstacle residual search, n23..25 B13."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import subprocess
import time
import sys
import exact_graph as exact
from paid_binary_residual import verify_merge
from audit_paid_regression import check_subset
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2].resolve()
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def gates(N, B):
    constpath = ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"
    const = read(constpath)
    assert B == 13 and N in (23, 24)
    assert const["verified"] and const["N"] == N and [B, N-B] in const["families"]
    U = F(const["radius_upper"])
    assert U < F(1, 4) and U/(1-2*U) < F(1, 2)
    assert const["minimum_interior_cells"] == 8 and const["maximum_boundary_cells"] == N-8
    sys.path.insert(0, str(exact.kernel.ARCS))
    import exact_arcs as arcs
    bmin = const["minimum_boundary_cells"]
    assert U < F(arcs.sincos_turn(F(1, 2*(bmin-1)))[1][0], arcs.SCALE)
    D = const["angle_scale"]
    assert D == 10**7
    for k, cap in enumerate(const["angle_caps"], 1):
        assert F(arcs.sincos_turn(F(cap, 2*D))[1][0], arcs.SCALE) > k*U
    librarypath = ROOT / "evidence/n23-portable-outer-obstacles-resume1/LIBRARY.json"
    tablepath = librarypath.parent / "OBSTACLES.tsv"
    library = read(librarypath)
    assert library["verified"] and library["all_library_trees_fresh_exact_replayed"]
    assert library["source_N"] == 23 and library["threshold"] == 1
    assert U <= F(library["radius_threshold"]) and library["no_root_or_local_theorem_used"]
    assert sha(tablepath) == library["pattern_table_sha256"]
    for relative, expected in library["files"].items():
        assert sha(WORK / relative) == expected
    controlpath = ROOT / "evidence/outer-paid-controls-resume1/VERIFIED.json"
    controls = read(controlpath)
    assert controls["verified"] and controls["outer_kernel_threshold_derivation_verified"]
    assert controls["positive_transformed_maps"] == 285
    assert controls["nontrivial_all_missing_types_paid"]
    assert controls["library_sha256"] == sha(librarypath)
    assert controls["table_sha256"] == sha(tablepath)
    assert controls["source_sha256"] == sha(ROOT / "test_outer_paid.py")
    assert controls["binary_sha256"] == sha(ROOT / "peel_outer_stream.exe")
    assert controls["matcher_binary_sha256"] == sha(ROOT / "peel_outer_match.exe")
    assert controls["reader_sha256"] == sha(ROOT / "paid_binary_residual.py")
    for name, expected in controls["native_sources_sha256"].items():
        assert sha(ROOT / name) == expected
    storagepath = ROOT / "evidence/paid-stream-storage-controls-resume2/VERIFIED.json"
    assert controls["original_storage_controls_sha256"] == sha(storagepath)
    storage = read(storagepath)
    assert storage["verified"] and storage["forced_cross_run_duplicates_checked"]
    for name, expected in storage["native_sources_sha256"].items():
        assert sha(ROOT / name) == expected
    dependencies = {p.resolve().relative_to(WORK).as_posix(): sha(p) for p in (
        Path(__file__), constpath, librarypath, tablepath, controlpath, storagepath,
        ROOT / "test_outer_paid.py", ROOT / "test_paid_storage.py", ROOT / "test_paid_matcher.py",
        ROOT / "peel_outer_stream.cpp", ROOT / "peel_outer_stream.exe", ROOT / "peel_outer_match.exe",
        ROOT / "peel_outer_match.cpp", ROOT / "peel_outer_stream_kernel.inc",
        ROOT / "paid_outer_matcher.inc", ROOT / "paid_stream_storage.inc",
        ROOT / "paid_binary_residual.py", ROOT / "audit_paid_regression.py",
        ROOT / "peel_paid_stream_kernel.inc", ROOT / "paid_matcher.inc", ROOT / "peel_paid_kernel.inc",
        ROOT / "peel_degree.cpp", ROOT / "stream_catalog.py", ROOT / "exact_graph.py",
        ROOT.parent / "round2-grouped/partial_force_exact.py", exact.kernel.ARCS / "exact_arcs.py",
        ROOT / "PROOF-AWARE-OUTER-PEELING.md",
    )}
    dependencies.update(library["files"])
    return const, library, tablepath, dependencies


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, choices=(23, 24), required=True)
    ap.add_argument("--B", type=int, choices=(13,), required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists() and not args.output.is_absolute() and args.output.as_posix().isascii()
    const, library, tablepath, dependencies = gates(args.n, args.B)
    args.output.mkdir(parents=True)
    inputpath = args.output / "INPUT-BINDINGS.json"
    inputpath.write_text(json.dumps({"N": args.n, "B": args.B, "files": dependencies,
                                   "residual_search_completed": False}, indent=2), encoding="utf8")
    target = args.output / f"N{args.n}-B{args.B}-outer-paid-residual.bin"
    command = [str(ROOT / "peel_outer_stream.exe"), str(args.n), str(args.B), str(target),
               str(const["angle_scale"]), *map(str, const["angle_caps"]), "0", "dfs",
               str(tablepath.relative_to(ROOT))]
    started = time.monotonic()
    print("Outer-paid necessary-family search started:", args.n, args.B,
          "all residuals retained; no completion claim", flush=True)
    result = subprocess.run(command, cwd=ROOT)
    assert result.returncode == 0, "Failed/incomplete outer residual search"
    for relative, expected in dependencies.items():
        assert sha(WORK / relative) == expected
    header, runs = verify_merge(target)
    assert (header["N"], header["B"], header["mode"]) == (args.n, args.B, "dfs")
    assert header["screen"] and header["scale"] == const["angle_scale"] and header["caps"] == const["angle_caps"]
    assert header["survivor_block_size"] == 100000
    byid = {row["id"]: row for row in library["obstacles"]}
    for payment in header["proof_payments"]:
        obstacle = byid[payment["obstacle"]]
        assert obstacle["B"] == args.B
        mapping = {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")}
        check_subset(args.n, args.B, obstacle, mapping, set(payment["sample_faces"]))
    report = {"verified": True, "N": args.n, "B": args.B,
              "complete_residual_family_search": True,
              "full_unpruned_catalogue_enumerated": False, "residual_orbits": header["orbits"],
              "pruned_recursive_states_not_orbit_count": header["proof_prunes"],
              "native_guard_source_argument_required_for_all_prunes": True,
              "payment_samples_independently_mapped": len(header["proof_payments"]),
              "all_sorted_run_union_equality_verified": True, "calls": header["calls"],
              "run_count": len(runs), "run_sha256": {r.path.name: sha(r.path) for r in runs},
              "catalog_sha256": sha(target), "input_bindings_sha256": sha(inputpath),
              "files": dependencies, "source_sha256": sha(Path(__file__)),
              "seconds": time.monotonic()-started,
              "all_residual_types_lower_bounds_paid": header["orbits"] == 0,
              "global_optimality_proved": False,
              "scope": "B13 necessary family paid branches plus complete unpaid residual catalogue"}
    (args.output / "SUMMARY.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Outer-paid family COMPLETE:", args.n, args.B, header["orbits"],
          "residual orbits; full target proof remains separate", flush=True)


if __name__ == "__main__":
    main()
