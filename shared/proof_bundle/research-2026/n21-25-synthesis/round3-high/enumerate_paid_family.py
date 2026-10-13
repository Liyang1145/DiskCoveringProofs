"""Content-gated bounded-memory COMPLETE residual-family search for n23..25.

Library-excluded branches plus all emitted residuals cover the necessary
family by the written peeling induction. Residuals still need lower bounds.
No completed catalogue is accepted before successful native termination and
an independent full equality audit of all sorted run inputs and output.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import subprocess
import time
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
    assert const["verified"] and const["N"] == N and [B, N-B] in const["families"]
    U = F(const["radius_upper"])
    assert U < F(1, 4) and U/(1-2*U) < F(1, 2)
    assert const["minimum_interior_cells"] == 8 and const["maximum_boundary_cells"] == N-8
    assert const["families"] == [[b, N-b] for b in
                                 range(const["minimum_boundary_cells"], const["maximum_boundary_cells"]+1)]
    import sys
    sys.path.insert(0, str(exact.kernel.ARCS))
    import exact_arcs as arcs
    bmin = const["minimum_boundary_cells"]
    assert U < F(arcs.sincos_turn(F(1, 2*(bmin-1)))[1][0], arcs.SCALE)
    D = const["angle_scale"]
    assert D == 10**7 and 0 < 2*const["angle_caps"][0] < const["angle_caps"][1] < const["angle_caps"][2] < D//2
    for k, cap in enumerate(const["angle_caps"], 1):
        assert F(arcs.sincos_turn(F(cap, 2*D))[1][0], arcs.SCALE) > k*U
    librarypath = ROOT / "evidence/n22-portable-strict-obstacles-resume1/LIBRARY.json"
    tablepath = librarypath.parent / "OBSTACLES.tsv"
    library = read(librarypath)
    assert library["verified"] and library["all_library_trees_fresh_exact_replayed"]
    assert library["no_root_or_local_theorem_used"] and U <= F(library["radius_threshold"])
    assert library["pattern_table_sha256"] == sha(tablepath)
    for relative, digest in library["files"].items():
        path = (WORK / relative).resolve()
        assert path.is_relative_to(WORK) and sha(path) == digest
    controls = ROOT / "evidence/paid-stream-storage-controls-resume2/VERIFIED.json"
    control = read(controls)
    assert control["verified"] and control["forced_cross_run_duplicates_checked"]
    assert control["source_sha256"] == sha(ROOT / "test_paid_storage.py")
    assert control["binary_sha256"] == sha(ROOT / "peel_paid_stream.exe")
    assert control["reader_sha256"] == sha(ROOT / "paid_binary_residual.py")
    for name, digest in control["native_sources_sha256"].items():
        assert sha(ROOT / name) == digest
    matching = ROOT / "evidence/paid-matcher-controls-resume1/VERIFIED.json"
    assert control["matcher_controls_sha256"] == sha(matching)
    match = read(matching)
    assert match["verified"] and match["positive_transformed_maps"] == 26013
    assert match["kernel_derivation_verified"]
    assert match["source_sha256"] == sha(ROOT / "test_paid_matcher.py")
    assert match["binary_sha256"] == sha(ROOT / "peel_paid.exe")
    regressionpath = ROOT / "evidence/paid-N19-B13-full-partition-resume1.json"
    regression = read(regressionpath)
    assert regression["verified"] and regression["all_missing_types_have_explicit_paid_injections"]
    assert regression["source_sha256"] == sha(ROOT / "audit_paid_regression.py")
    assert regression["library_sha256"] == sha(librarypath)
    assert regression["reference_sha256"] == sha(ROOT / "evidence/paid-N19-B13-reference-resume1.json")
    assert regression["residual_sha256"] == sha(ROOT / "evidence/paid-N19-B13-residual-resume1.bin")
    dependencies = {path.resolve().relative_to(WORK).as_posix(): sha(path) for path in
                    (constpath, librarypath, tablepath, controls, matching, regressionpath,
                     ROOT / "enumerate_paid_family.py", ROOT / "audit_paid_regression.py",
                     ROOT / "test_paid_storage.py", ROOT / "test_paid_matcher.py",
                     ROOT / "paid_residual.py", ROOT / "stream_catalog.py",
                     ROOT / "audit_streamed_hierarchy.py", ROOT / "exact_graph.py",
                     ROOT.parent / "round2-grouped/partial_force_exact.py",
                     ROOT / "evidence/paid-N19-B13-reference-resume1.json",
                     ROOT / "evidence/paid-N19-B13-residual-resume1.bin",
                     ROOT / "paid_binary_residual.py", ROOT / "peel_paid_stream.exe",
                     ROOT / "peel_paid_stream.cpp", ROOT / "peel_paid_stream_kernel.inc",
                     ROOT / "paid_stream_storage.inc", ROOT / "paid_matcher.inc",
                     ROOT / "peel_paid_kernel.inc", ROOT / "peel_degree.cpp",
                     ROOT / "PROOF-AWARE-PEELING.md", exact.kernel.ARCS / "exact_arcs.py")}
    dependencies.update(library["files"])
    return const, library, tablepath, dependencies


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, choices=(23, 24, 25), required=True)
    ap.add_argument("--B", type=int, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists() and not args.output.is_absolute() and args.output.as_posix().isascii()
    const, library, tablepath, dependencies = gates(args.n, args.B)
    args.output.mkdir(parents=True)
    # Save bindings before the native process, but do not publish a completion.
    inputpath = args.output / "INPUT-BINDINGS.json"
    inputpath.write_text(json.dumps({"N": args.n, "B": args.B, "files": dependencies,
                                   "library_math_files": library["files"],
                                   "residual_search_completed": False}, indent=2), encoding="utf8")
    target = args.output / f"N{args.n}-B{args.B}-paid-residual.bin"
    command = [str(ROOT / "peel_paid_stream.exe"), str(args.n), str(args.B), str(target),
               str(const["angle_scale"]), *map(str, const["angle_caps"]), "0", "dfs",
               str(tablepath.relative_to(ROOT))]
    started = time.monotonic()
    print("Paid necessary-family search started:", args.n, args.B,
          "bounded 100000-type blocks; no completed claim", flush=True)
    result = subprocess.run(command, cwd=ROOT)
    assert result.returncode == 0, "Incomplete/failed native residual search is not accepted"
    for relative, expected in dependencies.items():
        assert sha(WORK / relative) == expected, ("input changed during search", relative)
    header, runs = verify_merge(target)
    assert (header["N"], header["B"], header["mode"]) == (args.n, args.B, "dfs")
    assert header["screen"] and header["scale"] == const["angle_scale"] and header["caps"] == const["angle_caps"]
    assert header["survivor_block_size"] == 100000
    byid = {row["id"]: row for row in library["obstacles"]}
    payments = header["proof_payments"]
    for payment in payments:
        obstacle = byid[payment["obstacle"]]
        assert obstacle["B"] == args.B
        mapping = {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")}
        check_subset(args.n, args.B, obstacle, mapping, set(payment["sample_faces"]))
    report = {"verified": True, "N": args.n, "B": args.B,
              "complete_residual_family_search": True, "full_unpruned_catalogue_enumerated": False,
              "native_guard_source_argument_required_for_all_prunes": True,
              "payment_samples_independently_mapped": len(payments),
              "pruned_recursive_states_not_orbit_count": header["proof_prunes"],
              "residual_orbits": header["orbits"], "calls": header["calls"],
              "all_sorted_run_union_equality_verified": True, "run_count": len(runs),
              "run_sha256": {row.path.name: sha(row.path) for row in runs},
              "catalog_sha256": sha(target), "input_bindings_sha256": sha(inputpath),
              "source_sha256": sha(Path(__file__)), "files": dependencies,
              "seconds": time.monotonic()-started,
              "all_residual_types_lower_bounds_paid": header["orbits"] == 0,
              "actual_cover_reduction_not_formalized_here": True,
              "global_optimality_proved": False,
              "scope": "necessary family = certified-pruned branches + complete unpaid residual catalogue"}
    (args.output / "SUMMARY.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Paid necessary-family COMPLETE and independently merged:", args.n, args.B,
          header["orbits"], "residual orbits; no target-global claim", flush=True)


if __name__ == "__main__":
    main()
