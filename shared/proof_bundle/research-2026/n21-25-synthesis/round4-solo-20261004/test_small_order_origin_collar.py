"""Complete small-reference containment and actual small-order origin/angle controls."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import os
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from paid_binary_residual import BinaryRows, verify_merge
from group_catalog import canonical
from n25_outer_search import read, publish
from test_outer_collar import linux_path, WSL
from small_order_origin_caps import parameters
from small_order_cover_origin import classify
from merge_small_order_origin_chunks import merge, gate

assert __debug__


def derivation():
    old = (ROOT / "peel_origin_streamed_collar.cpp").read_text(encoding="utf8")
    changes = [
        ('#include "collar_chunk_storage.inc"', '#include "small_order_collar_chunk_storage.inc"'),
        ('#include "cover_origin_obstruction.inc"', '#include "small_order_cover_origin.inc"'),
        ("complete-cover-origin-collar-sorted-chunks-v1", "complete-small-order-origin-collar-sorted-chunks-v1"),
        ("#define main frozen_degree_main",
         '#pragma push_macro("main")\n#undef main\n#define main frozen_degree_main'),
        ("#undef main\n#undef possible", '#undef main\n#pragma pop_macro("main")\n#undef possible'),
    ]
    for before, after in changes:
        assert old.count(before) == 1
        old = old.replace(before, after)
    assert old == (ROOT / "peel_small_order_origin_collar.cpp").read_text(encoding="utf8")
    storage = (ROOT / "collar_chunk_storage.inc").read_text(encoding="utf8")
    storage = storage.replace(
        "// Sorted slabs are storage only. No stored-code membership affects recursion.",
        "// Same storage-only sorted slabs; a smaller independent C-drive safety guard.", 1)
    storage = storage.replace("20ULL*1024*1024*1024", "4ULL*1024*1024*1024", 1)
    assert storage == (ROOT / "small_order_collar_chunk_storage.inc").read_text(encoding="utf8")
    return changes


def native(binary, arguments):
    return subprocess.run(
        [WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env",
         "-C", linux_path(ROOT), "./"+binary, *map(str, arguments)],
        capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)


def relative(path):
    result = os.path.relpath(Path(path).resolve(), ROOT).replace("\\", "/")
    assert result.isascii()
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--caps", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    cappath, output = args.caps.resolve(), args.output.resolve()
    assert cappath.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    capreport = read(cappath)
    assert capreport["verified"] and capreport["source_sha256"] == sha(ROOT / "small_order_origin_caps.py")
    changes = derivation()
    output.mkdir()
    cases, rejected, nativechecks = [], [], []
    fixturecaps = (2000000, 4200000, 4800000)
    for N, B in ((3, 3), (5, 3), (6, 4), (7, 4), (8, 5)):
        reference = output / f"N{N}-B{B}-FULL.bin"
        result = subprocess.run([
            str(HIGH / "peel_outer_stream.exe"), str(N), str(B), relative(reference),
            "10000000", *map(str, fixturecaps), "0", "noscreen", "-"],
            cwd=ROOT, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        assert result.returncode == 0
        head, _ = verify_merge(reference)
        expected = {canonical(N, B, row["faces"], 1)[0] for _, row in BinaryRows(reference).rows()}
        for mode in ("noscreen", "audit-noscreen"):
            directory = output / f"N{N}-B{B}-{mode}"
            directory.mkdir()
            manifestpath = directory / "MANIFEST.json"
            result = native("peel_small_order_origin_collar-linux", [
                N, B, relative(manifestpath), "10000000", *fixturecaps,
                0, mode, "-", "-", 4900000, 7, 0])
            publish(directory / "TERMINAL.json", {
                "actual_exit_code": result.returncode, "native_terminal_observed": True,
                "stdout": result.stdout.decode("utf8", errors="replace"),
                "stderr": result.stderr.decode("utf8", errors="replace"),
                "manifest_sha256": sha(manifestpath) if manifestpath.exists() else None,
            })
            assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
            union = merge(manifestpath, result.returncode, directory / "UNION")
            actual = set()
            with (directory / "UNION/CATALOG.jsonl").open(encoding="ascii") as stream:
                next(stream)
                for line in stream:
                    actual.add(tuple(json.loads(line)["faces"]))
            assert expected <= actual
            cases.append({
                "N": N, "B": B, "mode": mode, "complete_full_reference_types": head["orbits"],
                "all_full_reference_outer_restrictions_present": True,
                "necessary_weak_graphs": len(actual), "allowed_extra_weak_graphs": len(actual-expected),
                "manifest_sha256": sha(manifestpath), "union_sha256": sha(directory / "UNION/VERIFIED.json"),
            })
        print("Small-order new source complete reference containment passed:", N, B, flush=True)
    rng = random.Random(23241006)
    for N in (23, 24):
        constants, cap8, bound = parameters(N)
        assert bound == next(row for row in capreport["orders"] if row["N"] == N)
        corepath = ROOT / f"n23-n24-archive-core-inputs-20261005-v1/n{N}/core-system.json"
        core = read(corepath)
        B = core["B"]
        truefaces = sorted(sum(1 << v for v in face) for face in core["all_faces"])
        fixtures = [("actual-attaining-full-graph", truefaces)]
        fixtures.append(("every-label-exposed-functional-obstruction",
                         sorted((1 << 0)|(1 << 1)|(1 << v) for v in range(2, N))))
        for j in range(30):
            values = set()
            for _ in range(rng.randint(1, 10)):
                values.add(sum(1 << v for v in rng.sample(range(N), 3)))
            fixtures.append((f"random-functional-{j}", sorted(values)))
        for ordinal, (label, faces) in enumerate(fixtures):
            seed = output / f"N{N}-seed-{ordinal}.txt"
            with seed.open("x", encoding="ascii") as stream:
                stream.write(f"{N} {B} {len(faces)}\n")
                stream.write(" ".join(map(str, faces))+"\n")
                stream.write(" ".join(map(str, constants["angle_caps"]))+"\n")
            result = native("test_small_order_origin_native-linux", [relative(seed), 1, cap8])
            publish(output / f"N{N}-seed-{ordinal}-TERMINAL.json", {
                "actual_exit_code": result.returncode,
                "stdout": result.stdout.decode("utf8", errors="replace"),
                "stderr": result.stderr.decode("utf8", errors="replace"),
            })
            assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
            expected = classify(N, B, faces, constants["radius_upper"])["actual_cover_obstruction"]
            tokens = result.stdout.decode("ascii").split()
            assert tokens[:2] == ["ORIGIN", str(int(expected))]
            if ordinal == 0:
                assert not expected and tokens == ["ORIGIN", "0", "ANGLE", "1"]
            nativechecks.append({"N": N, "label": label, "origin_obstruction": expected,
                                 "true_attaining_origin_and_angles_retained": ordinal == 0})
        # Disabled origin guard must not geometrically exclude the all-exposed fixture.
        seed = output / f"N{N}-seed-1.txt"
        result = native("test_small_order_origin_native-linux", [relative(seed), 0, cap8])
        assert result.returncode == 0 and result.stdout.decode("ascii").split()[:2] == ["ORIGIN", "0"]
    for label, N, B, limit, flag, cap8 in (
        ("node-budget-not-complete", 8, 5, 1, 0, 4900000),
        ("unsupported-N25-origin", 25, 16, 1, 1, 4900000),
        ("unsupported-N22-origin", 22, 15, 1, 1, 4900000),
        ("wrong-origin-flag", 24, 16, 1, 2, 4900000),
        ("bad-N", 26, 16, 1, 1, 4900000),
        ("bad-B", 24, 25, 1, 1, 4900000),
        ("quarter-turn-cap8", 24, 16, 1, 1, 5000000),
    ):
        manifestpath = output / (label+".json")
        result = native("peel_small_order_origin_collar-linux", [
            N, B, relative(manifestpath), "10000000", *fixturecaps,
            limit, "noscreen", "-", "-", cap8, 7, flag])
        assert result.returncode != 0 and not manifestpath.exists()
        rejected.append(label)
    # Mutate an actual complete small manifest, not invented schema flags.
    valid = read(output / "N8-B5-noscreen/MANIFEST.json")
    for label, key, value in (
        ("wrong-native-scope-schema", "schema", "complete-cover-origin-collar-sorted-chunks-v1"),
        ("completed-full-types-claim", "complete_full_triangulations", True),
        ("wrong-storage-space-guard", "disk_guard_bytes", 20*1024**3),
        ("unsupported-origin-domain", "origin_cover_orders", [25]),
        ("unbound-force-prunes", "proof_prunes", 1),
    ):
        changed = deepcopy(valid)
        changed[key] = value
        try:
            gate(changed)
        except (AssertionError, ValueError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("invalid small-order manifest gate accepted", label))
    files = {}
    for path in (Path(__file__), cappath, ROOT / "peel_small_order_origin_collar.cpp",
                 ROOT / "peel_small_order_origin_collar-linux", ROOT / "small_order_cover_origin.inc",
                 ROOT / "small_order_collar_chunk_storage.inc", ROOT / "merge_small_order_origin_chunks.py",
                 ROOT / "test_small_order_origin_native.cpp", ROOT / "test_small_order_origin_native-linux",
                 ROOT / "peel_origin_streamed_collar.cpp", ROOT / "collar_chunk_storage.inc",
                 ROOT / "eight_rod_possible.inc", ROOT / "eight_rod_angles.py",
                 ROOT / "N23-N24-UNEXPOSED-ORIGIN-SOURCE.md", HIGH / "peel_degree.cpp",
                 HIGH / "paid_outer_matcher.inc", ROOT / "sparse_outer_matcher.inc"):
        files[str(path)] = sha(path)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "small-order-origin-collar-complete-source-controls-v1",
        "only_include_schema_and_test_main_macro_isolation_changes": changes,
        "all_original_recursive_and_canonical_branches_literally_unchanged": True,
        "storage_only_difference_is_smaller_4GiB_guard": True,
        "complete_reference_containment_cases": cases,
        "actual_attaining_and_functional_native_origin_angle_checks": nativechecks,
        "both_N23_N24_true_attaining_graphs_retained_by_origin_and_own_angles": True,
        "negative_controls_rejected": rejected, "frozen_files": files,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("Small-order source/native/reference/attainer controls passed:", len(cases),
          len(nativechecks), len(rejected), flush=True)


if __name__ == "__main__":
    main()
