"""Actual-cover origin guard: independent masks, complete regression and seeds."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import os
import random
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import canonical
from n25_outer_search import read, publish, bind, unchanged
from refine_collar_origin import exposed_mask, controls
from test_streamed_collar import derivation_gate as storage_derivation, codes_from_union
from test_outer_collar import linux_path, WSL, collar_codes
from complete_simple_collar import simple_holes, budgets
from merge_origin_collar_chunks import merge

assert __debug__


def derivation_gate():
    storage_derivation()
    for reportname, original, derived, generator in (
        ("origin-streamed-collar-source-derivation.json", "peel_streamed_collar.cpp",
         "peel_origin_streamed_collar.cpp", "derive_origin_streamed_collar.py"),
        ("origin-chunk-merge-source-derivation.json", "merge_collar_chunks.py",
         "merge_origin_collar_chunks.py", "derive_origin_chunk_merge.py"),
    ):
        report = read(ROOT / reportname)
        assert report["verified_mechanical_derivation"]
        assert report["original_source_sha256"] == sha(ROOT / original)
        assert report["derived_source_sha256"] == sha(ROOT / derived)
        assert report["source_sha256"] == sha(ROOT / generator)
        text = (ROOT / original).read_text(encoding="utf8")
        for before, after in report["changes"]:
            assert text.count(before) == 1
            text = text.replace(before, after)
        assert text == (ROOT / derived).read_text(encoding="utf8")
    report = read(ROOT / "origin-streamed-collar-source-derivation.json")
    assert report["origin_guard_sha256"] == sha(ROOT / "cover_origin_obstruction.inc")
    probe = read(ROOT / "origin-probe-source-derivation.json")
    assert probe["only_main_name_changed"]
    assert probe["original_source_sha256"] == sha(ROOT / "peel_origin_streamed_collar.cpp")
    assert probe["derived_source_sha256"] == sha(ROOT / "origin_collar_probe_body.inc")
    assert probe["source_sha256"] == sha(ROOT / "derive_origin_probe.py")
    assert (ROOT / "peel_origin_streamed_collar.cpp").read_text(encoding="utf8").replace(
        probe["before"], probe["after"]) == (ROOT / "origin_collar_probe_body.inc").read_text(encoding="utf8")


def native(binary, args):
    return subprocess.run([WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env",
                           "-C", linux_path(ROOT), "./"+binary, *map(str, args)],
                          capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)


def relative(path):
    return os.path.relpath(path.resolve(), ROOT).replace("\\", "/")


def run_enum(N, B, path, flag, slab=7, mode="dfs", table="-", limit=0):
    c = read(HIGH.parent / "evidence/core-reduction/constants/n25.json")
    result = native("peel_origin_streamed_collar-linux", [
        N, B, relative(path), c["angle_scale"], *c["angle_caps"], limit, mode, "-",
        "-" if table == "-" else relative(table), "4058615", slab, flag])
    return result


def terminal(result, path, directory):
    publish(directory / "NATIVE-TERMINAL.json", {
        "native_terminal_observed": True, "actual_exit_code": result.returncode,
        "stdout": result.stdout.decode("utf8", errors="replace"),
        "stderr": result.stderr.decode("utf8", errors="replace"),
        "manifest_sha256": sha(path) if path.exists() else None,
    })


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    derivation_gate()
    constants = read(HIGH.parent / "evidence/core-reduction/constants/n25.json")
    from fractions import Fraction
    mathematical = controls(Fraction(constants["radius_upper"]))
    output.mkdir()
    files = {}
    # The full known attaining graph contains pure inner faces. Exposure must
    # ignore them, and every boundary dihedral/interior relabel must survive.
    geometrypath = HIGH.parent / "evidence/n25-algebraic-upper-round2/geometry.json"
    geometry = read(geometrypath)
    full = sorted(sum(1 << v for v in face) for face in geometry["faces"])
    rng = random.Random(251005)
    requests = []
    for sign in (1, -1):
        for shift in range(16):
            inner = list(range(16, 25));rng.shuffle(inner)
            labeling = [(shift+sign*v) % 16 for v in range(16)]+inner
            image = sorted(sum(1 << labeling[v] for v in range(25) if mask >> v & 1) for mask in full)
            requests.append({"N": 25, "B": 16, "flag": "1", "faces": image, "known": True})
    residual = ROOT / "n25-B14-complete-old-collar-paid-partition-20261005-v2/RESIDUAL.jsonl"
    origin = ROOT / "n25-B14-complete-origin-refined-residual-20261005-v1/VERIFIED.json"
    origin_report = read(origin)
    assert origin_report["verified"] and origin_report["parent_residual_sha256"] == sha(residual)
    with residual.open(encoding="ascii") as stream:
        next(stream)
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            if len(requests) >= 432:
                break
            requests.append({"N": 25, "B": 14, "flag": "1", "faces": row["faces"], "known": False})
            requests.append({"N": 25, "B": 14, "flag": "0", "faces": row["faces"], "known": False})
    for N in (21, 24, 25):
        for B in (14, 15, 16, 17):
            for trial in range(12):
                # Include arbitrary full and partial graphs, not only collars.
                faces = sorted({sum(1 << v for v in rng.sample(range(N), 3)) for j in range(30)})
                requests.append({"N": N, "B": B, "flag": "1", "faces": faces, "known": False})
    requestpath, answerpath = output / "REQUESTS.tsv", output / "NATIVE-ANSWERS.json"
    with requestpath.open("x", encoding="ascii") as stream:
        for index, row in enumerate(requests):
            stream.write("\t".join(map(str, [index, row["N"], row["B"], row["flag"],
                                           len(row["faces"]), *row["faces"]]))+"\n")
    result = native("test_cover_origin-linux", [relative(requestpath), relative(answerpath)])
    publish(output / "GRAPH-TERMINAL.json", {
        "actual_exit_code": result.returncode, "stdout": result.stdout.decode(errors="replace"),
        "stderr": result.stderr.decode(errors="replace"),
    })
    assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
    answers = read(answerpath)
    assert answers["scope"] == "per-graph actual-cover origin necessity only"
    assert len(answers["answers"]) == len(requests)
    obstructions = 0
    for index, (row, answer) in enumerate(zip(requests, answers["answers"], strict=True)):
        mask = exposed_mask(row["N"], row["B"], row["faces"])
        expected = row["N"] == 25 and row["flag"] == "1" and mask == (1 << 25)-1
        assert answer == {"request": index, "exposed_mask": mask, "cover_obstruction": int(expected),
                          "prune_count": int(expected), "samples": int(expected)}
        if row["known"]:
            assert not expected
        obstructions += expected
    assert obstructions > 0
    cases = []
    base = ROOT / "n25-B14-eight-sparse-guard-controls-20261005-v1"
    reference_report = read(base / "VERIFIED.json")
    for N, mode, sparse in ((20, "dfs", False), (21, "dfs", False),
                           (21, "audit", False), (21, "dfs", True)):
        reference = base / (f"N{N}-B14-eight-"+("sparse-dfs.json" if sparse else "baseline.json"))
        declared = next(r for r in reference_report["cases"] if r["N"] == N and r["mode"] == "dfs")
        assert sha(reference) == declared["residual_sha256" if sparse else "baseline_sha256"]
        _, expected = collar_codes(reference, N, 14)
        for flag in ("0", "1"):
            directory = output / f"N{N}-{mode}-sparse{int(sparse)}-origin{flag}"
            directory.mkdir()
            target = directory / "MANIFEST.json"
            table = ROOT / "n25-B14-union-sparse-library-20261005-v1/OBSTACLES.tsv" if sparse else "-"
            result = run_enum(N, 14, target, flag, slab=2, mode=mode, table=table)
            terminal(result, target, directory)
            assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
            merged = merge(target, 0, directory / "UNION")
            _, actual = codes_from_union(directory / "UNION/CATALOG.jsonl")
            assert actual == expected
            assert read(target)["origin_cover_prunes_not_type_count"] == 0
            cases.append({"N": N, "B": 14, "mode": mode, "sparse": sparse, "flag": flag,
                          "full_boundary_family_control": True, "complete_set_equals_reference": True,
                          "weak_graphs": len(actual), "manifest_sha256": sha(target),
                          "union_sha256": sha(directory / "UNION/VERIFIED.json")})
            bind(files, reference)
    # Exhaust restricted N25 controls with all hole allocations. They check
    # preservation/payment on true N25 states; they are NOT full N25 families.
    seeds = [
        ROOT / "n25-B14-complete-g0-simple-hole-completions-20261005-v1/INPUT-COLLAR.json",
        ROOT / "n25-B14-real-residual20-collar-payments-20261005-v1/parent-0000552/COMPLETIONS/INPUT-COLLAR.json",
    ]
    candidate_raw = [mask for mask in full if mask & ((1 << 16)-1)]
    candidate_code, mapping = canonical(25, 16, candidate_raw, 1)
    candidate = output / "CANDIDATE-COLLAR.json"
    publish(candidate, {"N": 25, "B": 16, "centers": len(mapping["centers"]), "faces": list(candidate_code)})
    seeds.append(candidate)
    seed_cases = []
    for index, seedpath in enumerate(seeds):
        seed = read(seedpath)
        B, centers, outer = seed["B"], seed["centers"], seed["faces"]
        holes = simple_holes(centers, B, outer)
        allocations = list(budgets(25-centers, len(holes)))
        expected_outer = canonical(centers, B, outer, 1)[0]
        for allocation_index, allocation in enumerate(allocations):
            for flag in ("0", "1"):
                directory = output / f"N25-seed{index}-allocation{allocation_index}-origin{flag}"
                directory.mkdir()
                inputpath = directory / "INPUT.tsv"
                tokens = [25, B, centers, len(outer), *outer, len(holes)]
                for cycle, inside in zip(holes, allocation, strict=True):
                    tokens.extend([len(cycle), inside, *cycle])
                inputpath.write_text("\t".join(map(str, tokens))+"\n", encoding="ascii")
                target = directory / "MANIFEST.json"
                result = native("seed_cover_origin-linux", [relative(inputpath), relative(target), flag, 1])
                terminal(result, target, directory)
                assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
                manifest = read(target)
                assert manifest["seeded_fixed_collar_restriction"] and manifest["not_a_complete_boundary_family"]
                merged = merge(target, 0, directory / "UNION")
                _, actual = codes_from_union(directory / "UNION/CATALOG.jsonl")
                expected = set() if centers == 25 and flag == "1" else {expected_outer}
                assert actual == expected
                seed_cases.append({"B": B, "centers": centers, "seed": index, "allocation": allocation,
                                   "flag": flag, "complete_restricted_result_paid_or_preserved": True,
                                   "not_a_full_boundary_family": True,
                                   "manifest_sha256": sha(target), "union_sha256": sha(directory / "UNION/VERIFIED.json")})
        bind(files, seedpath)
    # A full N25/B25 root family is removed exactly by the origin obstruction.
    directory = output / "N25-B25-complete-origin"
    directory.mkdir()
    target = directory / "MANIFEST.json"
    result = run_enum(25, 25, target, "1", slab=1)
    terminal(result, target, directory)
    assert result.returncode == 0
    merged = merge(target, 0, directory / "UNION")
    assert merged["unique_necessary_weak_graphs"] == 0
    full_N25 = {"N": 25, "B": 25, "not_a_required_N25_competitor_family": True,
                "complete_empty_by_origin_obstruction": True, "manifest_sha256": sha(target)}
    negatives = []
    for label, N, B, flag, limit in (("bad-flag", 25, 16, "2", 0),
                                     ("node-limit", 25, 16, "1", 1),
                                     ("bad-N", 26, 16, "1", 0),
                                     ("bad-B", 24, 25, "1", 0)):
        directory = output / label;directory.mkdir()
        target = directory / "MANIFEST.json"
        result = run_enum(N, B, target, flag, limit=limit)
        terminal(result, target, directory)
        assert result.returncode != 0 and not target.exists()
        negatives.append(label)
    try:
        merge(output / "N25-B25-complete-origin/MANIFEST.json", 1, output / "illegal-union")
    except AssertionError:
        negatives.append("nonzero-exit")
    else:
        raise AssertionError("accepted nonzero search")
    bad = read(output / "N25-B25-complete-origin/MANIFEST.json")
    bad["complete_necessary_outer_search"] = False
    path = output / "prefix-manifest.json";publish(path, bad)
    try:
        merge(path, 0, output / "illegal-prefix-union")
    except AssertionError:
        negatives.append("prefix-manifest")
    else:
        raise AssertionError("accepted prefix as complete")
    for path in (
        Path(__file__), ROOT / "cover_origin_obstruction.inc", ROOT / "peel_origin_streamed_collar.cpp",
        ROOT / "peel_origin_streamed_collar-linux", ROOT / "merge_origin_collar_chunks.py",
        ROOT / "test_cover_origin.cpp", ROOT / "test_cover_origin-linux", ROOT / "seed_cover_origin.cpp",
        ROOT / "seed_cover_origin-linux", ROOT / "UNEXPOSED-ORIGIN-CENTER-SOURCE.md",
        ROOT / "origin-streamed-collar-source-derivation.json", ROOT / "origin-probe-source-derivation.json",
        ROOT / "origin-chunk-merge-source-derivation.json", ROOT / "refine_collar_origin.py",
        requestpath, answerpath, geometrypath, residual, origin,
    ):
        bind(files, path)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "actual-cover-origin-streamed-enumeration-controls-v1",
        "source_sha256": sha(Path(__file__)), "native_source_sha256": sha(ROOT / "peel_origin_streamed_collar.cpp"),
        "native_binary_sha256": sha(ROOT / "peel_origin_streamed_collar-linux"),
        "origin_guard_sha256": sha(ROOT / "cover_origin_obstruction.inc"),
        "merge_source_sha256": sha(ROOT / "merge_origin_collar_chunks.py"),
        "graph_requests": len(requests), "all_native_exposed_masks_match_independent_face_unions": True,
        "native_origin_obstructions": obstructions,
        "all_32_dihedral_attaining_controls_retained": True, "mathematical_controls": mathematical,
        "complete_small_family_controls": cases, "complete_restricted_N25_seed_controls": seed_cases,
        "complete_N25_other_B_control": full_N25, "negative_controls_rejected": negatives,
        "files_relative_to_workspace": files, "required_full_N25_families_not_run_here": True,
        "global_optimality_proved": False,
    })
    print("Actual-cover origin controls PASS:", len(requests), "independent graph checks;",
          len(cases), "complete small families;", len(seed_cases), "restricted N25 controls", flush=True)


if __name__ == "__main__":
    main()
