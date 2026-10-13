"""Complete B15 controls and true N25 seeded origin payments before stopping anything."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, bind, unchanged
from test_origin_collar import native, relative, terminal, run_enum, derivation_gate
from test_streamed_collar import codes_from_union
from test_outer_collar import collar_codes
from complete_simple_collar import simple_holes, budgets
from group_catalog import canonical
from merge_origin_collar_chunks import merge

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    derivation_gate()
    originpath = ROOT / "n25-origin-collar-controls-20261005-v1/VERIFIED.json"
    origin = read(originpath)
    assert origin["verified"] and origin["all_native_exposed_masks_match_independent_face_unions"]
    unchanged(origin["files_relative_to_workspace"])
    output.mkdir()
    files, cases, seeds = {}, [], []
    base = ROOT / "n25-B15-eight-sparse-guard-controls-20261005-v1"
    control = read(base / "VERIFIED.json")
    assert control["verified"] and control["all_baseline_minus_residual_graphs_individually_paid"]
    table = ROOT / "n25-B15-new-sparse-library-20261005-v1/OBSTACLES.tsv"
    for N, mode in ((21, "dfs"), (21, "audit"), (22, "dfs"), (22, "audit")):
        row = next(r for r in control["cases"] if r["N"] == N and r["mode"] == mode)
        reference = base / f"N{N}-B15-eight-sparse-{mode}.json"
        assert sha(reference) == row["residual_sha256"]
        _, expected = collar_codes(reference, N, 15)
        case = output / f"N{N}-{mode}";case.mkdir()
        target = case / "MANIFEST.json"
        result = run_enum(N, 15, target, "1", slab=7, mode=mode, table=table)
        terminal(result, target, case)
        assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
        union = merge(target, 0, case / "UNION")
        _, actual = codes_from_union(case / "UNION/CATALOG.jsonl")
        assert actual == expected and read(target)["origin_cover_prunes_not_type_count"] == 0
        cases.append({"N": N, "B": 15, "mode": mode, "complete_set_equal": True, "weak_graphs": len(actual),
                      "manifest_sha256": sha(target), "union_sha256": sha(case / "UNION/VERIFIED.json")})
        bind(files, reference)
        print("B15 complete origin regression PASS:", N, mode, len(actual), flush=True)
    # Only already-closed early slab files are sampled; never a live last slab.
    old = ROOT / "n25-B15-streamed-eight-sparse-search-20261005-v1"
    chosen = {}
    slab_controls = []
    for index in range(3):
        path = old / f"N25-B15-complete-sorted-chunks.json.chunk-{index}.jsonl"
        initial_hash = sha(path)
        rows = []
        with path.open(encoding="ascii") as stream:
            header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
            assert header["N"] == 25 and header["B"] == 15 and header["rows"] == 100000
            for line in stream:
                rows.append(json.loads(line, object_pairs_hook=no_duplicate_keys))
        assert len(rows) == header["rows"] and sha(path) == initial_hash
        slab_controls.append({"slab": index, "center_counts": dict(Counter(r["centers"] for r in rows))})
        for row in rows:
            category = row["centers"] == 25
            if category not in chosen:
                try:
                    holes = simple_holes(row["centers"], 15, row["faces"])
                except AssertionError:
                    continue
                if not holes:
                    continue
                chosen[category] = {**row, "holes": holes}
        bind(files, path)
        if len(chosen) == 2:
            break
    assert len(chosen) == 2
    for index, (category, row) in enumerate(sorted(chosen.items())):
        centers, outer, holes = row["centers"], row["faces"], row["holes"]
        allocation = next(budgets(25-centers, len(holes)))
        for flag in ("0", "1"):
            case = output / f"N25-seed{index}-origin{flag}";case.mkdir()
            tokens = [25, 15, centers, len(outer), *outer, len(holes)]
            for cycle, inside in zip(holes, allocation, strict=True):
                tokens.extend([len(cycle), inside, *cycle])
            inputpath = case / "INPUT.tsv"
            inputpath.write_text("\t".join(map(str, tokens))+"\n", encoding="ascii")
            target = case / "MANIFEST.json"
            result = native("seed_cover_origin-linux", [relative(inputpath), relative(target), flag, 1])
            terminal(result, target, case)
            assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
            union = merge(target, 0, case / "UNION")
            _, actual = codes_from_union(case / "UNION/CATALOG.jsonl")
            expected = set() if category and flag == "1" else {canonical(centers, 15, outer, 1)[0]}
            assert actual == expected
            seeds.append({"centers": centers, "flag": flag, "complete_restricted_result_paid_or_retained": True,
                          "not_a_complete_boundary_family": True,
                          "manifest_sha256": sha(target), "union_sha256": sha(case / "UNION/VERIFIED.json")})
    for path in (Path(__file__), originpath, base / "VERIFIED.json", table,
                 ROOT / "peel_origin_streamed_collar.cpp", ROOT / "peel_origin_streamed_collar-linux",
                 ROOT / "cover_origin_obstruction.inc", ROOT / "merge_origin_collar_chunks.py",
                 ROOT / "seed_cover_origin.cpp", ROOT / "seed_cover_origin-linux",
                 ROOT / "UNEXPOSED-ORIGIN-CENTER-SOURCE.md"):
        bind(files, path)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "B15-origin-replacement-controls-v1",
        "source_sha256": sha(Path(__file__)), "origin_controls_sha256": sha(originpath),
        "all_complete_B15_small_sets_equal": True, "cases": cases,
        "all_N25_seed_results_paid_or_retained": True, "seed_cases": seeds,
        "old_closed_slab_center_count_controls": slab_controls,
        "old_live_search_not_modified_or_stopped_by_controls": True,
        "sampled_slabs_not_a_complete_search": True, "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
