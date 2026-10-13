"""Complete small-family partition control with an eight-rod sparse guard.

Batch matching proposes one witness for every removed weak graph; Python
individually checks all such witnesses against fresh strict source theorems.
"""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import validate
from n25_outer_search import read, publish, bind, unchanged
from verify_sparse_maps_fast import library_gate, batch_match
from test_eight_rod_collar import run_eight, derivation_gate, collar_codes
from eight_rod_angles import constants_gate, CAP8

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--maps", type=Path, required=True)
    ap.add_argument("--eight-controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    constants, library, table, files = library_gate(args.library.resolve())
    B = library["B"]
    constants_gate(constants)
    derivation_gate()
    maps, eight = map(read, (args.maps, args.eight_controls))
    assert maps["verified"] and maps["schema"] == "fresh-sparse-library-explicit-map-controls-v1"
    assert maps["B"] == B and maps["library_sha256"] == sha(args.library)
    assert maps["source_sha256"] == sha(ROOT / "verify_sparse_maps_fast.py")
    assert maps["matcher_include_sha256"] == sha(ROOT / "sparse_outer_matcher.inc")
    assert maps["matcher_binary_sha256"] == sha(ROOT / "sparse_outer_match-linux")
    assert maps["all_source_trees_fresh_exact_replayed"]
    assert eight["verified"] and eight["schema"] == "eight-rod-collar-controls-v1"
    assert eight["source_sha256"] == sha(ROOT / "test_eight_rod_collar.py")
    assert eight["native_source_sha256"] == sha(ROOT / "peel_eight_rod_collar.cpp")
    assert eight["native_binary_sha256"] == sha(ROOT / "peel_eight_rod_collar-linux")
    assert eight["native_results_agree_with_independent_exact_cycles"]
    assert eight["all_four_exact_attaining_controls_retained"]
    output.mkdir()
    byid = {o["id"]: o for o in library["obstacles"]}
    cases = []
    sizes = {14: (20, 21), 15: (21, 22), 16: (22, 23), 17: (21, 22)}
    for N in sizes[B]:
        baseline = output / f"N{N}-B{B}-eight-baseline.json"
        result = run_eight(N, B, baseline)
        assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
        base_header, allcodes = collar_codes(baseline, N, B)
        bycode = {tuple(row["faces"]): row["centers"] for row in base_header["weak_graphs"]}
        for mode in ("dfs", "audit"):
            target = output / f"N{N}-B{B}-eight-sparse-{mode}.json"
            result = run_eight(N, B, target, mode, table)
            assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
            header, residual = collar_codes(target, N, B)
            assert residual <= allcodes
            removed = sorted(allcodes-residual)
            transfers = output / f"N{N}-B{B}-{mode}-removed-maps"
            transfers.mkdir()
            answers = batch_match(table, [list(code) for code in removed], transfers, N, B)
            assert len(answers) == len(removed)
            with (transfers / "ACCEPTED-MAPS.jsonl").open("x", encoding="utf8") as ledger:
                for code, answer in zip(removed, answers, strict=True):
                    assert answer["obstacle"] >= 0, "a removed weak graph has no paid source witness"
                    obstacle = byid[answer["obstacle"]]
                    mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
                    validate(bycode[code], B, obstacle["faces"], mapping, code)
                    ledger.write(json.dumps({"faces": list(code), "obstacle": obstacle["id"], "map": mapping},
                                            separators=(",", ":"))+"\n")
            for payment in header["sparse_payments"]:
                mapping = {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")}
                validate(N, B, byid[payment["obstacle"]]["faces"], mapping, payment["sample_faces"])
            cases.append({
                "N": N, "B": B, "mode": mode, "baseline_weak_graphs": len(allcodes),
                "residual_weak_graphs": len(residual), "all_removed_weak_graphs_explicitly_paid": True,
                "removed_graphs": len(removed), "baseline_sha256": sha(baseline),
                "residual_sha256": sha(target), "accepted_maps_sha256": sha(transfers / "ACCEPTED-MAPS.jsonl"),
            })
        print("Eight-rod B", B, "complete sparse partition accepted:", N, len(allcodes), "baseline", flush=True)
    negatives = []
    for label, N, boundary, limit in (("node-limit", 25, B, 1), ("bad-N", 26, B, 0), ("bad-B", B, B+1, 0)):
        target = output / (label+".json")
        result = run_eight(N, boundary, target, library=table, limit=limit)
        assert result.returncode != 0 and not target.exists()
        negatives.append(label)
    for path in (Path(__file__), args.maps, args.eight_controls,
                 ROOT / "verify_sparse_maps_fast.py", ROOT / "test_eight_rod_collar.py",
                 ROOT / "eight_rod_angles.py", ROOT / "eight_rod_possible.inc",
                 ROOT / "peel_eight_rod_collar.cpp", ROOT / "peel_eight_rod_collar-linux",
                 ROOT / "EIGHT-ROD-ANGLE-SOURCE.md", ROOT / "eight-rod-collar-source-derivation.json"):
        bind(files, path)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "eight-rod-sparse-complete-partition-controls-v1",
        "N": 25, "B": B, "source_sha256": sha(Path(__file__)),
        "library_sha256": sha(args.library), "maps_controls_sha256": sha(args.maps),
        "eight_controls_sha256": sha(args.eight_controls), "cap8": CAP8,
        "native_source_sha256": sha(ROOT / "peel_eight_rod_collar.cpp"),
        "native_binary_sha256": sha(ROOT / "peel_eight_rod_collar-linux"),
        "sparse_guard_sha256": sha(ROOT / "sparse_outer_matcher.inc"),
        "all_baseline_minus_residual_graphs_individually_paid": True,
        "cases": cases, "negative_controls_rejected": negatives,
        "files_relative_to_workspace": files, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
