"""Bounded performance diagnostic; all runs intentionally remain incomplete."""
from pathlib import Path
import argparse
import re
import sys
import time

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate
from cached_support_gate import derivation_gate
from test_cached_support_origin_partition import native_logged
from test_origin_collar import relative

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--limit", type=int, default=100000)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists() and 1000 <= args.limit <= 1000000
    files = derivation_gate()
    constants = read(ROOT.parent / "evidence/core-reduction/constants/n25.json")
    output.mkdir()
    cases = []
    for name, binary, library_path in (
        ("old-two", "peel_origin_streamed_collar-linux",
         ROOT / "n25-B16-new-sparse-library-20261005-v1/LIBRARY.json"),
        ("uncached-164", "peel_support_origin_collar-linux",
         ROOT / "n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json"),
        ("cached-164", "peel_cached_support_origin_collar-linux",
         ROOT / "n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json"),
    ):
        _, library, table, dependencies = sparse_library_gate(library_path)
        files.update(dependencies)
        directory = output / name
        directory.mkdir()
        target = directory / "INCOMPLETE-MANIFEST.json"
        code, seconds = native_logged(binary, [
            25, 16, relative(target), constants["angle_scale"], *constants["angle_caps"],
            args.limit, "dfs", "-", relative(table), 4058615, 100000, 1,
        ], directory)
        assert code != 0 and not target.exists()
        text = (directory / "NATIVE-STDERR.log").read_text(encoding="utf8")
        assert "REJECTED NODE LIMIT: incomplete collar search, no completion" in text
        cases.append({
            "name": name, "node_limit": args.limit, "actual_exit_code": code, "seconds": seconds,
            "obstacles": library["obstacle_count"], "not_complete_or_a_proof_of_exhaustion": True,
            "log_sha256": sha(directory / "NATIVE-STDERR.log"), "binary_sha256": sha(ROOT / binary),
        })
        bind(files, ROOT / binary);bind(files, library_path)
        print("Intentionally incomplete support benchmark:", name, args.limit,
              "calls;", round(seconds, 3), "seconds; nonzero node-limit exit verified", flush=True)
    bind(files, Path(__file__))
    unchanged(files)
    publish(output / "DIAGNOSTIC.json", {
        "schema": "intentionally-incomplete-support-origin-performance-diagnostic-v1",
        "N": 25, "B": 16, "cases": cases, "all_native_terminal_results_collected": True,
        "no_successful_search_manifest_or_complete_family_claim": True,
        "search_prefixes_not_recovery_points": True, "source_sha256": sha(Path(__file__)),
        "files_relative_to_workspace": files, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
