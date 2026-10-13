"""Fixed-collar control adapter only; no full-family or recursion changes."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from cached_support_gate import derivation_gate
from derive_sparse_support_filter import derive

assert __debug__


def main():
    files = derivation_gate()
    report_path = ROOT / "cached-origin-seed-source-derivation.json"
    assert not report_path.exists()
    probe = derive("peel_cached_support_origin_collar.cpp", "cached_origin_probe_body.inc", [
        ("int main(int argc,char**argv)", "int frozen_cached_origin_main(int argc,char**argv)"),
    ])
    seed = derive("seed_cover_origin.cpp", "seed_cached_support_origin.cpp", [
        ('#include "origin_collar_probe_body.inc"', '#include "cached_origin_probe_body.inc"'),
        (' if(argc!=5)throw runtime_error("usage: seed-origin input output flag slab");',
         ' if(argc!=6)throw runtime_error("usage: seed-cached-origin input output flag slab strict-table");'),
        (' initialize_cover_origin(argv[3]);initialize_collar_chunks(argv[2],stoull(argv[4]));',
         ' load_sparse_obstacles(argv[5]);\n'
         ' initialize_cover_origin(argv[3]);initialize_collar_chunks(argv[2],stoull(argv[4]));'),
    ])
    publish(report_path, {
        "verified": True, "schema": "cached-origin-fixed-seed-control-derivation-v1",
        "source_sha256": sha(Path(__file__)), "files": [probe, seed],
        "only_main_identity_include_and_strict_table_parameter_changed": True,
        "all_fixed_seed_recursion_and_origin_checks_unchanged": True,
        "not_a_complete_boundary_family": True, "global_optimality_proved": False,
    })
    print("Cached-origin fixed seed controls derived without changing recursion", flush=True)


if __name__ == "__main__":
    main()
