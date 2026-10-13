"""Derive a fixed-collar test adapter; do not change frozen search files."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from derive_sparse_support_filter import derive
from test_pending_degree_upper_small import derivation_gate

assert __debug__


def main():
    derivation_gate()
    path = ROOT / "pending-degree-controls-source-derivation.json"
    assert not path.exists()
    probe = derive("peel_pending_degree_origin_collar.cpp", "pending_degree_probe_body.inc", [
        ("int main(int argc,char**argv)", "int frozen_pending_degree_main(int argc,char**argv)"),
    ])
    seed = derive("seed_cached_support_origin.cpp", "seed_pending_degree_origin.cpp", [
        ('#include "cached_origin_probe_body.inc"', '#include "pending_degree_probe_body.inc"'),
        (' if(argc!=6)throw runtime_error("usage: seed-cached-origin input output flag slab strict-table");',
         ' if(argc!=7)throw runtime_error("usage: seed-pending-degree input output origin slab strict-table pending-degree-flag");'),
        (' load_sparse_obstacles(argv[5]);',
         ' load_sparse_obstacles(argv[5]);\n initialize_pending_degree_upper(argv[6]);'),
        ('write_cover_origin_summary(out);write_collar_chunk_manifest(out);',
         'write_cover_origin_summary(out);write_pending_degree_upper_summary(out);write_collar_chunk_manifest(out);'),
    ])
    publish(path, {
        "verified": True, "schema": "pending-degree-fixed-seed-control-derivation-v1",
        "files": [probe, seed], "source_sha256": sha(Path(__file__)),
        "same_original_fixed_seed_input_and_recursion": True,
        "not_a_complete_boundary_family": True, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
