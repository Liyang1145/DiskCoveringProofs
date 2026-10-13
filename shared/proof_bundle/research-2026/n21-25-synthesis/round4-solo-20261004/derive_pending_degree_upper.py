"""Isolate an earlier consequence of the frozen minimum-root degree guard."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from derive_sparse_support_filter import derive

assert __debug__


def main():
    report_path = ROOT / "pending-degree-upper-source-derivation.json"
    assert not report_path.exists()
    record = derive("peel_cached_support_origin_collar.cpp", "peel_pending_degree_origin_collar.cpp", [
        ('#include "sparse_support_cached_matcher.inc"',
         '#include "sparse_support_cached_matcher.inc"\n#include "pending_degree_upper.inc"'),
        (' if(already_cover_origin_paid(s))return;',
         ' if(pending_degree_upper_impossible(s,pending)){prunes++;return;}\n'
         ' if(already_cover_origin_paid(s))return;'),
        (' if(argc!=15)throw runtime_error("usage: origin-streamed-collar N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus cap8 slab-limit origin-cover-screen-0-or-1");',
         ' if(argc!=16)throw runtime_error("usage: pending-degree-origin N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus cap8 slab-limit origin-cover-screen-0-or-1 pending-degree-upper-0-or-1");'),
        (' initialize_cover_origin(argv[14]);',
         ' initialize_cover_origin(argv[14]);\n initialize_pending_degree_upper(argv[15]);'),
        (' write_cover_origin_summary(out);',
         ' write_cover_origin_summary(out);\n write_pending_degree_upper_summary(out);'),
    ])
    publish(report_path, {
        "verified": True, "schema": "isolated-pending-degree-upper-derivation-v1",
        "file": record, "source_sha256": sha(Path(__file__)),
        "provider_sha256": sha(ROOT / "pending_degree_upper.inc"),
        "source_induction_sha256": sha(ROOT / "PENDING-DEGREE-UPPER-SOURCE.md"),
        "all_original_recursion_angles_origin_injection_storage_and_code_unchanged": True,
        "only_earlier_consequence_of_existing_minimum_root_degree_rule": True,
        "no_running_native_or_input_modified": True, "global_optimality_proved": False,
    })
    print("Isolated pending-degree upper source derived; no live job changed", flush=True)


if __name__ == "__main__":
    main()
