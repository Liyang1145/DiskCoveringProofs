"""Isolated state reuse prototype; not a replacement of any running native."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from derive_sparse_support_filter import derive

assert __debug__


def main():
    report_path = ROOT / "exact-state-reuse-source-derivation.json"
    assert not report_path.exists()
    record = derive("peel_cached_support_origin_collar.cpp", "peel_exact_state_origin_collar.cpp", [
        ('#include "sparse_support_cached_matcher.inc"',
         '#include "sparse_support_cached_matcher.inc"\n#include "exact_collar_state_reuse.inc"'),
        (' if(calls%1000000==0)cerr<<"COLLAR PROGRESS B="',
         ' auto completed_state_key=exact_collar_state_key(s,pending,omitted_faces);\n'
         ' if(exact_collar_state_already_completed(completed_state_key))return;\n'
         ' CompletedCollarStateVisit completed_state_guard(move(completed_state_key));\n'
         ' if(calls%1000000==0)cerr<<"COLLAR PROGRESS B="'),
        (' if(argc!=15)throw runtime_error("usage: origin-streamed-collar N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus cap8 slab-limit origin-cover-screen-0-or-1");',
         ' if(argc!=16)throw runtime_error("usage: exact-state-origin N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus cap8 slab-limit origin-cover-screen-0-or-1 exact-state-reuse-0-or-1");'),
        (' initialize_cover_origin(argv[14]);',
         ' initialize_cover_origin(argv[14]);\n initialize_exact_state_reuse(argv[15]);'),
        (' write_cover_origin_summary(out);',
         ' write_cover_origin_summary(out);\n write_exact_state_reuse_summary(out);'),
    ])
    publish(report_path, {
        "verified": True, "schema": "isolated-exact-completed-state-reuse-derivation-v1",
        "file": record, "source_sha256": sha(Path(__file__)),
        "state_reuse_provider_sha256": sha(ROOT / "exact_collar_state_reuse.inc"),
        "source_induction_sha256": sha(ROOT / "EXACT-COLLAR-STATE-REUSE-SOURCE.md"),
        "all_original_recursion_angles_origin_injection_storage_and_canonical_code_unchanged": True,
        "only_fully_equal_already_completed_states_can_be_reused": True,
        "no_running_native_or_input_modified": True, "global_optimality_proved": False,
    })
    print("Isolated exact completed-state reuse source derived; no live job changed", flush=True)


if __name__ == "__main__":
    main()
