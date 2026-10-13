"""Add only the exact actual-cover origin obstruction to frozen streaming search."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    original, target = ROOT / "peel_streamed_collar.cpp", ROOT / "peel_origin_streamed_collar.cpp"
    reportpath = ROOT / "origin-streamed-collar-source-derivation.json"
    assert not target.exists() and not reportpath.exists()
    text = original.read_text(encoding="utf8")
    changes = [
        ('#include "collar_chunk_storage.inc"',
         '#include "collar_chunk_storage.inc"\n#include "cover_origin_obstruction.inc"'),
        (' if(already_sparse_paid(s))return;',
         ' if(already_cover_origin_paid(s))return;\n if(already_sparse_paid(s))return;'),
        ('if(argc!=14)throw runtime_error("usage: streamed-collar N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus cap8 slab-limit");',
         'if(argc!=15)throw runtime_error("usage: origin-streamed-collar N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus cap8 slab-limit origin-cover-screen-0-or-1");'),
        (' initialize_collar_chunks(output,stoull(argv[13]));',
         ' initialize_collar_chunks(output,stoull(argv[13]));\n initialize_cover_origin(argv[14]);'),
        ('STREAMED COLLAR NATIVE PID=', 'COVER ORIGIN NATIVE PID='),
        ('complete-outer-collar-sorted-chunks-v1', 'complete-cover-origin-collar-sorted-chunks-v1'),
        (' write_sparse_summary(out);', ' write_sparse_summary(out);\n write_cover_origin_summary(out);'),
    ]
    counts = []
    for before, after in changes:
        assert text.count(before) == 1, before
        counts.append(1)
        text = text.replace(before, after)
    target.write_text(text, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True,
        "original_source_sha256": sha(original), "derived_source_sha256": sha(target),
        "origin_guard_sha256": sha(ROOT / "cover_origin_obstruction.inc"),
        "source_sha256": sha(Path(__file__)), "changes": changes, "occurrence_counts": counts,
        "all_old_recursive_branches_angle_and_sparse_guards_unchanged": True,
        "new_pruning_requires_actual_N25_arbitrary_cover_domain": True,
        "new_guard_not_a_standalone_weak_geometry_exclusion": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
