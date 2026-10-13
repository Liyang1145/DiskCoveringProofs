"""Replace only bounded in-memory storage by sorted slab output."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    original = ROOT / "peel_eight_rod_collar.cpp"
    target = ROOT / "peel_streamed_collar.cpp"
    reportpath = ROOT / "streamed-collar-source-derivation.json"
    assert not target.exists() and not reportpath.exists()
    old = original.read_text(encoding="utf8")
    write_start = ' out<<",\\"weak_graphs\\":[";'
    write_end = ' out<<"]}\\n";out.close();if(!out)throw runtime_error("collar output write");'
    start, end = old.index(write_start), old.index(write_end)+len(write_end)
    old_writer = old[start:end]
    changes = [
        ("constexpr size_t COLLAR_MEMORY_LIMIT=2000000;",
         '#include "collar_chunk_storage.inc"'),
        ('if(collars.size()>COLLAR_MEMORY_LIMIT)\n   throw runtime_error("MEMORY LIMIT: collar catalogue incomplete");',
         'if(collars.size()>=collar_slab_limit)flush_collar_chunk();'),
        ('<<" weak_graphs="<<collars.size()', '<<" current_slab_rows="<<collars.size()'),
        ('if(argc!=13)throw runtime_error("usage: eight-rod-collar N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus cap8");',
         'if(argc!=14)throw runtime_error("usage: streamed-collar N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus cap8 slab-limit");'),
        ('load_sparse_obstacles(argv[11]);',
         'load_sparse_obstacles(argv[11]);\n initialize_collar_chunks(output,stoull(argv[13]));'),
        ('EIGHT ROD NATIVE PID=', 'STREAMED COLLAR NATIVE PID='),
        (' ofstream out(output);if(!out)throw runtime_error("collar output open");',
         ' flush_collar_chunk();\n ofstream out(output);if(!out)throw runtime_error("collar output open");'),
        ('outer-collar-overapproximation-v1', 'complete-outer-collar-sorted-chunks-v1'),
        ('<<",\\"weak_graph_count\\":"<<collars.size();',
         '<<",\\"unique_weak_graph_count_not_computed_by_native\\":true";'),
        (old_writer, ' write_collar_chunk_manifest(out);\n out<<"}\\n";out.close();if(!out)throw runtime_error("collar output write");'),
    ]
    text = old
    counts = []
    for before, after in changes:
        count = text.count(before)
        assert count > 0
        if before != '<<" weak_graphs="<<collars.size()':
            assert count == 1
        counts.append(count)
        text = text.replace(before, after)
    reconstructed = text
    for before, after in reversed(changes):
        reconstructed = reconstructed.replace(after, before)
    assert reconstructed == old
    target.write_text(text, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True, "original_source_sha256": sha(original),
        "derived_source_sha256": sha(target), "storage_include_sha256": sha(ROOT / "collar_chunk_storage.inc"),
        "source_sha256": sha(Path(__file__)), "changes": changes, "occurrence_counts": counts,
        "all_geometric_guards_and_recursive_branches_unchanged": True,
        "flush_membership_never_used_as_a_pruning_condition": True,
        "complete_union_requires_independent_merge_after_actual_zero_exit": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
