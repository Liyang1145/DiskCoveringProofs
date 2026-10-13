"""Keep every classifier/check unchanged, reuse finished native map batches."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    original = ROOT / "filter_complete_collar.py"
    target, reportpath = ROOT / "filter_complete_collar_cached.py", ROOT / "cached-collar-filter-derivation.json"
    assert not target.exists() and not reportpath.exists()
    text = original.read_text(encoding="utf8")
    changes = [
        ("from verify_sparse_maps_fast import library_gate, batch_match",
         "from verify_sparse_maps_fast import library_gate\nfrom cached_collar_maps import cached_batch_match"),
        ('    ap.add_argument("--closure", type=Path, action="append", default=[])',
         '    ap.add_argument("--cached-run", type=Path, required=True)\n'
         '    ap.add_argument("--closure", type=Path, action="append", default=[])'),
        ('    unchanged(files)\n    output.mkdir()',
         '    cached_bindings = read(args.cached_run.resolve() / "INPUT-BINDINGS.json")\n'
         '    assert (cached_bindings["N"], cached_bindings["B"], cached_bindings["parent_weak_graphs"]) == (25, B, total)\n'
         '    unchanged(cached_bindings["files_relative_to_workspace"])\n'
         '    for path in (args.cached_run.resolve() / "INPUT-BINDINGS.json",\n'
         '                 ROOT / "cached_collar_maps.py", ROOT / "derive_cached_collar_filter.py",\n'
         '                 ROOT / "filter_complete_collar.py", ROOT / "cached-collar-filter-derivation.json"):\n'
         '        bind(files, path)\n'
         '    unchanged(files)\n    output.mkdir()'),
        ('            answers = batch_match(table, [row["faces"] for row in rows], directory, 25, B)',
         '            answers = cached_batch_match(table, [row["faces"] for row in rows], directory, 25, B,\n'
         '                                         args.cached_run, files)'),
        ('        "not_a_global_n25_proof": True, "global_optimality_proved": False,',
         '        "cached_partial_pass_not_accepted_as_complete": True,\n'
         '        "unavailable_sparse_matches_conservatively_kept_unpaid": True,\n'
         '        "not_a_global_n25_proof": True, "global_optimality_proved": False,'),
    ]
    counts = []
    for before, after in changes:
        assert text.count(before) == 1
        counts.append(1)
        text = text.replace(before, after)
    target.write_text(text, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True,
        "original_source_sha256": sha(original), "derived_source_sha256": sha(target),
        "source_sha256": sha(Path(__file__)), "changes": changes, "occurrence_counts": counts,
        "all_source_row_and_mathematical_payment_checks_unchanged": True,
        "backend_failure_never_a_geometric_exclusion": True, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
