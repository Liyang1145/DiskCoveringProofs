"""Check exact new-file support-filter derivation without importing an optimizer."""
from pathlib import Path
from n25_outer_search import read, bind, unchanged
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def derivation_gate():
    path = ROOT / "sparse-support-filter-source-derivation.json"
    report = read(path)
    assert report["verified"] and report["schema"] == "necessary-sparse-support-filter-derivation-v1"
    assert report["source_sha256"] == sha(ROOT / "derive_sparse_support_filter.py")
    assert report["source_lemma_sha256"] == sha(ROOT / "SPARSE-SUPPORT-NECESSARY-FILTERS.md")
    assert report["only_necessary_matching_filters_and_include_names_changed"]
    assert report["all_existing_candidate_search_and_positive_injection_checks_unchanged"]
    assert report["full_search_recursion_angles_storage_and_origin_condition_unchanged"]
    assert [(r["source"], r["target"]) for r in report["files"]] == [
        ("sparse_outer_matcher.inc", "sparse_support_matcher.inc"),
        ("sparse_outer_match.cpp", "sparse_support_match.cpp"),
        ("peel_eight_rod_collar.cpp", "peel_support_eight_collar.cpp"),
        ("peel_origin_streamed_collar.cpp", "peel_support_origin_collar.cpp"),
    ]
    files = {}
    for record in report["files"]:
        source, target = ROOT / record["source"], ROOT / record["target"]
        assert sha(source) == record["source_sha256"] and sha(target) == record["target_sha256"]
        text = source.read_text(encoding="utf8")
        for before, after in record["changes"]:
            assert text.count(before) == 1
            text = text.replace(before, after)
        assert text == target.read_text(encoding="utf8")
        reverse = text
        for before, after in reversed(record["changes"]):
            assert reverse.count(after) == 1
            reverse = reverse.replace(after, before)
        assert reverse == source.read_text(encoding="utf8")
        bind(files, source);bind(files, target)
    for item in (path, Path(__file__), ROOT / "derive_sparse_support_filter.py",
                 ROOT / "SPARSE-SUPPORT-NECESSARY-FILTERS.md"):
        bind(files, item)
    unchanged(files)
    return files
