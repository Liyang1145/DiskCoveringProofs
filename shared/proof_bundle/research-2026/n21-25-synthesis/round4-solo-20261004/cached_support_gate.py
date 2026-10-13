"""Recheck isolated cache derivation and its uncached necessary-filter parent."""
from pathlib import Path
from stream_catalog import sha
from n25_outer_search import read, bind, unchanged
from support_filter_gate import derivation_gate as uncached_derivation_gate

ROOT = Path(__file__).resolve().parent
assert __debug__


def derivation_gate():
    files = uncached_derivation_gate()
    path = ROOT / "cached-sparse-support-source-derivation.json"
    report = read(path)
    assert report["verified"] and report["schema"] == "bounded-sparse-support-cache-derivation-v1"
    assert report["source_sha256"] == sha(ROOT / "derive_cached_sparse_support.py")
    assert report["prior_derivation_sha256"] == sha(ROOT / "sparse-support-filter-source-derivation.json")
    assert report["source_lemma_sha256"] == sha(ROOT / "SPARSE-SUPPORT-CACHE-SOURCE.md")
    assert report["complete_integer_key_contains_all_filter_target_values"]
    assert report["original_variant_and_internal_search_order_preserved"]
    assert report["all_positive_checks_and_recursion_unchanged"] and report["cache_eviction_not_a_recursion_prune"]
    assert report["maximum_cached_keys"] == 4096 and report["maximum_cached_candidate_indices"] == 1048576
    assert [(r["source"], r["target"]) for r in report["files"]] == [
        ("sparse_support_matcher.inc", "sparse_support_cached_matcher.inc"),
        ("sparse_support_match.cpp", "sparse_support_cached_match.cpp"),
        ("peel_support_eight_collar.cpp", "peel_cached_support_eight_collar.cpp"),
        ("peel_support_origin_collar.cpp", "peel_cached_support_origin_collar.cpp"),
    ]
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
    for item in (path, Path(__file__), ROOT / "derive_cached_sparse_support.py",
                 ROOT / "SPARSE-SUPPORT-CACHE-SOURCE.md"):
        bind(files, item)
    unchanged(files)
    return files
