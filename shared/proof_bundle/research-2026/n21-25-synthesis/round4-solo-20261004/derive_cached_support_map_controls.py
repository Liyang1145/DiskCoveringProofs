"""Mechanically instantiate the exact uncached map controls for the cached binary."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from derive_sparse_support_filter import derive

assert __debug__


def main():
    report_path = ROOT / "cached-support-map-control-source-derivation.json"
    assert not report_path.exists()
    changes = [
        ("from support_filter_gate import derivation_gate", "from cached_support_gate import derivation_gate"),
        ("sparse_support_match-linux", "sparse_support_cached_match-linux"),
        ("necessary-sparse-support-filter-map-controls-v1", "bounded-sparse-support-cache-map-controls-v1"),
        ("sparse-support-filter-source-derivation.json", "cached-sparse-support-source-derivation.json"),
    ]
    source, target = ROOT / "test_sparse_support_filter.py", ROOT / "test_cached_sparse_support.py"
    assert not target.exists()
    original = source.read_text(encoding="utf8")
    text = original
    counts = []
    for before, after in changes:
        count = text.count(before)
        assert count > 0
        counts.append(count)
        text = text.replace(before, after)
    reverse = text
    for before, after in reversed(changes):
        reverse = reverse.replace(after, before)
    assert reverse == original
    target.write_text(text, encoding="utf8", newline="\n")
    publish(report_path, {
        "verified": True, "schema": "cached-support-map-control-mechanical-instantiation-v1",
        "source": source.name, "original_source_sha256": sha(source),
        "target": target.name, "target_source_sha256": sha(target),
        "changes": changes, "occurrence_counts": counts, "exact_inverse_equals_frozen_source": True,
        "all_request_equality_positive_maps_and_negative_controls_unchanged": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("Cached matcher controls mechanically instantiated; exact inverse PASS", flush=True)


if __name__ == "__main__":
    main()
