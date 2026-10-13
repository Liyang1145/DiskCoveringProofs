"""Retain all bounded partition/replay logic, require actual N25 origin-qualified parents."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    reportpath = ROOT / "origin-batch-tools-source-derivation.json"
    assert not reportpath.exists()
    reports = []
    jobs = [
        ("batch_streamed_collar.py", "batch_origin_collar.py", [
            ('    assert manifest["schema"] == "complete-outer-collar-sorted-chunks-v1"',
             '    assert manifest["schema"] == "complete-cover-origin-collar-sorted-chunks-v1"\n'
             '    assert manifest["N"] == 25 and manifest["B"] in (14, 15, 16, 17)\n'
             '    assert manifest["origin_cover_screen"] and manifest["origin_cover_only_N25"]\n'
             '    assert manifest["origin_cover_scope"] == "actual arbitrary disk covers only; not weak graph geometry"\n'
             '    assert not manifest.get("seeded_fixed_collar_restriction", False), "restricted seed is not the complete family"\n'
             '    assert manifest["origin_radius_upper_numerator"] == 239146311738101\n'
             '    assert manifest["origin_radius_upper_denominator"] == 10**15'),
            ('sha(ROOT / "merge_collar_chunks.py")', 'sha(ROOT / "merge_origin_collar_chunks.py")'),
            ('            assert type(centers) is int and B <= centers <= N',
             '            assert type(centers) is int and B <= centers < N'),
            ('        "lower_bounds_not_paid_by_partition": True, "global_optimality_proved": False,',
             '        "parent_requires_actual_cover_origin_condition": True,\n'
             '        "not_an_unqualified_geometric_weak_graph_family": True,\n'
             '        "lower_bounds_not_paid_by_partition": True, "global_optimality_proved": False,'),
        ]),
        ("audit_collar_batch_payments.py", "audit_origin_collar_batches.py", [
            ("from batch_streamed_collar import parent_gate, catalog_rows, identity",
             "from batch_origin_collar import parent_gate, catalog_rows, identity"),
            ('sha(ROOT / "batch_streamed_collar.py")', 'sha(ROOT / "batch_origin_collar.py")'),
            ('        "source_cover_transport_and_other_families_still_required": True,',
             '        "parent_requires_actual_cover_origin_condition": True,\n'
             '        "not_an_unqualified_geometric_weak_graph_family": True,\n'
             '        "source_cover_transport_and_other_families_still_required": True,'),
        ]),
    ]
    for originalname, derivedname, changes in jobs:
        original, target = ROOT / originalname, ROOT / derivedname
        assert not target.exists()
        text = original.read_text(encoding="utf8")
        counts = []
        for before, after in changes:
            count = text.count(before)
            assert count == 1, (before, count)
            counts.append(count)
            text = text.replace(before, after)
        target.write_text(text, encoding="utf8", newline="\n")
        reports.append({
            "original": originalname, "derived": derivedname,
            "original_sha256": sha(original), "derived_sha256": sha(target),
            "changes": changes, "occurrence_counts": counts,
        })
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True, "files": reports,
        "all_original_zero_exit_union_slab_partition_and_exact_replay_checks_preserved": True,
        "new_parent_constraints_stricter_not_weaker": True,
        "actual_complete_origin_production_parent_validation_still_required": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
