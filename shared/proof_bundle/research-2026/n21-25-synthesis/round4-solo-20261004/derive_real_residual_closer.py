"""Keep the accepted completion pipeline; select only genuine unpaid parents."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    original = ROOT / "close_pending_simple_collars.py"
    target, reportpath = ROOT / "close_real_residual_collars.py", ROOT / "real-residual-closer-derivation.json"
    assert not target.exists() and not reportpath.exists()
    text = original.read_text(encoding="utf8")
    setup = '''    residual_root = args.residual.resolve()
    partition = read(residual_root / "VERIFIED.json")
    assert partition["verified"] and partition["all_complete_parent_rows_processed_once"]
    assert partition["schema"] == "complete-old-collar-independent-paid-partition-v1"
    assert partition["source_sha256"] == sha(ROOT / "filter_complete_collar_cached.py")
    unchanged(partition["files_relative_to_workspace"])
    assert (partition["N"], partition["B"]) == (source["N"], source["B"])
    assert partition["parent_groups_sha256"] == source["groups_sha256"]
    assert sha(residual_root / "RESIDUAL.jsonl") == partition["residual_sha256"]
    residual_ids, last = set(), -1
    with (residual_root / "RESIDUAL.jsonl").open(encoding="ascii") as stream:
        header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
        assert header["source_catalog_sha256"] == source["groups_sha256"]
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert last < row["id"] < partition["parent_weak_graphs"]
            last = row["id"]
            residual_ids.add(last)
    assert len(residual_ids) == partition["residual_weak_graphs"]
    excluded_running = set()
    excluded_selection_hashes = []
    for path in args.exclude_selection:
        selection = read(path)
        assert selection["parent_complete_catalog_sha256"] == source["groups_sha256"]
        excluded_running.update(selection["selected_parent_groups"])
        excluded_selection_hashes.append(sha(path))
    selected = []'''
    changes = [
        ('    ap.add_argument("--count", type=int, default=5)',
         '    ap.add_argument("--residual", type=Path, required=True)\n'
         '    ap.add_argument("--exclude-selection", type=Path, action="append", default=[])\n'
         '    ap.add_argument("--count", type=int, default=5)'),
        ("    selected = []", setup),
        ('            assert row["not_an_exclusion"]',
         '            assert row["not_an_exclusion"]\n'
         '            if row["group"] not in residual_ids or row["group"] in excluded_running:\n'
         '                continue'),
        ('        "selected_parent_groups": [r["group"] for r in selected],',
         '        "selected_parent_groups": [r["group"] for r in selected],\n'
         '        "real_residual_report_sha256": sha(residual_root / "VERIFIED.json"),\n'
         '        "real_residual_sha256": partition["residual_sha256"],\n'
         '        "excluded_running_selection_sha256": excluded_selection_hashes,\n'
         '        "selected_only_actual_unpaid_parents": True,'),
        ('    assert sha(catalog / "GROUPS.json") == source["groups_sha256"]',
         '    assert sha(residual_root / "RESIDUAL.jsonl") == partition["residual_sha256"]\n'
         '    assert [sha(path) for path in args.exclude_selection] == excluded_selection_hashes\n'
         '    assert sha(catalog / "GROUPS.json") == source["groups_sha256"]'),
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
        "all_completion_proposal_exact_replay_and_closure_steps_unchanged": True,
        "genuine_residual_intersection_and_running_selection_exclusion_only": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
