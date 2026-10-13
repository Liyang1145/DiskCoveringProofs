"""Bind all pending graphs of an accepted full parent; no discovery relabelling."""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from batch_origin_collar import parent_gate, catalog_rows

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("manifest", "terminal", "union", "partition", "payments", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    paths = {name: getattr(args, name).resolve()
             for name in ("manifest", "terminal", "union", "partition", "payments", "output")}
    assert all(path.is_relative_to(ROOT) for path in paths.values())
    assert not paths["output"].exists()
    union, catalogpath, _ = parent_gate(paths["manifest"], paths["terminal"], paths["union"])
    reportpath = paths["payments"] / "VERIFIED.json"
    report = read(reportpath)
    assert report["verified"] and report["schema"] == "complete-streamed-collar-batch-payment-audit-v1"
    assert report["source_sha256"] == sha(ROOT / "audit_origin_collar_batches.py")
    assert report["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert report["all_parent_rows_stream_compared_against_exact_batch_inputs"]
    assert report["all_excluded_trees_fresh_exact_replayed_again"]
    assert report["parent_union_report_sha256"] == sha(paths["union"])
    assert report["parent_catalog_sha256"] == sha(catalogpath)
    assert report["partition_report_sha256"] == sha(paths["partition"])
    assert (report["N"], report["B"], report["parent_weak_graphs"]) == (
        union["N"], union["B"], union["unique_necessary_weak_graphs"])
    for field, name in (("payments_sha256", "PAYMENTS.jsonl"), ("pending_sha256", "PENDING.jsonl"),
                        ("audited_stages_sha256", "AUDITED-STAGES.jsonl")):
        assert report[field] == sha(paths["payments"] / name)
    constants = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    assert report["constants_sha256"] == sha(constants)
    batch_size = read(paths["partition"])["batch_size"]
    pendingpath = paths["payments"] / "PENDING.jsonl"
    graphs = []
    total, N, B = report["parent_weak_graphs"], report["N"], report["B"]
    with pendingpath.open(encoding="ascii") as stream:
        line = stream.readline()
        selected = json.loads(line, object_pairs_hook=no_duplicate_keys) if line else None
        for row in catalog_rows(catalogpath, N, B, total):
            if selected is None:
                continue
            assert selected["parent_index"] >= row["id"]
            if selected["parent_index"] != row["id"]:
                continue
            assert selected["not_a_geometric_exclusion"]
            assert (selected["centers"], selected["faces"]) == (row["centers"], row["faces"])
            assert selected["batch"] == row["id"]//batch_size
            assert selected["group"] == row["id"] % batch_size
            graphs.append({"parent_index": row["id"], "centers": row["centers"], "faces": row["faces"],
                           "source_batch": selected["batch"], "source_local_group": selected["group"]})
            line = stream.readline()
            selected = json.loads(line, object_pairs_hook=no_duplicate_keys) if line else None
        assert selected is None and not stream.read(1)
    assert len(graphs) == report["pending_weak_graphs"]
    frozenpaths = [
        paths["manifest"], paths["terminal"], paths["union"], paths["partition"], catalogpath,
        reportpath, pendingpath, paths["payments"] / "PAYMENTS.jsonl",
        paths["payments"] / "AUDITED-STAGES.jsonl", constants,
        ROOT / "audit_origin_collar_batches.py", HIGH / "exact_graph.py", Path(__file__).resolve(),
    ]
    frozen = {str(path): sha(path) for path in frozenpaths}
    paths["output"].parent.mkdir(parents=True, exist_ok=True)
    publish(paths["output"], {
        "schema": "all-pending-complete-origin-parent-exact-graph-snapshot-v1", "N": N, "B": B,
        "parent_weak_graphs": total, "selected_pending_graphs": len(graphs), "graphs": graphs,
        "every_pending_parent_row_compared_against_full_catalog": True,
        "all_full_parent_pending_rows_frozen_once": True,
        "not_an_incomplete_discovery_or_search_prefix": True,
        "frozen_files": frozen,
        "parent_inputs": {key: str(path) for key, path in paths.items() if key != "output"},
        "source_sha256": sha(Path(__file__)), "lower_bounds_not_paid_by_snapshot": True,
        "global_optimality_proved": False,
    })
    print("Entire complete-parent pending graph snapshot:", len(graphs), "graphs; no new payments", flush=True)


if __name__ == "__main__":
    main()
