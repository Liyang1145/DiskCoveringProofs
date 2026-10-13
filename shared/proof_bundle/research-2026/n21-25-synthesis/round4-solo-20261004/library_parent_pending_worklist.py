"""Explicit library-parent residual ranges into a genuine original root snapshot."""
from pathlib import Path
from collections import Counter
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read
from batch_origin_collar import parent_gate, catalog_rows
from audit_complete_origin_finer_supplement import valid_payment_partition
from audit_complete_origin_library_transport import pending_source

assert __debug__


def consecutive_jobs(positions, batch_size):
    assert type(batch_size) is int and 1 <= batch_size <= 1024
    assert positions and positions == sorted(set(positions))
    assert all(type(pos) is int and pos >= 0 for pos in positions)
    jobs = []
    start = 0
    while start < len(positions):
        end = start+1
        while (end < len(positions) and end-start < batch_size
               and positions[end] == positions[end-1]+1):
            end += 1
        jobs.append({"job": len(jobs), "first": positions[start], "count": end-start,
                     "selected_offset": start})
        start = end
    assert [pos for job in jobs for pos in range(job["first"], job["first"]+job["count"])] == positions
    return jobs


def select(snapshotpath, basepath):
    snapshotpath, basepath = snapshotpath.resolve(), basepath.resolve()
    assert snapshotpath.is_relative_to(ROOT) and basepath.is_relative_to(ROOT)
    snapshot, base = read(snapshotpath), read(basepath / "VERIFIED.json")
    assert snapshot["schema"] == "all-pending-complete-origin-parent-exact-graph-snapshot-v1"
    assert snapshot["source_sha256"] == sha(ROOT / "snapshot_complete_origin_pending.py")
    assert snapshot["all_full_parent_pending_rows_frozen_once"]
    assert snapshot["every_pending_parent_row_compared_against_full_catalog"]
    assert base["verified"] and base["schema"] == "complete-origin-parent-exact-outer-library-transport-merge-v2"
    assert base["source_sha256"] == sha(ROOT / "audit_complete_origin_library_transport_v2.py")
    assert base["all_parent_indices_disjointly_partitioned_once"]
    assert base["every_old_positive_weak_tree_freshly_mathematically_replayed"]
    assert base["all_library_complete_filling_trees_freshly_mathematically_replayed"]
    assert base["every_new_transport_requires_exact_complete_outer_face_equality"]
    assert base["new_library_payments_target_only_old_exact_pending_parent_indices"]
    assert (base["N"], base["B"]) == (snapshot["N"], snapshot["B"]) == (25, 16)
    for path, digest in {**snapshot["frozen_files"], **base["frozen_files"]}.items():
        assert Path(path).is_absolute() and sha(path) == digest
    original = {}
    previous = -1
    for pos, graph in enumerate(snapshot["graphs"]):
        pid = graph["parent_index"]
        assert type(pid) is int and pid > previous
        previous = pid
        original[pid] = (pos, graph)
    assert len(original) == snapshot["selected_pending_graphs"]
    parent = {key: Path(value) for key, value in snapshot["parent_inputs"].items()}
    assert base["base_report_sha256"] == sha(parent["payments"] / "VERIFIED.json")
    union, catalogpath, _ = parent_gate(parent["manifest"], parent["terminal"], parent["union"])
    total, N, B = union["unique_necessary_weak_graphs"], union["N"], union["B"]
    assert total == base["complete_parent_weak_graphs"] == snapshot["parent_weak_graphs"]
    assert sha(basepath / "PAYMENTS.jsonl") == base["payments_sha256"]
    assert sha(basepath / "PENDING.jsonl") == base["pending_sha256"]
    selected, counts = [], Counter()
    with (basepath / "PAYMENTS.jsonl").open(encoding="ascii") as paid, \
            (basepath / "PENDING.jsonl").open(encoding="ascii") as pending:
        partition = valid_payment_partition(total, paid, pending)
        for row in catalog_rows(catalogpath, N, B, total):
            pid, payment, unresolved = next(partition)
            assert pid == row["id"]
            if payment is not None:
                status = payment["status"]
                assert status in ("strict-exact-weak-graph-exclusion",
                                  "strict-complete-filling-family-exact-transport")
                counts[status] += 1
                if status == "strict-exact-weak-graph-exclusion":
                    assert pid not in original
                else:
                    assert pid in original
                continue
            assert pid in original
            pos, graph = original[pid]
            pending_source(row, unresolved, graph)
            selected.append({"snapshot_position": pos, **graph})
        assert next(partition, None) is None
    assert counts["strict-exact-weak-graph-exclusion"] == base["counts"]["old-strict-weak-force"]
    assert counts["strict-complete-filling-family-exact-transport"] == base["counts"]["new-strict-exact-outer-family-transport"]
    assert len(selected) == base["remaining_weak_graphs"] == base["counts"]["pending"]
    assert len(selected)+sum(counts.values()) == total
    return snapshot, base, selected
