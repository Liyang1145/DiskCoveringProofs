"""Coverage/refusal tests for the new gapped full-parent acceptance adapter."""
from pathlib import Path
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from library_parent_pending_worklist import consecutive_jobs
from audit_library_parent_fillings import check_job_partition

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    entries = [{"snapshot_position": pos} for pos in (0, 1, 4, 5, 6, 8)]
    jobs = consecutive_jobs([entry["snapshot_position"] for entry in entries], 2)
    check_job_partition(entries, jobs)
    rejected, cases = [], []
    cases.append(("missing-final-job", entries, jobs[:-1]))
    cases.append(("duplicate-job", entries, jobs+jobs[-1:]))
    cases.append(("unordered-jobs", entries, list(reversed(jobs))))
    changed = deepcopy(jobs);changed[1]["first"] = 2
    cases.append(("paid-gap-included", entries, changed))
    changed = deepcopy(jobs);changed[1]["selected_offset"] = 3
    cases.append(("wrong-selected-offset", entries, changed))
    changed = deepcopy(jobs);changed[0]["count"] = 0
    cases.append(("zero-worker-range", entries, changed))
    changed = deepcopy(jobs);changed[0]["count"] = 1025
    cases.append(("oversized-worker-range", entries, changed))
    changed = deepcopy(jobs);changed[0]["first"] = False
    cases.append(("boolean-first-position", entries, changed))
    changed = deepcopy(jobs);changed[0]["job"] = False
    cases.append(("boolean-job-ordinal", entries, changed))
    changed = deepcopy(jobs);changed[0]["selected_offset"] = False
    cases.append(("boolean-selected-offset", entries, changed))
    changed = deepcopy(entries);changed[0]["snapshot_position"] = False
    cases.append(("boolean-selected-position", changed, jobs))
    for label, selected, descriptors in cases:
        try:
            check_job_partition(selected, descriptors)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("bad gapped full-parent job accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "library-parent-filling-job-audit-controls-v1",
        "finite_exact_selected_range_partition_positive": True,
        "negative_controls_rejected": rejected, "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_library_parent_fillings.py"),
        "complete_source_and_exact_filling_tree_replays_required_separately": True,
        "no_mathematical_family_payment_by_functional_controls": True, "global_optimality_proved": False,
    })
    print("Gapped library-parent full audit controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
