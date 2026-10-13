"""Exact general filling on the entire pinched subset of the complete residual."""
from pathlib import Path
from collections import Counter
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish, bind, unchanged
from stream_catalog import sha, no_duplicate_keys
from complete_simple_collar import simple_holes
from test_linked_general_collar import derivation_gate
from general_collar_filling_linked import start_states
from prove_linked_general_collar import propose

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("parent", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--limit", type=int, default=20000)
    args = ap.parse_args()
    parent, controlspath, output = (getattr(args, name).resolve() for name in ("parent", "controls", "output"))
    assert output.is_relative_to(ROOT) and not output.exists()
    derivation_gate()
    controls = read(controlspath)
    assert controls["verified"] and controls["schema"] == "linked-general-collar-filling-controls-v1"
    for field, name in (
        ("source_sha256", "test_linked_general_collar.py"), ("kernel_sha256", "linked_general_collar_kernel.py"),
        ("provider_sha256", "general_collar_filling_linked.py"),
        ("proposal_source_sha256", "prove_linked_general_collar.py"),
        ("replay_source_sha256", "replay_linked_general_collar.py"),
        ("source_induction_sha256", "GENERAL-COLLAR-FILLING-SOURCE.md"),
    ):
        assert controls[field] == sha(ROOT / name)
    assert controls["all_no_payment_complete_type_sets_equal_to_references"]
    assert controls["pinched_complete_branch_cover_independently_replayed"]
    assert controls["pinched_control_all_completions_strictly_paid"]
    assert controls["known_attaining_candidate_not_strictly_paid"]
    assert set(controls["negative_controls_rejected"]) == {
        "deleted-topology-child", "link-degree-three",
        "closed-link-component-plus-another-component", "node-limit-explicitly-unpaid"}
    unchanged(controls["files_relative_to_workspace"])
    reportpath, residualpath = parent / "VERIFIED.json", parent / "RESIDUAL.jsonl"
    report = read(reportpath)
    assert report["verified"] and report["schema"] == "complete-origin-residual-exact-force-refinement-v1"
    assert report["source_sha256"] == sha(ROOT / "pay_origin_refined_force.py")
    assert report["every_parent_residual_row_compared_with_complete_catalog_and_identity_map"]
    assert sha(residualpath) == report["residual_sha256"]
    unchanged(report["files_relative_to_workspace"])
    N, B = report["N"], report["B"]
    rows, skipped = [], 0
    with residualpath.open(encoding="ascii") as stream:
        header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
        assert header["schema"] == "complete-collar-origin-and-exact-force-residual-v1"
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            try:
                simple_holes(row["centers"], B, row["faces"])
            except AssertionError as error:
                assert str(error) == "pinched hole boundary"
                start_states(N, B, row["centers"], row["faces"])
                rows.append(row)
            else:
                skipped += 1
    assert len(rows)+skipped == report["remaining_weak_graphs"]
    assert [r["id"] for r in rows] == sorted(set(r["id"] for r in rows))
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    files = {}
    for path in (Path(__file__), controlspath, reportpath, residualpath, constants_path,
                 ROOT / "linked_general_collar_kernel.py", ROOT / "general_collar_filling.py",
                 ROOT / "general_collar_filling_linked.py", ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md",
                 ROOT / "prove_linked_general_collar.py", ROOT / "replay_linked_general_collar.py",
                 ROOT / "linked-general-paid-collar-source-derivation.json",
                 ROOT / "general-paid-collar-source-derivation.json"):
        bind(files, path)
    unchanged(files)
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": N, "B": B, "selected_pinched_parent_groups": [r["id"] for r in rows],
        "complete_parent_residual_rows": report["remaining_weak_graphs"],
        "all_pinched_rows_selected_exactly_once": True, "simple_rows_skipped": skipped,
        "maximum_proposed_states_per_family": args.limit, "files_relative_to_workspace": files,
        "all_other_parent_rows_not_paid_by_this_stage": True, "global_optimality_proved": False,
    })
    counts = Counter()
    with (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as ledger:
        for index, row in enumerate(rows):
            gid = row["id"]
            directory = output / f"parent-{gid:07}";directory.mkdir()
            collarpath, proposalpath, exactpath = (directory / name for name in
                                                   ("INPUT-COLLAR.json", "PROPOSAL.json", "EXACT.json"))
            collar = {"N": N, "B": B, "centers": row["centers"], "faces": row["faces"],
                      "source_parent_group": gid}
            publish(collarpath, collar)
            payload = propose(collar, constants, args.limit, 1)
            payload.update(source_collar_sha256=sha(collarpath), constants_sha256=sha(constants_path),
                           kernel_sha256=sha(ROOT / "linked_general_collar_kernel.py"),
                           source_sha256=sha(ROOT / "prove_linked_general_collar.py"),
                           whole_family_payment_requires_independent_replay=True, global_optimality_proved=False)
            publish(proposalpath, payload)
            process = subprocess.run([
                sys.executable, str(ROOT / "replay_linked_general_collar.py"), "--collar", str(collarpath),
                "--proposal", str(proposalpath), "--output", str(exactpath),
            ], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
            publish(directory / "REPLAY-TERMINAL.json", {
                "independent_process_terminal_observed": True, "actual_exit_code": process.returncode,
                "stdout": process.stdout.decode(errors="replace"), "stderr": process.stderr.decode(errors="replace"),
            })
            status = {"parent_group": gid, "status": "unpaid",
                      "not_a_standalone_geometric_weak_graph_exclusion": True}
            if process.returncode == 0:
                accepted = read(exactpath)
                assert accepted["verified"]
                assert (accepted["N"], accepted["B"], accepted["collar_centers"], accepted["collar_faces"]) == (
                    N, B, row["centers"], row["faces"])
                unchanged(accepted["files_relative_to_workspace"])
                if accepted["all_full_simple_disk_completions_strictly_paid"]:
                    status.update(status="strictly-paid-general-filling-family",
                                  exact_sha256=sha(exactpath), proposal_sha256=sha(proposalpath),
                                  branch_nodes=accepted["nodes"])
                    ledger.write(json.dumps(status, separators=(",", ":"))+"\n")
                else:
                    status.update(pending_complete_leaves=accepted["pending_complete_leaves"],
                                  frontier=accepted["unsearched_frontier_nodes"])
            else:
                status["reason"] = "independent exact replay failed; not paid"
            counts[status["status"]] += 1
            publish(directory / "STATUS.json", status)
            ledger.flush()
            print("Pinched fixed-family payment:", index+1, "/", len(rows), gid,
                  status["status"], flush=True)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-pinched-residual-subset-payment-v1", "N": N, "B": B,
        "all_parent_pinched_rows_selected_and_processed_once": True,
        "selected_pinched_families": len(rows), "simple_families_not_paid_here": skipped,
        "counts": dict(counts), "parent_report_sha256": sha(reportpath),
        "payments_sha256": sha(output / "PAYMENTS.jsonl"),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "all_other_parent_rows_not_paid_here": True, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
