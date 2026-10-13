"""Successor distinguishing original group ID 522460 from its 169 members.

The v1 selection helper/control remains frozen. Its erroneous startup member
guard stopped before any output or solver work. No v1 evidence is rewritten.
This is proposal-only; independent replay and residual type mapping are distinct.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from probe_n23_remaining_outer import select_remaining
from probe_collar_batches import make
import exact_graph as exact

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("parent", "outer", "core", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--limit", type=int, default=31)
    args = ap.parse_args()
    parent, outer, corepath, controlpath, output = (
        getattr(args, name).resolve() for name in ("parent", "outer", "core", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (parent, outer, corepath, controlpath, output))
    assert not output.exists() and 1 < args.limit <= 1001
    controls = read(controlpath)
    assert controls["verified"] and controls["schema"] == "N23-remaining-outer-proposal-selection-controls-v1"
    assert controls["proposal_source_sha256"] == sha(ROOT / "probe_n23_remaining_outer.py")
    assert controls["source_sha256"] == sha(ROOT / "test_n23_remaining_outer_selection.py")
    assert controls["core_sha256"] == sha(corepath) and controls["known_attaining_group_retained"]
    assert len(controls["negative_controls_rejected"]) == 11
    accepted = read(parent / "VERIFIED.json")
    assert accepted["verified"]
    assert accepted["schema"] == "complete-N23-B15-origin-pair-and-effective-outer-disjoint-payment-v1"
    assert accepted["source_sha256"] == sha(ROOT / "audit_n23_B15_effective_outer_payment.py")
    assert accepted["all_previous_unpaid_source_face_center_anchor_maps_independently_checked"]
    assert accepted["all_22857_positive_outer_trees_freshly_exact_replayed_again"]
    assert accepted["pending_full_types"] == 793841
    for path, digest in accepted["frozen_files"].items():
        assert sha(path) == digest
    assert sha(parent / "PENDING.jsonl") == accepted["pending_sha256"]
    groupspath, previouspath = outer / "OUTER/GROUPS.json", outer / "FORCE/SUMMARY.json"
    data, previous, core = map(read, (groupspath, previouspath, corepath))
    assert (data["N"], data["B"], data["threshold"], data["group_count"]) == (23, 15, 1, 535262)
    assert previous["groups_sha256"] == sha(groupspath) and previous["excluded_groups"] == 22857
    selected, known = select_remaining(data["groups"], previous["outcomes"], core)
    assert len(selected) == 6879
    assert sum(g["members"] for g in selected) == accepted["pending_full_types"]
    assert known == 522460 and data["groups"][known]["members"] == 169
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constants_path)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    frozenpaths = (
        Path(__file__), ROOT / "probe_n23_remaining_outer.py",
        parent / "VERIFIED.json", parent / "PENDING.jsonl",
        groupspath, previouspath, corepath, controlpath, constants_path,
        ROOT / "probe_collar_batches.py", HIGH / "exact_graph.py",
        HIGH / "candidate_domain.py", HIGH / "group_catalog.py",
        HIGH / "replay_group_stage.py",
    )
    frozen = {str(path): sha(path) for path in frozenpaths}
    output.mkdir()
    publish(output / "INPUT-SNAPSHOT.json", {
        "schema": "original-N23-B15-remaining-outer-proposal-input-v2",
        "N": 23, "B": 15, "selected_original_groups": [g["id"] for g in selected],
        "selected_group_count": len(selected), "associated_original_group_members": 793841,
        "known_attaining_original_group": known,
        "known_attaining_members": data["groups"][known]["members"],
        "original_group_identifier_not_confused_with_member_count": True,
        "v1_startup_guard_failed_before_solver_or_output_not_a_completed_stage": True,
        "core_path_explicit_not_default_path_fabrication": str(corepath),
        "force_node_limit": args.limit, "frozen_files": frozen,
        "not_yet_a_fresh_residual_type_mapping_or_payment_merge": True,
        "global_optimality_proved": False,
    })
    outcomes = [{"group": g["id"], "status": "pending",
                 "not_selected_by_this_new_proposal_stage": True} for g in data["groups"]]
    totals, covered = Counter(), 0
    started = time.monotonic()
    with (output / "outcomes.jsonl").open("x", encoding="ascii") as ledger:
        for step, group in enumerate(selected, 1):
            if group["id"] == known:
                nodes, failure = None, {"known_exact_attaining_group_explicitly_retained": True}
            else:
                nodes, failure = make(15, group["centers"], group["faces"], constants,
                                      args.limit, route_weak=True)
            if nodes is None:
                outcome = {"group": group["id"], "status": "pending", **failure}
            else:
                assert group["id"] != known
                result = exact.verify(15, group["centers"], group["faces"], nodes, constants)
                assert result["minimum_force_margin"] is not None
                assert F(result["minimum_force_margin"]) > 0
                payload = {
                    "N": 23, "B": 15, "partial_centers": group["centers"], "faces": group["faces"],
                    "nodes": nodes, "groups_sha256": frozen[str(groupspath)],
                    "constants_sha256": frozen[str(constants_path)],
                    "radius_upper": constants["radius_upper"],
                }
                treepath = output / f"group-{group['id']:07}.json.gz"
                with gzip.open(treepath, "xt", encoding="utf8") as stream:
                    json.dump(payload, stream, separators=(",", ":"))
                outcome = {"group": group["id"], "status": "excluded", **result,
                           "members": group["members"], "tree_sha256": sha(treepath)}
                covered += group["members"]
            outcomes[group["id"]] = outcome
            totals[outcome["status"]] += 1
            ledger.write(json.dumps(outcome, separators=(",", ":"))+"\n")
            ledger.flush()
            if step % 10 == 0 or step == len(selected):
                print("N23 original residual outer proposals v2", step, "/", len(selected),
                      dict(totals), "seconds", round(time.monotonic()-started, 1), flush=True)
    for path, digest in frozen.items():
        assert sha(path) == digest
    receiptpath = output / "SUMMARY.json"
    publish(receiptpath, {
        "N": 23, "B": 15, "groups_sha256": frozen[str(groupspath)], "outcomes": outcomes,
        "excluded_groups": totals["excluded"], "pending_groups": len(outcomes)-totals["excluded"],
        "catalog_members_excluded": covered, "requested_groups_complete": True,
        "selected_original_group_count": len(selected), "known_attaining_group_control": known,
        "known_attaining_group_original_member_count": data["groups"][known]["members"],
        "all_unselected_original_groups_explicitly_pending": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "not_yet_fresh_residual_type_maps_or_payment_merge": True,
        "global_optimality_proved": False,
    })
    replayer = HIGH / "replay_group_stage.py"
    with (output / "REPLAY-STDOUT.log").open("xb") as stdout, \
            (output / "REPLAY-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen([
            sys.executable, "-u", str(replayer), "--groups", str(groupspath),
            "--receipt", str(receiptpath), "--output", str(output / "EXACT-REPLAY.json")],
            stdout=stdout, stderr=stderr, cwd=str(ROOT),
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "REPLAY-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid,
        "independent_process_terminal_observed": True, "source_sha256": sha(replayer),
    })
    assert code == 0
    print("N23 new residual outer trees independently replayed; type-payment merge still required",
          dict(totals), flush=True)


if __name__ == "__main__":
    main()
