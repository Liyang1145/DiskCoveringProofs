"""Stronger proposals only on ended N23 stage's still-unpaid selected groups."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from group_catalog import canonical
from probe_collar_batches import make
import exact_graph as exact

assert __debug__


def remaining_ids(outcomes, selected, known):
    assert type(known) is int
    assert [row["group"] for row in outcomes] == list(range(len(outcomes)))
    assert selected == sorted(set(selected))
    assert all(type(gid) is int and 0 <= gid < len(outcomes) for gid in selected)
    assert known in selected and outcomes[known]["status"] == "pending"
    assert all(outcomes[gid]["status"] in ("excluded", "pending") for gid in selected)
    return [gid for gid in selected if outcomes[gid]["status"] == "pending"]


def main():
    ap = argparse.ArgumentParser()
    for name in ("previous-stage", "groups", "core", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--limit", type=int, default=127)
    args = ap.parse_args()
    previous, groupspath, corepath, controlpath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("previous-stage", "groups", "core", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (previous, groupspath, corepath, controlpath, output))
    assert not output.exists() and 31 < args.limit <= 1001
    controls = read(controlpath)
    assert controls["verified"] and controls["schema"] == "N23-stronger-pending-group-selection-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_stronger_pending_selection.py")
    assert controls["proposal_source_sha256"] == sha(Path(__file__))
    receiptpath, replaypath, inputpath, terminalpath = (
        previous / name for name in ("SUMMARY.json", "EXACT-REPLAY.json", "INPUT-SNAPSHOT.json", "REPLAY-TERMINAL.json"))
    old, replay, inputs, terminal, data, core = map(
        read, (receiptpath, replaypath, inputpath, terminalpath, groupspath, corepath))
    assert old["source_sha256"] == sha(ROOT / "probe_n23_remaining_outer_v2.py")
    assert old["requested_groups_complete"] and old["selected_original_group_count"] == 6879
    assert replay["verified"] and replay["receipt_sha256"] == sha(receiptpath)
    assert replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert replay["exact_groups_replayed"] == old["excluded_groups"] == 6772
    assert terminal["independent_process_terminal_observed"] and terminal["actual_exit_code"] == 0
    assert terminal["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    digest = sha(groupspath)
    assert old["groups_sha256"] == replay["groups_sha256"] == digest
    assert (data["N"], data["B"], data["threshold"], data["group_count"]) == (23, 15, 1, 535262)
    assert [g["id"] for g in data["groups"]] == list(range(535262))
    bindingspath = groupspath.parent / data["bindings_file"]
    assert sha(bindingspath) == data["bindings_sha256"] == replay["bindings_sha256"]
    for path, expected in old["frozen_files"].items():
        assert sha(path) == expected
    assert old["frozen_files"][str(corepath)] == sha(corepath)
    assert (core["N"], core["B"]) == (23, 15)
    code, mapping = canonical(23, 15, sorted(sum(1 << v for v in face) for face in core["all_faces"]), 1)
    known = inputs["known_attaining_original_group"]
    assert known == old["known_attaining_group_control"] == 522460
    assert tuple(data["groups"][known]["faces"]) == code and len(mapping["centers"]) == 22
    selected = remaining_ids(old["outcomes"], sorted(inputs["selected_original_groups"]), known)
    assert len(selected) == 107
    assert sum(data["groups"][gid]["members"] for gid in selected) == 33861
    assert data["groups"][known]["members"] == 169
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constantspath)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    frozenpaths = (
        Path(__file__), receiptpath, replaypath, inputpath, terminalpath,
        groupspath, bindingspath, corepath, controlpath, constantspath,
        ROOT / "probe_collar_batches.py", HIGH / "exact_graph.py", HIGH / "candidate_domain.py",
        HIGH / "group_catalog.py", HIGH / "replay_group_stage.py",
    )
    frozen = {str(path): sha(path) for path in frozenpaths}
    output.mkdir()
    publish(output / "INPUT-SNAPSHOT.json", {
        "schema": "N23-original-pending-group-stronger-proposal-input-v1",
        "N": 23, "B": 15, "selected_original_groups": selected,
        "selected_group_count": len(selected), "associated_original_group_members": 33861,
        "known_attaining_original_group": known, "known_attaining_members": 169,
        "previous_6772_positive_groups_not_reproposed": True,
        "force_node_limit": args.limit, "frozen_files": frozen,
        "original_residual_type_payment_merge_still_required": True, "global_optimality_proved": False,
    })
    outcomes = [{"group": gid, "status": "pending", "not_selected_by_this_stronger_stage": True}
                for gid in range(535262)]
    totals, members = Counter(), 0
    started = time.monotonic()
    with (output / "outcomes.jsonl").open("x", encoding="ascii") as ledger:
        for step, gid in enumerate(selected, 1):
            group = data["groups"][gid]
            assert group["centers"] < 23 and old["outcomes"][gid]["status"] == "pending"
            if gid == known:
                nodes, failure = None, {"known_exact_attaining_group_explicitly_retained": True}
            else:
                nodes, failure = make(15, group["centers"], group["faces"], constants, args.limit, route_weak=True)
            if nodes is None:
                row = {"group": gid, "status": "pending", **failure}
            else:
                assert gid != known
                result = exact.verify(15, group["centers"], group["faces"], nodes, constants)
                assert result["minimum_force_margin"] is not None and F(result["minimum_force_margin"]) > 0
                treepath = output / f"group-{gid:07}.json.gz"
                with gzip.open(treepath, "xt", encoding="utf8") as stream:
                    json.dump({
                        "N": 23, "B": 15, "partial_centers": group["centers"], "faces": group["faces"],
                        "nodes": nodes, "groups_sha256": digest, "constants_sha256": sha(constantspath),
                        "radius_upper": constants["radius_upper"],
                    }, stream, separators=(",", ":"))
                row = {"group": gid, "status": "excluded", **result,
                       "members": group["members"], "tree_sha256": sha(treepath)}
                members += group["members"]
            outcomes[gid] = row
            totals[row["status"]] += 1
            ledger.write(json.dumps(row, separators=(",", ":"))+"\n")
            ledger.flush()
            if step % 10 == 0 or step == len(selected):
                print("N23 stronger original pending groups", step, "/", len(selected),
                      dict(totals), "seconds", round(time.monotonic()-started, 1), flush=True)
    for path, expected in frozen.items():
        assert sha(path) == expected
    newreceipt = output / "SUMMARY.json"
    publish(newreceipt, {
        "N": 23, "B": 15, "groups_sha256": digest, "outcomes": outcomes,
        "excluded_groups": totals["excluded"], "pending_groups": 535262-totals["excluded"],
        "catalog_members_excluded": members, "requested_groups_complete": True,
        "selected_original_group_count": len(selected), "known_attaining_group_control": known,
        "previous_positive_groups_not_reproposed": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "all_source_residual_maps_and_disjoint_payment_still_required": True, "global_optimality_proved": False,
    })
    replayer = HIGH / "replay_group_stage.py"
    with (output / "REPLAY-STDOUT.log").open("xb") as stdout, \
            (output / "REPLAY-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen([
            sys.executable, "-u", str(replayer), "--groups", str(groupspath),
            "--receipt", str(newreceipt), "--output", str(output / "EXACT-REPLAY.json")],
            stdout=stdout, stderr=stderr, cwd=str(ROOT),
            env=dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "REPLAY-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid,
        "independent_process_terminal_observed": True, "source_sha256": sha(replayer),
    })
    assert code == 0
    print("N23 stronger pending-group trees independently replayed:", dict(totals),
          "; actual residual type payment not merged here", flush=True)


if __name__ == "__main__":
    main()
