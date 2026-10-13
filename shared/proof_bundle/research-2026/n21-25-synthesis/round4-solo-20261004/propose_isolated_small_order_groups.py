"""Small-order exact force proposals with explicit, isolated candidate inputs."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
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
from group_catalog import canonical, canonical_full
from probe_collar_batches import make
import exact_graph as exact

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("groups", "core", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--limit", type=int, default=31)
    args = ap.parse_args()
    groupspath, corepath, output = args.groups.resolve(), args.core.resolve(), args.output.resolve()
    assert all(path.is_relative_to(ROOT) for path in (groupspath, corepath, output))
    assert not output.exists() and 1 <= args.limit <= 10001
    data, core = read(groupspath), read(corepath)
    N, B = data["N"], data["B"]
    assert N in (23, 24) and core["N"] == N
    assert data["verified_embeddings_during_generation"] and data["full_selected_catalog_scanned"]
    assert [group["id"] for group in data["groups"]] == list(range(data["group_count"]))
    assert sum(group["members"] for group in data["groups"]) == data["selected_types"]
    bindingspath = (groupspath.parent / data["bindings_file"]).resolve()
    assert bindingspath.is_relative_to(ROOT) and sha(bindingspath) == data["bindings_sha256"]
    digest = sha(groupspath)
    constantspath = HIGH.parent / f"evidence/core-reduction/constants/n{N}.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    assert constants["verified"] and constants["N"] == N
    assert 0 < F(constants["radius_upper"]) < F(1, 4)
    known = None
    if B == core["B"]:
        masks = sorted(sum(1 << v for v in face) for face in core["all_faces"])
        code = (canonical_full(N, B, masks) if data["threshold"] == 0
                else canonical(N, B, masks, data["threshold"])[0])
        matches = [group["id"] for group in data["groups"] if tuple(group["faces"]) == code]
        assert len(matches) <= 1
        known = matches[0] if matches else None
    frozen = {str(path): sha(path) for path in (
        Path(__file__), groupspath, bindingspath, corepath, constantspath,
        ROOT / "probe_collar_batches.py", HIGH / "candidate_domain.py",
        HIGH / "exact_graph.py", HIGH / "group_catalog.py", HIGH / "replay_group_stage.py")}
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": N, "B": B, "groups_sha256": digest, "explicit_core_path": str(corepath),
        "known_attaining_group": known, "force_limit": args.limit,
        "missing_legacy_core_defaults_not_created_or_used": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    outcomes, counts, members, started = [], Counter(), 0, time.monotonic()
    for group in data["groups"]:
        gid = group["id"]
        assert B <= group["centers"] <= N
        if gid == known:
            nodes, failure = None, {"known_attaining_outer_explicitly_retained": True}
        else:
            nodes, failure = make(B, group["centers"], group["faces"], constants, args.limit,
                                  route_weak=True)
        if nodes is None:
            outcome = {"group": gid, "status": "pending", **failure}
        else:
            result = exact.verify(B, group["centers"], group["faces"], nodes, constants)
            assert F(result["minimum_force_margin"]) > 0
            treepath = output / f"group-{gid:07}.json.gz"
            with gzip.open(treepath, "xt", encoding="utf8") as tree:
                json.dump({
                    "N": N, "B": B, "partial_centers": group["centers"],
                    "faces": group["faces"], "nodes": nodes, "groups_sha256": digest,
                    "constants_sha256": constantshash, "radius_upper": constants["radius_upper"],
                }, tree, separators=(",", ":"))
            outcome = {"group": gid, "status": "excluded", "members": group["members"],
                       "tree_sha256": sha(treepath), **result}
            members += group["members"]
        outcomes.append(outcome)
        counts[outcome["status"]] += 1
        if len(outcomes) % 25 == 0 or len(outcomes) == data["group_count"]:
            print("Isolated small-order group proposals", N, B, len(outcomes),
                  "/", data["group_count"], dict(counts), "seconds",
                  round(time.monotonic()-started, 1), flush=True)
    for path, expected in frozen.items():
        assert sha(path) == expected
    receiptpath = output / "SUMMARY.json"
    publish(receiptpath, {
        "N": N, "B": B, "groups_sha256": digest, "outcomes": outcomes,
        "excluded_groups": counts["excluded"], "pending_groups": counts["pending"],
        "catalog_members_excluded": members, "requested_groups_complete": True,
        "known_attaining_group_control": known, "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "actual_source_selection_maps_and_disjoint_type_payment_still_required": True,
        "global_optimality_proved": False,
    })
    replayer = HIGH / "replay_group_stage.py"
    with (output / "REPLAY-STDOUT.log").open("xb") as stdout, \
            (output / "REPLAY-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen([
            sys.executable, "-u", str(replayer), "--groups", str(groupspath),
            "--receipt", str(receiptpath), "--output", str(output / "EXACT-REPLAY.json")],
            stdout=stdout, stderr=stderr, cwd=str(ROOT),
            env=dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "REPLAY-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid,
        "independent_process_terminal_observed": True, "source_sha256": sha(replayer),
    })
    assert code == 0
    print("Isolated small-order group trees independently replayed:", dict(counts),
          "; actual complete-source payment not merged here", flush=True)


if __name__ == "__main__":
    main()
