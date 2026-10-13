"""Complete small native fibers, actual own-order families and refusal controls."""
from pathlib import Path
from copy import deepcopy
from collections import defaultdict
import argparse
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish
from stream_catalog import sha
from group_catalog import canonical
from small_order_filling_kernel import all_complete_codes, replay_payload, constants_gate
from general_collar_filling_linked import internal_links_possible
from small_order_collar_lower_pipeline import source_gate, rows
from test_outer_collar import WSL, linux_path

assert __debug__


def run(command, output, label):
    with (output / (label+"-STDOUT.log")).open("xb") as stdout, \
            (output / (label+"-STDERR.log")).open("xb") as stderr:
        process = subprocess.Popen(list(map(str, command)), stdout=stdout, stderr=stderr,
                                   cwd=str(ROOT),
                                   env=dict(os.environ, OPENBLAS_NUM_THREADS="1",
                                            OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
                                   creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / (label+"-TERMINAL.json"), {
        "actual_exit_code": code, "pid": process.pid,
        "actual_child_terminal_observed": True, "command": list(map(str, command))})
    assert code == 0, (label, (output / (label+"-STDERR.log")).read_text())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    output.mkdir()
    cases, frozen = [], {}
    degree = read(HIGH / "evidence/degree-pruning-regressions-resume1/VERIFIED.json")
    assert degree["verified"] and degree["source_sha256"] == sha(HIGH / "peel_degree.cpp")
    assert degree["binary_sha256"] == sha(HIGH / "peel_degree.exe")
    reference_binary = output / "FULL-REFERENCE-linux"
    sourcehash = sha(HIGH / "peel_degree.cpp")
    run([WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/g++",
         "-std=c++17", "-O2", linux_path(HIGH / "peel_degree.cpp"),
         "-o", linux_path(reference_binary)], output, "REFERENCE-BUILD")
    assert sha(HIGH / "peel_degree.cpp") == sourcehash
    frozen[str(reference_binary)] = sha(reference_binary)
    for N, B in ((5, 3), (6, 3), (6, 4), (7, 4), (7, 5), (8, 5), (8, 6), (9, 4)):
        nativepath = output / f"N{N}-B{B}-FULL.json"
        relative_native = nativepath.relative_to(ROOT).as_posix()
        assert relative_native.isascii()
        run([WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env",
             "-C", linux_path(ROOT), linux_path(reference_binary), N, B, relative_native,
             10000000, 804156, 1666328, 2698800, 0, "noscreen"],
            output, f"N{N}-B{B}-NATIVE")
        native = read(nativepath)
        assert native["complete"] and not native["screen"]
        assert (native["N"], native["B"]) == (N, B)
        fibers, centers = defaultdict(set), {}
        for full in native["survivors"]:
            code, mapping = canonical(N, B, full["faces"], 1)
            fibers[code].add(tuple(full["faces"]))
            assert code not in centers or centers[code] == len(mapping["centers"])
            centers[code] = len(mapping["centers"])
        calls, pinched = 0, 0
        for code, expected in fibers.items():
            actual, steps = all_complete_codes(N, B, centers[code], list(code))
            assert actual == expected, (N, B, code, len(actual), len(expected))
            calls += steps
            from complete_simple_collar import simple_holes
            try:
                simple_holes(centers[code], B, list(code))
            except AssertionError as error:
                assert str(error) == "pinched hole boundary"
                pinched += 1
        cases.append({
            "N": N, "B": B, "complete_full_reference_types": native["orbits"],
            "all_collar_fibers": len(fibers), "all_fibers_exactly_equal_to_complete_reference": True,
            "pinched_collar_fibers": pinched, "all_filling_states": calls,
            "reference_sha256": sha(nativepath)})
        frozen[str(nativepath)] = sha(nativepath)
        print("Small-order neutral topology complete native fibers", N, B,
              native["orbits"], "types", len(fibers), "fibers", "pinched", pinched, flush=True)
    # Real own N24 production identity, not a synthetic transplanted N25 case.
    stage = ROOT / "n24-B16-s1"
    record = source_gate(stage)
    iterator = rows(stage, record, True)
    first = next(iterator)
    iterator.close()
    real = output / "REAL-N24"
    real.mkdir()
    collarpath = real / "COLLAR.json"
    publish(collarpath, {"N": 24, "B": 16, "centers": first["centers"], "faces": first["faces"],
                        "actual_source_parent_index": first["id"],
                        "source_acceptance_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json")})
    proposalpath, exactpath = real / "PROPOSAL.json", real / "EXACT.json"
    run([sys.executable, "-u", ROOT / "propose_small_order_filling.py",
         "--collar", collarpath, "--output", proposalpath, "--limit", 10000, "--force-limit", 31],
        real, "PROPOSE")
    run([sys.executable, "-u", ROOT / "replay_small_order_filling.py",
         "--collar", collarpath, "--proposal", proposalpath, "--output", exactpath], real, "REPLAY")
    actual = read(exactpath)
    assert actual["verified"] and actual["whole_completion_family_strictly_closed"]
    constants = read(ROOT.parent / "evidence/core-reduction/constants/n24.json")
    payload = read(proposalpath)
    refuses = []
    def reject(name, fn):
        try:
            fn()
        except (AssertionError, KeyError, ValueError, IndexError, TypeError):
            refuses.append(name)
        else:
            raise AssertionError("incorrect own-order input accepted: "+name)
    for field, value in (
        ("schema", "proof-paid-linked-general-collar-branch-tree-v1"),
        ("N", 25), ("cap8", 4058615), ("radius_upper", "1/4")):
        bad = deepcopy(payload)
        bad[field] = value
        reject("payload-"+field, lambda bad=bad: replay_payload(bad, constants))
    bad_constants = deepcopy(constants)
    bad_constants["radius_upper"] = "239146311738101/1000000000000000"
    reject("N25-radius-in-N24", lambda: replay_payload(payload, bad_constants))
    reject("N23-constants-in-N24", lambda: constants_gate(
        read(ROOT.parent / "evidence/core-reduction/constants/n23.json"), 24, 16))
    bad = deepcopy(payload)
    bad["nodes"].append(deepcopy(bad["nodes"][0]))
    reject("unreachable-extra-node", lambda: replay_payload(bad, constants))
    bad = deepcopy(payload)
    bad["nodes"][0]["state"]["next"] += 1
    reject("wrong-source-state", lambda: replay_payload(bad, constants))
    bad = deepcopy(payload)
    bad["roots"].append(0)
    reject("duplicate-root", lambda: replay_payload(bad, constants))
    bad = deepcopy(payload)
    bad["nodes"][0] = {
        "state": bad["nodes"][0]["state"], "kind": "FORCE",
        "force_nodes": [], "exact_result": {"verified": True}}
    reject("missing-force-proof-not-a-payment", lambda: replay_payload(bad, constants))
    # Pick a genuinely nonempty actual fiber with topology children; disabling
    # force only exposes its branches and must never give strict closure.
    from propose_small_order_filling import propose
    branching = None
    iterator = rows(stage, record)
    for number, row in enumerate(iterator):
        from small_order_filling_kernel import start_states, children
        following = children(start_states(24, 16, row["centers"], row["faces"])[0], 24, 16)
        if following and all_complete_codes(24, 16, row["centers"], row["faces"])[0]:
            branching = {"N": 24, "B": 16, "centers": row["centers"], "faces": row["faces"]}
            break
        assert number < 1000, "no actual branching production control located"
    iterator.close()
    assert branching is not None
    controltree = propose(branching, constants, 100000, 1, force_enabled=False)
    control_result = replay_payload(controltree, constants)
    assert control_result["pending_complete_leaves"] > 0
    assert not control_result["whole_completion_family_strictly_closed"]
    publish(output / "ACTUAL-BRANCH-NO-FORCE.json", controltree)
    bad = deepcopy(controltree)
    next(node for node in bad["nodes"] if node["kind"] == "SPLIT")["children"].pop()
    reject("deleted-actual-topology-child", lambda: replay_payload(bad, constants))
    bad = deepcopy(controltree)
    next(node for node in bad["nodes"] if node["kind"] == "FULL_PENDING")["kind"] = "DEAD"
    reject("pending-full-cannot-be-dead", lambda: replay_payload(bad, constants))
    limited = propose(branching, constants, 1, 1, force_enabled=False)
    limited_result = replay_payload(limited, constants)
    assert limited_result["unsearched_frontier_nodes"] > 0
    assert not limited_result["whole_completion_family_strictly_closed"]
    refuses.append("proposal-node-limit-left-unpaid")
    branch = [(1 << 16) | (1 << 17) | (1 << v) for v in (18, 19, 20)]
    assert not internal_links_possible(sorted(branch), [16])
    refuses.append("internal-link-degree-three")
    closed = [(1 << 16) | (1 << 17) | (1 << 18),
              (1 << 16) | (1 << 18) | (1 << 19),
              (1 << 16) | (1 << 19) | (1 << 17),
              (1 << 16) | (1 << 20) | (1 << 21)]
    assert not internal_links_possible(sorted(closed), [16])
    refuses.append("closed-link-component-plus-another-component")
    for path in (
        Path(__file__), ROOT / "small_order_filling_kernel.py",
        ROOT / "propose_small_order_filling.py", ROOT / "replay_small_order_filling.py",
        ROOT / "SMALL-ORDER-COMPLETE-FILLING-SOURCE-v1.md",
        ROOT / "general_collar_filling.py", ROOT / "general_collar_filling_linked.py",
        ROOT / "complete_simple_collar.py", ROOT / "small_order_origin_caps.py",
        ROOT / "eight_rod_angles.py", HIGH / "cross_order_strict_transfer.py",
        HIGH / "group_catalog.py", HIGH / "peel_degree.cpp", HIGH / "peel_degree.exe",
        HIGH / "exact_graph.py", HIGH.parent / "round2-grouped/partial_force_exact.py",
        collarpath, proposalpath, exactpath, output / "ACTUAL-BRANCH-NO-FORCE.json"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "small-order-own-full-filling-controls-v1",
        "complete_small_native_fiber_cases": cases,
        "fresh_isolated_reference_compiled_from_unchanged_original_full_source": True,
        "native_reference_source_sha256": sourcehash,
        "native_reference_binary_sha256": sha(reference_binary),
        "all_no_payment_full_sets_equal_to_complete_native_references": True,
        "real_own_order_strict_family_separate_process_replayed": True,
        "real_nonempty_branch_fiber_not_paid_without_force": True,
        "proposal_limits_never_mistaken_for_completion": True,
        "negative_controls_rejected": refuses, "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "kernel_sha256": sha(ROOT / "small_order_filling_kernel.py"),
        "proposal_source_sha256": sha(ROOT / "propose_small_order_filling.py"),
        "replay_source_sha256": sha(ROOT / "replay_small_order_filling.py"),
        "not_complete_production_boundary_family_payment": True,
        "global_optimality_proved": False})
    print("Own-order completion controls accepted:", len(cases), "full-set cases,",
          len(refuses), "refusals; not full production family payment", flush=True)


if __name__ == "__main__":
    main()
