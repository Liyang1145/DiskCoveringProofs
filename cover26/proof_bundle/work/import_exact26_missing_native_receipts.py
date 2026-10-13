"""Fresh explicit closure of missing native bytes and original partitions.

Reuses old strict force/area mathematics QUALIFIED, never reruns enumeration.
"""

import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import check_frontier, linux
import audit_exact26_native_dependency_closure as closure
import inventory_exact26_native_dispatch_interfaces as census
import n26_force as force
import verify_conditional_force_stage as binding
import verify_force_stage as dispatch


SCHEMA = "N26-qualified-prior-native-byte-and-partition-closure-import-v1"
STAGES = tuple("n26-force-stage-v"+str(i) for i in range(3, 9))
KINDS = ("split", "force", "force_tree", "area", "empty", "terminal")


def load(path, expected, files):
    path = binding.local_path(path)
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != expected:
        raise ValueError("actual prior native source byte changed: "+str(path))
    text = linux(path)
    if text in files and files[text] != digest:
        raise ValueError("prior native import has conflicting actual-byte bindings")
    files[text] = digest
    return json.loads(raw)


def native_event_gate(folder, event, run, launch, data, refs):
    b, prefix, kind = event["B"], tuple(event["prefix"]), event["kind"]
    if b not in refs or kind not in KINDS:
        raise ValueError("unknown native event family/payment mechanism")
    index, depth = run["event_index"], int(kind == "split")
    if (
        run["result"] != f"native-{index:05d}.json"
        or run["launch"] != f"native-{index:05d}-launch.json"
        or launch["event_index"] != index or launch["B"] != b
        or launch["prefix"] != list(prefix) or launch["depth"] != depth
        or launch["exit_code"] != 0 or data["origin_screen"] is not True
    ):
        raise ValueError("prior native result/launch source ownership or strict origin scope differs")
    tail = ["26", str(b), linux(folder/run["result"]), str(force.D), *map(str, force.CAPS),
            "0", "dfs", "frontier", ",".join(map(str, prefix)) if prefix else "-", str(depth), "1"]
    command = launch["command"]
    if (
        command[-14:] != tail
        or command[-16:-14] != ["/lib64/ld-linux-x86-64.so.2", linux(folder/"peel_prefix_origin.linux")]
        or command[:-16] not in ([], ["wsl.exe", "--"])
    ):
        raise ValueError("actual native launch changed exact executable, output or necessary-domain arguments")
    return check_frontier(data, refs[b], prefix, depth)


def old_payment_gate(event, paid):
    kind = event["kind"]
    if (paid["B"], paid["prefix"], paid["kind"]) != (event["B"], event["prefix"], kind):
        raise ValueError("qualified prior strict payment belongs to another actual source")
    if kind == "force":
        if F(paid["strict_margin_above_U"]) <= 0 or F(paid["required_radius_lower"]) <= force.U:
            raise ValueError("qualified prior force payment is not strict")
    elif kind == "force_tree":
        if paid["all_incoming_angular_boxes_covered"] is not True or F(paid["minimum_strict_force_margin"]) <= 0:
            raise ValueError("qualified prior angular payment is incomplete or nonstrict")
    elif kind == "area":
        if F(paid["area_dual_upper"]) >= 0:
            raise ValueError("qualified prior area payment is not strict")
    else:
        raise ValueError("a non-geometric event was counted as old mathematical payment")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    current_path = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
    final_path = Path("outputs/n26-current28-six-target-supplemental-independent-final-v1.json")
    closure_path = Path("outputs/n26-exact26-native-receipt-current-dependency-closure-v1.json")
    census_path = Path("outputs/n26-exact26-native-dispatch-actual-current-inventory-v1.json")
    files = {}
    current = load(current_path, census.CURRENT_SHA, files)
    final = load(final_path, census.FINAL_SHA, files)
    problem = load(closure_path, binding.sha(closure_path), files)
    inventory = load(census_path, binding.sha(census_path), files)
    if (
        final["current_audit_sha256"] != census.CURRENT_SHA
        or problem["actual_current_sha256"] != census.CURRENT_SHA
        or problem["missing_explicit_native_dependency_current_bindings"] != 28800
        or problem["unequal_explicit_native_dependency_current_bindings"] != 0
        or current["global_optimality_proved"] is not False
        or current["candidate_angle_unresolved_closed_boxes"] != 25
        or current["Rstar_conditional_frontier_pending_subtrees"] != 5637
    ):
        raise ValueError("qualified prior native import changed actual missing-binding/source scope")
    actual = {closure.key(path): digest for path, digest in current["files"].items()}
    missing = {closure.key(row["path"]): row for row in problem["missing_bindings"]}
    if len(missing) != 28800:
        raise ValueError("actual native missing-path ownership duplicated/truncated")
    # Independently derive the missing set from all38bound native receipts.
    derived = {}
    for row in inventory["native_receipts"]:
        path = binding.local_path(row["native_acceptance_path"])
        receipt = load(path, actual[closure.key(path)], files)
        for name, digest in receipt["files"].items():
            target = path.parent/name
            normalized = closure.key(target)
            if normalized not in actual:
                item = {"path": linux(target), "expected_sha256": digest,
                        "native_receipt": linux(path)}
                if normalized in derived and derived[normalized] != item:
                    raise ValueError("native receipts disagree on an omitted dependency")
                derived[normalized] = item
            elif actual[normalized] != digest:
                raise ValueError("native receipt disagrees with an existing current dependency")
    if derived != missing:
        raise ValueError("qualified native import does not match the entire actual omitted dependency set")
    refs = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
            for b in (14, 15, 16, 17)}
    for ref in refs.values():
        ref.children = lru_cache(maxsize=32768)(ref.children)
    reports, all_counts, covered, fixture, rejected = [], Counter(), set(), None, []
    for stage_name in STAGES:
        folder = (Path("outputs")/stage_name).resolve()
        inputs = {}
        for name in ("NATIVE-VERIFIED.json", "TRACE.json", "MANIFEST.json", "VERIFIED.json",
                     "SOURCE-FRONTIER.json", "LOWER-LEDGER.json", "FRONTIER.json"):
            path = folder/name
            inputs[name] = load(path, actual[closure.key(path)], files)
        receipt, trace, accepted = (inputs[name] for name in ("NATIVE-VERIFIED.json", "TRACE.json", "VERIFIED.json"))
        source, old_ledger, frontier = (inputs[name] for name in ("SOURCE-FRONTIER.json", "LOWER-LEDGER.json", "FRONTIER.json"))
        publication = (Path("outputs")/("n26-force-stage-published-replay-v"+stage_name.rsplit("v", 1)[1]+".json")).resolve()
        if load(publication, actual[closure.key(publication)], files) != accepted:
            raise ValueError("qualified prior stage acceptance lacks its actual identical publication")
        if (
            accepted["verified"] is not True or accepted["global_optimality_proved"] is not False
            or accepted["schema"] != "N26-successive-force-angular-stage-acceptance-v1"
            or receipt["native_events_checked"] != 2400 or len(trace["events"]) != 2400
            or len(receipt["runs"]) != 2400
            or inputs["MANIFEST.json"]["kernel_source_sha256"] != dispatch.KERNEL_SOURCE
            or inputs["MANIFEST.json"]["kernel_binary_sha256"] != dispatch.KERNEL_BINARY
        ):
            raise ValueError("qualified prior native stage lacks actual accepted original scope")
        for name in ("peel_prefix_origin.cpp", "peel_prefix_origin.linux",
                     "verify_force_stage.py", "audit_prefix_origin.py", "audit_prefix_partition.py"):
            selected = folder/name
            digest = binding.sha(selected)
            if actual.get(closure.key(selected)) != digest:
                raise ValueError("qualified native original source/kernel implementation changed")
            files[linux(selected)] = digest
        pending = {b: {} for b in refs}
        terminal = {b: set() for b in refs}
        counts = {b: Counter() for b in refs}
        source_keys = set()
        for row in source["pending_states"]:
            b, prefix = row["B"], tuple(row["prefix"])
            state = refs[b].resolve(prefix)
            if {"B": b, **refs[b].entry(prefix, state, refs[b].children(state))} != row:
                raise ValueError("original incoming stage source did not independently reconstruct")
            if (b, prefix) in source_keys:
                raise ValueError("duplicated incoming prior source")
            source_keys.add((b, prefix))
            pending[b][prefix] = state
        if any((b, p[:i]) in source_keys for b, p in source_keys for i in range(len(p))):
            raise ValueError("incoming prior source overlaps ancestor and descendant")
        payments = {(row["B"], tuple(row["prefix"]), row["kind"]): row for row in old_ledger}
        if len(payments) != len(old_ledger):
            raise ValueError("qualified prior strict ledger repeats source ownership")
        reused = set()
        for index, (event, run) in enumerate(zip(trace["events"], receipt["runs"])):
            b, prefix, kind = event["B"], tuple(event["prefix"]), event["kind"]
            if run["event_index"] != index or prefix not in pending[b] or prefix in terminal[b]:
                raise ValueError("actual native event is outside the complete current prior partition")
            loaded = []
            for field, digest_field in (("result", "result_sha256"), ("launch", "launch_sha256")):
                target = folder/run[field]
                normalized = closure.key(target)
                if normalized not in missing or missing[normalized]["expected_sha256"] != run[digest_field]:
                    raise ValueError("new byte closure imported an already-bound or unowned path")
                loaded.append(load(target, run[digest_field], files))
                covered.add(normalized)
            data, launch = loaded
            native_event_gate(folder, event, run, launch, data, refs)
            if fixture is None:
                fixture = (folder, event, run, launch, data)
            state = pending[b][prefix]
            children = refs[b].children(state)
            if kind == "split":
                if not children or event["all_child_count"] != len(children):
                    raise ValueError("actual old split lost a necessary immediate sibling")
                pending[b].pop(prefix)
                for child_index, child in enumerate(children):
                    target = prefix+(child_index,)
                    if target in pending[b]:
                        raise ValueError("old split created overlapping child ownership")
                    pending[b][target] = refs[b].normalize(child)
            elif kind == "empty":
                if not state.pending or children:
                    raise ValueError("actual old empty event deletes a terminal/nonempty subtree")
                pending[b].pop(prefix)
            elif kind == "terminal":
                if state.pending or state.next_vertex != 26:
                    raise ValueError("actual prior terminal is not complete")
                terminal[b].add(prefix)
            elif kind in ("force", "force_tree", "area"):
                payment_key = b, prefix, kind
                if payment_key not in payments or payment_key in reused:
                    raise ValueError("actual prior geometric deletion lacks its unique accepted ledger row")
                old_payment_gate(event, payments[payment_key])
                reused.add(payment_key)
                pending[b].pop(prefix)
            else:
                raise ValueError("uninspected actual historical payment dispatch")
            counts[b][kind] += 1
            if (index+1) % 200 == 0:
                print(json.dumps({"actual_prior_native_stage": stage_name,
                                  "events_independently_reconstructed": index+1,
                                  "missing_original_bytes_freshly_admitted": len(covered),
                                  "new_geometric_payments": 0}), flush=True)
        if reused != set(payments):
            raise ValueError("prior native trace omitted an actual strict ledger row")
        expected_rows = []
        for b in refs:
            if (
                trace["pending_prefixes"][str(b)] != [list(p) for p in sorted(pending[b])]
                or trace["terminal_pending_prefixes"][str(b)] != [list(p) for p in sorted(terminal[b])]
            ):
                raise ValueError("actual entire native trace lost an unpaid sibling or raw terminal")
            expected_rows.extend({"B": b, **refs[b].entry(p, state, refs[b].children(state))}
                                 for p, state in sorted(pending[b].items()))
            family = next(row for row in frontier["families"] if row["B"] == b)
            if (
                any(family[kind] != counts[b][kind] for kind in KINDS)
                or family["pending_subtrees"] != len(pending[b])
                or family["unresolved_terminal_subtrees"] != len(terminal[b])
                or family["family_exhausted"] != (not pending[b])
            ):
                raise ValueError("actual old family counters/terminal conservation differ")
        if expected_rows != frontier["pending_states"] or frontier["families"] != accepted["families"]:
            raise ValueError("actual prior final frontier did not fully reconstruct")
        stage_counts = Counter({kind: sum(counts[b][kind] for b in refs) for kind in KINDS})
        if dict(stage_counts) != accepted["event_counts"]:
            raise ValueError("qualified prior actual acceptance event counts differ")
        all_counts.update(stage_counts)
        reports.append({"stage": stage_name, "actual_events_independently_reconstructed": 2400,
                        "actual_missing_original_bytes_freshly_admitted": 4800,
                        "actual_prior_strict_ledger_rows_qualified_reused": len(reused),
                        "exact_event_counts": dict(stage_counts),
                        "retained_pending_subtrees": len(expected_rows),
                        "all_old_force_area_math_QUALIFIED_reused_NOT_a_new_leaf_replay": True})
    if covered != set(missing) or sum(all_counts.values()) != 14400:
        raise ValueError("new native closure did not cover exactly the actual missing28800original paths")
    folder, event, run, launch, data = fixture
    def reject(name, action):
        try:
            action()
        except (ValueError, KeyError, IndexError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError("invalid native closure control accepted: "+name)
    for name, field, value in (
        ("wrong-N", "N", 25), ("wrong-cap", "caps", [1, 2, 3, 4]),
        ("origin-disabled", "origin_screen", False), ("family-promotion", "family_complete", True),
        ("global-promotion", "global_optimality_proved", True),
    ):
        wrong = deepcopy(data)
        wrong[field] = value
        reject(name, lambda wrong=wrong: native_event_gate(folder, event, run, launch, wrong, refs))
    for name, change in (
        ("lost-native-sibling", lambda obj: obj["frontier"].pop()),
        ("duplicate-native-sibling", lambda obj: obj["frontier"].append(obj["frontier"][0])),
    ):
        wrong = deepcopy(data)
        change(wrong)
        reject(name, lambda wrong=wrong: native_event_gate(folder, event, run, launch, wrong, refs))
    for name, changed in (
        ("launch-failed", {"exit_code": 1}),
        ("launch-wrong-depth", {"depth": 99}),
        ("launch-wrong-owner", {"B": 25}),
    ):
        wrong = {**launch, **changed}
        reject(name, lambda wrong=wrong: native_event_gate(folder, event, run, wrong, data, refs))
    wrong = deepcopy(launch)
    wrong["command"][-1] = "0"
    reject("launch-origin-flag-disabled",
           lambda: native_event_gate(folder, event, run, wrong, data, refs))
    reject("wrong-original-byte-digest",
           lambda: load(folder/run["result"], "0"*64, {}))
    if len(rejected) != 12:
        raise ValueError("actual native-byte/partition negative controls incomplete")
    for module in (Path(__file__), Path(closure.__file__), Path(census.__file__), Path(force.__file__),
                   Path(dispatch.__file__), Path("work/audit_prefix_origin.py"),
                   Path("work/audit_prefix_partition.py"),
                   Path("work/recheck_exact26_missing_native_import.py"),
                   Path("work/run_exact26_missing_native_byte_closure_v1.ps1"),
                   Path("work/n26-prior-native-byte-closure-admission-proof.md"),
                   Path("work/n26-exact26-core-native-source-interface-proof.md")):
        files[linux(module)] = binding.sha(module)
    for path, digest in files.items():
        if binding.sha(path) != digest:
            raise ValueError("admitted prior native original changed before publication")
    report = {
        "schema": SCHEMA, "verified": True,
        "actual_proof_time_SIX_current_sha256": census.CURRENT_SHA,
        "actual_proof_time_SIX_final_sha256": census.FINAL_SHA,
        "all_actual_missing_prior_native_bytes_freshly_content_rehashed": 28800,
        "all_actual_selected_original_native_events_independently_reconstructed": 14400,
        "all_actual_original_stage_partitions_siblings_AND_raw_terminals_reconstructed": True,
        "all_missing_paths_independently_derived_from_entire38_native_receipts": True,
        "actual_prior_stages": reports, "actual_event_counts": dict(all_counts),
        "actual_invalid_native_byte_launch_AND_partition_controls_rejected": rejected,
        "old_force_area_math_QUALIFIED_reused_NOT_new_entire_geometry_or_force_tree_replay": True,
        "no_compilation_native_execution_or_historical_receipt_replacement": True,
        "all_actual_admitted_input_sha256": files,
        "new_formal_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "actual_original_U_frontier_unchanged": 3922, "actual_original_LOCAL_unchanged": "7/800000",
        "not_a_latest_current_or_unrestricted_joint_source_acceptance": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "separate_independent_final_AND_future_actual_latest_current_join_STILL_required": True,
        "executed_import_checker_sha256": binding.sha(__file__),
    }
    args.output.mkdir(parents=True)
    with (args.output/"VERIFIED.json").open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("all_actual_admitted_input_sha256", "actual_prior_stages")}), flush=True)


if __name__ == "__main__":
    main()
