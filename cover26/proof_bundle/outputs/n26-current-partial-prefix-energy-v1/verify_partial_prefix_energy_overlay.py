"""Standalone exact energy exclusions for actual nonterminal source prefixes."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_origin import OriginReference
from audit_prefix_partition import check_frontier, linux, native_command
import n26_partial_prefix_quadratic_kernel as partial
import n26_quadratic_energy_minorant as quadratic
import n26_sharp_partial_domains as independent
import n26_sharp_radius_constraints as constraints
import verify_conditional_force_stage as stage


read, sha, local_path = stage.read, stage.sha, stage.local_path
SCHEMA = "N26-current-partial-prefix-energy-overlay-bindings-v1"


def strict_gate(result):
    if (not result["radius_at_most_Rstar_partial_whole_box_excluded"]
            or F(result["minimum_strict_energy_margin"]) <= 0
            or F(result["minimum_strict_radius_margin"]) <= 0):
        raise ValueError("partial energy whole-root payment is not strictly proved")


def input_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != SCHEMA or manifest["radius_scope"] != stage.SCOPE:
        raise ValueError("partial energy source scope changed")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("partial energy sealed file changed: " + name)
    parent_path = local_path(manifest["parent_current_audit"])
    parent = read(parent_path)
    if (sha(parent_path) != manifest["parent_current_audit_sha256"]
            or not parent["current_bound_bytes_rechecked"]
            or parent["radius_scope"] != stage.SCOPE or parent["global_optimality_proved"] is not False
            or read(folder / "SOURCE-CURRENT-AUDIT.json") != parent):
        raise ValueError("partial source is not an honest actual current audit")
    for text, digest in parent["files"].items():
        if sha(text) != digest:
            raise ValueError("partial energy current dependency changed: " + text)
    source_folder = local_path(manifest["source_stage"])
    accepted, inventory = stage.bound(source_folder)
    replay_path = local_path(manifest["source_published_replay"])
    if (read(replay_path) != accepted or read(folder / "SOURCE-ACCEPTANCE.json") != accepted
            or parent["files"].get(linux(source_folder / "VERIFIED.json")) != sha(
                source_folder / "VERIFIED.json")
            or parent["files"].get(linux(replay_path)) != sha(replay_path)
            or sha(source_folder / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or sha(stage.__file__) != accepted["files"]["verify_conditional_force_stage.py"]):
        raise ValueError("partial energy substituted its actual current stage or published replay")
    values = stage.input_gate(source_folder, source_folder.parent / "n26-multislope-area-lower-v1")
    source_manifest, incoming, _, basis, old, multi, native, trace, paths = values
    radius = F(accepted["radius_upper"])
    arcs = stage.force.load_trig(folder)[0]
    source, ledger, _ = stage.replay(source_folder, incoming, old, multi, native, trace, arcs,
                                     radius, read(source_folder / "CANDIDATE-PATH.json"))
    if (source != read(source_folder / "FRONTIER.json")
            or ledger != read(source_folder / "LOWER-LEDGER.json")
            or source != read(folder / "SOURCE-FRONTIER.json")
            or len(source["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or basis["r_strict_interval"] != parent["r_strict_interval"]):
        raise ValueError("partial energy actual source partition did not semantically reconstruct")
    inventory.extend(paths)
    caps_folder = local_path(manifest["caps"])
    cap_report, paths = stage.bound(caps_folder)
    inventory.extend(paths)
    cap = read(caps_folder / "CERTIFICATE.json")
    if (read(folder / "CAP-CERTIFICATE.json") != cap
            or sha(caps_folder / "VERIFIED.json") != manifest["cap_acceptance_sha256"]):
        raise ValueError("partial energy replaced the same-root sharp caps")
    caps, _ = constraints.cap_gate(radius, cap, arcs)
    for module in (partial, quadratic, constraints, independent):
        if sha(module.__file__) != manifest["copied_files"][Path(module.__file__).name]:
            raise ValueError("partial energy executed arithmetic different from its sealed copy")
    proposal, kernels, runs = (read(folder / name) for name in ("PROPOSAL.json", "KERNELS.json", "NATIVE-RUNS.json"))
    if (proposal["schema"] != "N26-unaccepted-current-partial-prefix-energy-discovery-v1"
            or proposal["verified"] is not False or proposal["radius_scope"] != stage.SCOPE
            or proposal["source_acceptance_sha256"] != sha(source_folder / "VERIFIED.json")
            or proposal["source_frontier_sha256"] != sha(source_folder / "FRONTIER.json")
            or proposal["cap_acceptance_sha256"] != sha(caps_folder / "VERIFIED.json")
            or proposal["kernels_sha256"] != sha(folder / "KERNELS.json")):
        raise ValueError("partial energy discovery changed its graph, caps or actual source")
    inventory.extend([parent_path, replay_path])
    return manifest, parent, accepted, source, source_folder, radius, arcs, caps, proposal, kernels, runs, inventory


def derive(folder, values, selected=None, kernels_override=None, runs_override=None, radius_override=None):
    manifest, parent, accepted, source, source_folder, radius, arcs, caps, proposal, kernels, runs, _ = values
    selected = manifest["selected_source_indices"] if selected is None else selected
    kernels = kernels if kernels_override is None else kernels_override
    runs = runs if runs_override is None else runs_override
    radius = radius if radius_override is None else F(radius_override)
    if radius != F(accepted["radius_upper"]):
        raise ValueError("partial energy transfer radius differs from the actual same root")
    if (not isinstance(selected, list) or not selected or len(set(selected)) != len(selected)
            or any(type(i) is not int or not 0 <= i < len(source["pending_states"]) for i in selected)
            or len(runs) != len(selected)):
        raise ValueError("partial energy selected actual prefixes are missing, invalid or duplicated")
    records = {row["source_index"]: row for row in proposal["results"]}
    if len(records) != len(proposal["results"]):
        raise ValueError("partial discovery source indices are duplicated")
    refs = {b: OriginReference(26, b, "dfs", caps=stage.force.CAPS, scale=stage.force.D)
            for b in (14, 15, 16, 17)}
    results, domains, controls = [], [], []
    for index, (source_index, run) in enumerate(zip(selected, runs)):
        row = source["pending_states"][source_index]
        b, prefix = row["B"], tuple(row["prefix"])
        if row["terminal"]:
            raise ValueError("a complete terminal or candidate was processed as a partial nonterminal")
        if (run["index"] != index or run["source_index"] != source_index
                or run["B"] != b or run["prefix"] != list(prefix)):
            raise ValueError("partial native prefix ownership changed")
        reference = refs[b]
        state = reference.resolve(prefix)
        if {"B": b, **reference.entry(prefix, state, reference.children(state))} != row:
            raise ValueError("partial source raw state differs from independent prefix resolution")
        launch, native = read(folder / run["launch"]), read(folder / run["result"])
        command = ["/lib64/ld-linux-x86-64.so.2", linux(source_folder / "peel_prefix_origin.linux"),
                   "26", str(b), linux(folder / run["result"]), str(stage.force.D),
                   *map(str, stage.force.CAPS), "0", "dfs", "frontier", ",".join(map(str, prefix)), "0", "1"]
        if (launch["command"] != command or launch["exit_code"] != 0
                or sha(folder / run["result"]) != run["result_sha256"]
                or sha(folder / run["launch"]) != run["launch_sha256"] or not native["origin_screen"]):
            raise ValueError("partial prefix native origin check changed")
        check_frontier(native, reference, prefix, 0)
        record = records[source_index]
        spec = {"N": 26, "B": b, "next": row["next"], "faces": row["faces"]}
        if record["B"] != b or record["prefix"] != list(prefix) or record["spec"] != spec:
            raise ValueError("energy proof belongs to a different actual partial prefix")
        matrix, derivation = constraints.constraint_matrix(spec, caps)
        alternative, independent_derivation = independent.matrix(spec, caps)
        if matrix is None or matrix != alternative:
            raise ValueError("this positive energy overlay requires a nonempty independently matching domain")
        lower = [F(-matrix[i][0], constraints.SCALE) for i in range(1, b)]
        upper = [F(matrix[0][i], constraints.SCALE) for i in range(1, b)]
        kernel_index = record["kernel_index"]
        if (type(kernel_index) is not int or not 0 <= kernel_index < len(kernels)
                or kernels[kernel_index]["source_index"] != source_index):
            raise ValueError("partial kernel ownership differs from its actual prefix")
        kernel = partial.kernel_gate(spec, kernels[kernel_index]["certificate"])
        control = partial.identity_control(kernel)
        result = partial.bound(kernel, matrix, lower, upper, record["certificate"], radius, arcs)
        strict_gate(result)
        results.append({"source_index": source_index, "B": b, "prefix": list(prefix), "spec": spec,
                        "source_raw_state": row, "kernel_index": kernel_index,
                        "whole_partial_transport_subtree_excluded_for_radius_at_most_Rstar": True,
                        **result})
        domains.append({"source_index": source_index, "matrix": matrix,
                        "full_root_lower": list(map(str, lower)), "full_root_upper": list(map(str, upper)),
                        "all_pairs_Bellman_Ford_derivation": derivation,
                        "independent_BFS_Floyd_derivation": independent_derivation})
        controls.append({"source_index": source_index, **control})
    removed = set(selected)
    kept = [row for index, row in enumerate(source["pending_states"]) if index not in removed]
    if len(kept) + len(removed) != len(source["pending_states"]):
        raise ValueError("partial energy transfer lost an unattempted source subtree")
    old_terminals = [row for row in source["pending_states"] if row["terminal"]]
    new_terminals = [row for row in kept if row["terminal"]]
    if old_terminals != new_terminals or len(new_terminals) != parent["all_current_unresolved_terminal_paths_reconstructed"]:
        raise ValueError("partial energy transfer altered complete candidate or other terminal members")
    frontier = {"schema": "N26-current-partial-prefix-energy-conditional-frontier-v1",
                "radius_scope": stage.SCOPE, "radius_upper": str(radius),
                "screen_radius_threshold": str(stage.force.U),
                "inherited_source_is_unconditional_at_U": False,
                "families": [{"B": b, "I": 26 - b, "pending_subtrees": sum(row["B"] == b for row in kept),
                              "unresolved_terminal_subtrees": sum(row["B"] == b and row["terminal"] for row in kept)}
                             for b in (14, 15, 16, 17)],
                "pending_states": kept,
                "known_candidate_unique_complete_terminal": source["known_candidate_unique_complete_terminal"],
                "source_conditional_pending_subtrees": len(source["pending_states"]),
                "new_partial_energy_whole_subtrees_excluded": len(results),
                "all_unattempted_subtrees_and_all_complete_terminals_retained_identically": True,
                "original_U_frontier_rewritten": False,
                "full_catalog_complete": False, "global_optimality_proved": False}
    return frontier, results, domains, controls


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = input_gate(folder)
    manifest, parent, accepted, _, _, radius, _, _, _, kernels, runs, inventory = values
    frontier, results, domains, controls = derive(folder, values)
    negatives = []

    def reject(label, **changed):
        try:
            derive(folder, values, **changed)
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid current partial energy transfer accepted: " + label)

    selected = manifest["selected_source_indices"]
    record = next(row for row in values[8]["results"] if row["source_index"] == selected[0])
    reject("duplicate-current-partial-prefix", selected=selected + selected[:1], runs_override=runs + runs[:1])
    reject("same-root-radius-changed-to-conservative-U", radius_override=stage.force.U)
    bad = deepcopy(kernels)
    bad[record["kernel_index"]]["certificate"]["weight_numerators"][0] = 0
    reject("nonpositive-partial-rod-weight", kernels_override=bad)
    bad = deepcopy(kernels)
    cert = bad[record["kernel_index"]]["certificate"]
    cert["inverse_numerators"][0][0] = str(int(cert["inverse_numerators"][0][0]) + 1)
    reject("changed-partial-ground-inverse", kernels_override=bad)
    bad = deepcopy(kernels)
    bad[record["kernel_index"]]["certificate"]["schema"] = "N26-full-type-positive-quadratic-ground-kernel-v1"
    reject("complete-type-certificate-silently-relabelled", kernels_override=bad)
    bad = deepcopy(kernels)
    bad[record["kernel_index"]]["certificate"]["spec"]["faces"][0] ^= (1 << 0) | (1 << 2)
    reject("partial-kernel-belongs-to-a-different-present-face", kernels_override=bad)
    bad = deepcopy(runs)
    bad[0]["source_index"] += 1
    reject("native-run-attached-to-different-prefix", runs_override=bad)
    terminal = next(i for i, row in enumerate(values[3]["pending_states"]) if row["terminal"])
    reject("complete-candidate-terminal-removed-as-partial-prefix", selected=[terminal], runs_override=runs[:1])
    equality = deepcopy(results[0])
    equality["minimum_strict_energy_margin"] = "0"
    try:
        strict_gate(equality)
    except ValueError:
        negatives.append("equality-not-paid-as-strict-partial-energy")
    else:
        raise AssertionError("partial energy equality was paid")
    regression = read(folder / "ADAPTER-REGRESSION.json")
    if (regression["tested_adapter_sha256"] != sha(partial.__file__)
            or regression["regression_controls_passed"] != 12
            or len(regression["invalid_kernel_controls_rejected"]) != 11
            or regression["current_transport_subtrees_removed_by_this_test"] != 0):
        raise ValueError("partial adapter regression evidence changed")
    for name, value in (("FRONTIER.json", frontier), ("LOWER-LEDGER.json", results),
                        ("DOMAINS.json", domains), ("POSITIVE-CONTROLS.json", controls)):
        path = folder / name
        if path.exists():
            if read(path) != value:
                raise ValueError("partial energy published semantic output changed: " + name)
        else:
            path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    inventory.extend(folder / name for name in manifest["copied_files"])
    inventory.append(Path(__file__))
    digests = {linux(path): sha(path) for path in inventory}
    report = {"schema": "N26-accepted-current-partial-prefix-energy-whole-subtree-overlay-v1",
              "verified": True, "radius_scope": stage.SCOPE, "radius_upper": str(radius),
              "r_strict_interval": accepted["r_strict_interval"],
              "source_acceptance_sha256": manifest["source_acceptance_sha256"],
              "parent_current_audit_sha256": manifest["parent_current_audit_sha256"],
              "all_source_stage_events_and_siblings_semantically_reconstructed": True,
              "fresh_native_and_reference_partial_prefix_checks": len(results),
              "new_strict_radius_conditional_whole_partial_subtrees_excluded": len(results),
              "source_conditional_pending_subtrees": frontier["source_conditional_pending_subtrees"],
              "conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
              "families": frontier["families"],
              "all_unattempted_and_complete_terminal_raw_states_retained_identically": True,
              "all_partial_full_root_domains_and_inverse_identities_rechecked": True,
              "partial_square_completion_and_radius_one_controls": len(controls),
              "adapter_regression_controls": regression["regression_controls_passed"],
              "minimum_strict_energy_margin": str(min(F(row["minimum_strict_energy_margin"]) for row in results)),
              "minimum_strict_radius_margin": str(min(F(row["minimum_strict_radius_margin"]) for row in results)),
              "original_U_frontier_nodes_removed": 0,
              "candidate_angle_unresolved_closed_boxes_unchanged": parent["candidate_angle_unresolved_closed_boxes"],
              "unrestricted_reduction_final_joint_acceptance": False,
              "full_catalog_complete": False, "global_lower_bound_proved": False,
              "global_optimality_proved": False, "n27_started": False,
              "negative_controls_rejected": negatives,
              "files": {name: sha(folder / name) for name in
                        ["MANIFEST.json", *manifest["copied_files"], "FRONTIER.json", "LOWER-LEDGER.json",
                         "DOMAINS.json", "POSITIVE-CONTROLS.json"]},
              "source_files": digests, "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_partial_prefix_energy_overlay.py"]:
        raise ValueError("partial energy executed a different sealed checker")
    for text, digest in digests.items():
        if sha(text) != digest:
            raise ValueError("partial energy dependencies changed during final binding")
    for text, digest in parent["files"].items():
        if sha(text) != digest:
            raise ValueError("current parent bytes changed during partial energy acceptance")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2),
          flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    proposal = read(args.proposal)
    source_folder = local_path(proposal["source_stage"])
    accepted, _ = stage.bound(source_folder)
    if (read(args.source_replay) != accepted
            or sha(source_folder / "VERIFIED.json") != proposal["source_acceptance_sha256"]
            or sha(args.kernels) != proposal["kernels_sha256"]):
        raise ValueError("partial energy builder lacks matching actual source and kernel evidence")
    selected = [row["source_index"] for row in proposal["results"] if row["partial_energy_whole_root_proposed"]]
    if not selected:
        raise ValueError("no strict partial whole-root proposal to accept")
    args.output.mkdir(parents=True)
    copies = [(args.proposal, "PROPOSAL.json"), (args.kernels, "KERNELS.json"),
              (args.parent_current_audit, "SOURCE-CURRENT-AUDIT.json"),
              (source_folder / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
              (source_folder / "FRONTIER.json", "SOURCE-FRONTIER.json"),
              (local_path(proposal["caps"]) / "CERTIFICATE.json", "CAP-CERTIFICATE.json"),
              (args.regression, "ADAPTER-REGRESSION.json")]
    for name in ("verify_conditional_force_stage.py", "verify_force_stage.py", "verify_force_forest.py",
                 "n26_force.py", "n26_force_angles.py", "verify_degree_area.py", "verify_multislope_area.py",
                 "verify_partial_area_closures.py", "exact_arcs.py", "audit_prefix_origin.py", "audit_prefix_partition.py"):
        copies.append((source_folder / name, name))
    for name in ("verify_partial_prefix_energy_overlay.py", "n26_partial_prefix_quadratic_kernel.py",
                 "n26_quadratic_energy_minorant.py", "n26_sharp_radius_constraints.py", "n26_sharp_partial_domains.py"):
        copies.append((Path(__file__).with_name(name), name))
    copies.append((Path(__file__).with_name("n26-partial-prefix-energy-proof.md"), "PROOF.md"))
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    source = read(source_folder / "FRONTIER.json")
    runs = []
    for index, source_index in enumerate(selected):
        row = source["pending_states"][source_index]
        result, launch = args.output / f"prefix-{index:03d}.json", args.output / f"prefix-{index:03d}-launch.json"
        command = native_command(source_folder / "peel_prefix_origin.linux",
                                 ["26", str(row["B"]), linux(result), str(stage.force.D), *map(str, stage.force.CAPS),
                                  "0", "dfs", "frontier", ",".join(map(str, row["prefix"])), "0", "1"])
        run = subprocess.run(command, capture_output=True, timeout=30)
        launch.write_text(json.dumps({"command": command, "exit_code": run.returncode,
                                     "stdout": run.stdout.decode("utf-8", errors="replace"),
                                     "stderr": run.stderr.decode("utf-8", errors="replace")}, indent=2) + "\n",
                          encoding="utf-8")
        if run.returncode:
            raise ValueError("fresh partial native check failed; incomplete bundle preserved")
        runs.append({"index": index, "source_index": source_index, "B": row["B"], "prefix": row["prefix"],
                     "result": result.name, "result_sha256": sha(result),
                     "launch": launch.name, "launch_sha256": sha(launch)})
        copies.extend([(result, result.name), (launch, launch.name)])
    (args.output / "NATIVE-RUNS.json").write_text(json.dumps(runs, indent=2) + "\n", encoding="utf-8")
    copies.append((args.output / "NATIVE-RUNS.json", "NATIVE-RUNS.json"))
    manifest = {"schema": SCHEMA, "radius_scope": stage.SCOPE,
                "source_stage": linux(source_folder), "source_acceptance_sha256": sha(source_folder / "VERIFIED.json"),
                "source_published_replay": linux(args.source_replay),
                "parent_current_audit": linux(args.parent_current_audit),
                "parent_current_audit_sha256": sha(args.parent_current_audit),
                "caps": proposal["caps"], "cap_acceptance_sha256": proposal["cap_acceptance_sha256"],
                "selected_source_indices": selected,
                "copied_files": {name: sha(args.output / name) for _, name in copies}}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False, "selected_partial_prefixes": selected,
                      "independent_exact_acceptance_pending": True}), flush=True)


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    builder = commands.add_parser("build")
    for name in ("proposal", "kernels", "parent-current-audit", "source-replay", "regression", "output"):
        builder.add_argument("--" + name, type=Path, required=True)
    verifier = commands.add_parser("verify")
    verifier.add_argument("--input", type=Path, required=True)
    verifier.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "build":
        build(args)
    else:
        verify(args.input, args.report)


if __name__ == "__main__":
    main()
