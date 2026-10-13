"""Original initial-source prerequisites, exact queue retention and bindings.

Read-only historical inputs; only a NEW audit report is written. Completed
continuous tables and native search mathematics are explicitly qualified reuse.
All actual initial queue replacements and area graph/prefix duals are checked.
"""

import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
import json
import os
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import check_frontier, linux
import audit_prefix_origin as origin
import audit_prefix_partition as partition
import build_transport_frontier as original_transport
import new_upper_scope as family
import prepare_new_scope_frontiers as prepare
import run_new_scope_batch as queue
import run_prefix_batch as old_queue
import verify_conditional_force_stage as binding
import verify_multislope_area as area
import verify_partial_area_closures as partial


CURRENT_SHA = "c85e130c935e68e2275e53fa457c9c4d95d8be5416b128f4307a76061057911b"
FINAL_SHA = "7c2d29f19f310de58d03a2043fae3dde8bcaeb69635843086118a91ab9b6db4e"
CORE_SHA = "7d15411a1f1ff89262193de91225f9ebff1962ada84dade81f962fd162f134e7"
MODULES = (origin, partition, family, prepare, queue,
           old_queue, area, area.base, partial)


def normalized(text):
    return os.path.normcase(os.path.abspath(str(binding.local_path(text))))


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate original source JSON key: " + key)
        result[key] = value
    return result


class Inputs:
    def __init__(self, current):
        self.actual = {}
        for text, digest in current["files"].items():
            key = normalized(text)
            if key in self.actual and self.actual[key] != digest:
                raise ValueError("conflicting actual current lexical aliases")
            self.actual[key] = digest
        self.checked, self.missing, self.cache, self.roles = {}, {}, {}, {}

    def check(self, text, expected=None, role="initial-source"):
        path = binding.local_path(text)
        key = normalized(path)
        canonical = linux(path)
        # The preserved C: archive junction resolves to F:. If the CURRENT
        # inventory already explicitly binds that real target, a C: access
        # alias is not a second omitted prerequisite. Resolve only this
        # selected path, never every file in the273526-entry inventory.
        current_digest = self.actual.get(key) or self.actual.get(normalized(canonical))
        if expected is None:
            expected = current_digest or self.checked.get(canonical)
        digest = binding.sha(path)
        if expected is None or digest != expected or (
                current_digest is not None and digest != current_digest):
            raise ValueError("uncommitted/changed actual initial-source input: " + str(path))
        if canonical in self.checked and self.checked[canonical] != digest:
            raise ValueError("initial input changed during reconstruction")
        self.checked[canonical] = digest
        self.roles.setdefault(canonical, set()).add(role)
        if current_digest is None:
            self.missing[canonical] = digest
        else:
            self.missing.pop(canonical, None)
        return path

    def read(self, text, expected=None, role="initial-source"):
        path = self.check(text, expected, role)
        key = normalized(path)
        if key not in self.cache:
            self.cache[key] = json.loads(path.read_text(encoding="utf-8"),
                                        object_pairs_hook=unique_object)
        return self.cache[key]

    def bound_map(self, mapping, role):
        for text, digest in mapping.items():
            self.check(text, digest, role)

    def receipt(self, folder, expected=None, filename="VERIFIED.json"):
        path = folder / filename
        record = self.read(path, expected, "accepted-initial-receipt")
        if record.get("verified") is not True or record.get("global_optimality_proved") is not False:
            raise ValueError("wrong qualified original area acceptance scope")
        for name, digest in record["files"].items():
            # BASE-ACCEPTANCE honestly preserves the old base PROOF under
            # BASE-PROOF, as specified by the actual original base gate.
            local_name = "BASE-PROOF.md" if filename == "BASE-ACCEPTANCE.json" and name == "PROOF.md" else name
            target = folder / local_name
            if target.parent != folder:
                raise ValueError("original relative receipt escaped its bundle")
            self.check(target, digest, "accepted-initial-receipt-dependency")
        return record


def snapshot_gate(current, final, core):
    if (
        current["schema"] != "N26-complete-current-with-six-target-source-geometry-audit-v1"
        or current["radius_scope"] != binding.SCOPE
        or current["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or current["candidate_angle_unresolved_closed_boxes"] != 25
        or final["current_audit_sha256"] != CURRENT_SHA
        or final["all_current_file_digests_rehashed"] is not True
        or final["current_file_digests_rechecked"] != len(current["files"])
        or core["schema"] != "N26-exact26-core-original-geometry-source-interface-audit-v1"
        or core["proof_time_current_sha256"] != CURRENT_SHA
        or core["qualified_original_physical_disk_count"] != 26
        or core["new_formal_geometric_payments"] != 0
        or any(item[field] is not False for item in (current, final, core)
               for field in ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("initial-source audit changed actual proof-time scope")


def claim_gate(manifest, pending, completed):
    if (
        manifest["pending_prefixes"] != [list(p) for p in sorted(pending)]
        or manifest["closed_prefixes"] != [list(p) for p in sorted(completed)]
    ):
        raise ValueError("initial queue lost/duplicated/changed actual retained paths")
    all_paths = set(pending) | set(completed)
    if len(all_paths) != len(pending) + len(completed) or any(
            path[:depth] in all_paths for path in all_paths for depth in range(len(path))):
        raise ValueError("initial queue paths overlap")


def command_gate(record, manifest, prefix, operation, limit, depth):
    queue.command_gate(record, manifest, prefix, operation, limit, depth)
    command = record["command"]
    head = command[:-14]
    if head[:2] == ["wsl.exe", "--"]:
        head = head[2:]
    if (
        len(head) != 2 or head[0] != "/lib64/ld-linux-x86-64.so.2"
        or normalized(head[1]) != normalized("work/prefix-origin-v1/peel_prefix_origin.linux")
    ):
        raise ValueError("initial event command names a different native kernel")


def run_data(inputs, record, expected_exit):
    if record["exit_code"] != expected_exit:
        raise ValueError("initial native event has wrong recorded exit")
    log = inputs.check(record["log"], record["log_sha256"], "original-event-log")
    result_path = binding.local_path(record["path"])
    if expected_exit:
        if result_path.exists() or "REJECTED NODE LIMIT:" not in log.read_text(encoding="utf-8"):
            raise ValueError("limited initial solve is not an unpaid split")
        return None
    return inputs.read(result_path, record["sha256"], "original-event-result")


def solve_gate(data, manifest, prefix):
    b = manifest["B"]
    if (
        data["complete"] is not True or data["operation"] != "solve"
        or data["N"] != 26 or data["B"] != b or data["prefix"] != list(prefix)
        or data["mode"] != "dfs" or data["screen"] is not True
        or data["origin_screen"] is not True or data["caps"] != list(area.CAPS)
        or data["scale"] != area.D or data["family_complete"] is not False
        or data["geometric_reduction_proved"] is not False
        or data["global_optimality_proved"] is not False
        or type(data["rooted"]) is not int or data["rooted"] < len(data["survivors"])
    ):
        raise ValueError("initial complete-subtree result changed owner or scope")
    seen = set()
    for row in data["survivors"]:
        faces, stabilizer = tuple(row["faces"]), row["stabilizer"]
        if (
            faces in seen or tuple(sorted(faces)) != faces
            or type(stabilizer) is not int or not 1 <= stabilizer <= 2*b
            or (2*b) % stabilizer
        ):
            raise ValueError("invalid/duplicate original completed canonical graph")
        seen.add(faces)
    if data["orbits"] != len(seen):
        raise ValueError("wrong original completed graph count")


def replacement_gate(prefix, rows, expected):
    if rows != expected or not rows or any(len(row["prefix"]) != len(prefix)+1 for row in rows):
        raise ValueError("initial split lost an immediate child or changed its state")


def reconstruct_queue(inputs, manifest, initial):
    b = manifest["B"]
    if (
        manifest["schema"] != "N26-new-threshold-adaptive-prefix-checkpoint-v1"
        or manifest["N"] != 26 or b not in (14, 15, 16, 17)
        or manifest["caps"] != list(area.CAPS) or manifest["scale"] != area.D
        or manifest["origin_condition_enabled"] is not True
        or manifest["global_optimality_proved"] is not False
        or manifest["arbitrary_cover_reduction_accepted"] is not False
        or type(manifest["node_limit"]) is not int or manifest["node_limit"] < 2
    ):
        raise ValueError("wrong original initial queue model")
    ref = OriginReference(26, b, "dfs", caps=area.CAPS, scale=area.D)
    ref.children = lru_cache(None)(ref.children)
    rows = check_frontier(initial, ref, (), 2)
    if initial["origin_screen"] is not True:
        raise ValueError("initial source lost the origin predicate")
    pending = {tuple(row["prefix"]): row for row in rows}
    completed, records, events, first_replacement = {}, [], Counter(), None
    for event in manifest["events"]:
        prefix, kind = tuple(event["prefix"]), event["kind"]
        if prefix not in pending:
            raise ValueError("initial event outside current pending partition")
        events[kind] += 1
        if kind == "closed":
            record = event["run"]
            command_gate(record, manifest, prefix, "solve", manifest["node_limit"], 0)
            data = run_data(inputs, record, 0)
            solve_gate(data, manifest, prefix)
            completed[prefix] = pending.pop(prefix)
            records.append((record, data))
        elif kind in ("split", "refine"):
            if kind == "split":
                record = event["limited_run"]
                command_gate(record, manifest, prefix, "solve", manifest["node_limit"], 0)
                run_data(inputs, record, 1)
            elif pending[prefix]["child_count"] != 1:
                raise ValueError("initial claimed forced refinement was not forced")
            record = event["frontier_run"]
            command_gate(record, manifest, prefix, "frontier", 0, 1)
            data = run_data(inputs, record, 0)
            if data["origin_screen"] is not True:
                raise ValueError("initial replacement lost the origin predicate")
            expected = ref.frontier(prefix, 1)
            replacement_gate(prefix, data["frontier"], expected)
            children = check_frontier(data, ref, prefix, 1)
            if first_replacement is None:
                first_replacement = (prefix, children, expected)
            pending.pop(prefix)
            for row in children:
                child = tuple(row["prefix"])
                if child in pending or child in completed:
                    raise ValueError("initial immediate-child replacement overlaps")
                pending[child] = row
        else:
            raise ValueError("unknown initial source event")
    claim_gate(manifest, pending, completed)
    graphs = {}
    for record, data in records:
        for row in data["survivors"]:
            faces = tuple(row["faces"])
            if faces in graphs and graphs[faces] != row["stabilizer"]:
                raise ValueError("original overlapping canonical codes disagree")
            graphs[faces] = row["stabilizer"]
    values = {
        "completed_subtrees": len(completed), "pending_subtrees": len(pending),
        "closed_rooted_graphs": sum(data["rooted"] for _, data in records),
        "closed_distinct_orbits": len(graphs),
        "limited_tasks_split_not_excluded": events["split"],
        "forced_nodes_refined": events["refine"],
        "restricted_family_catalog_exhausted": not pending,
    }
    return ref, pending, completed, records, graphs, values, events, first_replacement


def catalog_gate(source, completed_records):
    expected = {
        (data["B"], tuple(data["prefix"]), normalized(record["path"]), record["sha256"])
        for record, data in completed_records
    }
    got = {
        (row["B"], tuple(row["prefix"]), normalized(row["original_path"]), row["sha256"])
        for row in source["catalogs"]
    }
    if (
        len(expected) != len(completed_records) or len(got) != len(source["catalogs"])
        or got != expected or source["selected_closed_subtrees"] != len(expected)
        or source["full_catalog_complete"] is not False
        or source["global_optimality_proved"] is not False
    ):
        raise ValueError("selected catalogue inventory lost/changed a completed raw path")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("initial-source audit requires a new report")
    current_path = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
    final_path = Path("outputs/n26-current28-six-target-supplemental-independent-final-v1.json")
    core_path = Path("outputs/n26-exact26-core-source-interface-audit-v2.json")
    for path, digest in ((current_path, CURRENT_SHA), (final_path, FINAL_SHA), (core_path, CORE_SHA)):
        if binding.sha(path) != digest:
            raise ValueError("actual completed initial-interface premise changed")
    current, final, core = [binding.read(path) for path in (current_path, final_path, core_path)]
    snapshot_gate(current, final, core)
    inputs = Inputs(current)
    inputs.check(current_path, CURRENT_SHA, "proof-time-current")
    inputs.check(final_path, FINAL_SHA, "proof-time-independent-final")
    inputs.read(core_path, CORE_SHA, "qualified-completed-continuous-table-audit")
    inputs.bound_map(core["input_sha256"], "completed-core-audit-input")
    output = Path("outputs")
    # Bootstrap omitted original paths only through the ACTUAL bound area
    # SOURCE's committed provenance, never by accepting a newly computed hash.
    area_folder = output/"n26-multislope-area-lower-v1"
    source = inputs.read(area_folder/"SOURCE.json")
    inputs.bound_map(source["original_files"], "selected-catalogue-original-provenance")
    for b in (14, 15, 16, 17):
        progress = inputs.read(output/f"n26-new-B{b}-progress-v1.json")
        manifest = inputs.read(progress["latest_checkpoint"], progress["checkpoint_sha256"])
        inputs.bound_map(manifest["frozen_inputs"], "original-checkpoint-frozen-input")
    frontier_folder = output/"n26-new-scope-frontiers-v1"
    frontier_receipt = inputs.read(frontier_folder/"VERIFIED.json")
    inputs.bound_map(frontier_receipt["files"], "initial-frontier-prerequisite")
    scope = output / "n26-new-scope-v1"
    scope_receipt = inputs.read(scope/"VERIFIED.json")
    if (
        scope_receipt["arithmetic_verified"] is not True
        or scope_receipt["family_scope_valid_assuming_cited_n8_theorem"] is not True
        or scope_receipt["N8_lower_bound_reproved_here"] is not False
    ):
        raise ValueError("initial family source hid its imported n8 qualification")
    inputs.bound_map(scope_receipt["files"], "original-scope-prerequisite")
    # The frozen scope receipt records Windows names while later checkpoints
    # record /mnt/c names. bound_map already committed the normalized identity.
    constants = inputs.read(scope/"CONSTANTS.json")
    if constants["angle_caps"] != list(area.CAPS) or constants["angle_scale"] != area.D:
        raise ValueError("initial source changed U-angle caps")
    if (
        frontier_receipt["frontier_generation_and_independent_reconstruction_verified"] is not True
        or frontier_receipt["new_angle_caps"] != list(area.CAPS)
        or frontier_receipt["new_radius_upper"] != constants["radius_upper"]
        or frontier_receipt["origin_condition_enabled"] is not True
    ):
        raise ValueError("initial fresh-U frontier scope changed")
    inputs.bound_map(frontier_receipt["files"], "initial-frontier-prerequisite")
    origin_receipt = inputs.read(output/"n26-origin-screen-controls-v1.json")
    inputs.bound_map(origin_receipt["files"], "original-origin-control-prerequisite")
    module_versions = {}
    for module in MODULES:
        name, actual = Path(module.__file__).name, binding.sha(module.__file__)
        versions = {digest for text, digest in current["files"].items()
                    if binding.local_path(text).name == name}
        committed = {digest for text, digest in inputs.checked.items()
                     if binding.local_path(text).name == name}
        if (versions | committed) != {actual}:
            raise ValueError("initial-source helper differs from committed original implementation: " + name)
        # An identical committed original executor may have been copied into a
        # bundle. Record the loaded work path as an explicit selected dependency.
        inputs.check(module.__file__, actual, "inspected-loaded-original-helper")
        module_versions[name] = actual
    # Complete origin regressions are qualified original implementation
    # premises, not fresh native executions. Their actual raw bytes are bound.
    original_regression_runs = 0
    for label in ("native_runs", "baseline_runs"):
        for record in origin_receipt[label]:
            inputs.check(record["log"], record["log_sha256"], "original-origin-regression-log")
            if record["exit_code"] == 0:
                inputs.check(record["path"], record["sha256"], "original-origin-regression-result")
            elif binding.local_path(record["path"]).exists():
                raise ValueError("original failed origin regression published a result")
            original_regression_runs += 1
    queues, completed_records, all_graphs, queue_summaries = {}, [], set(), []
    for b in (14, 15, 16, 17):
        progress = inputs.read(output/f"n26-new-B{b}-progress-v1.json")
        if (
            progress["N"] != 26 or progress["B"] != b
            or progress["verified_partition_bookkeeping"] is not True
            or progress["global_optimality_proved"] is not False
        ):
            raise ValueError("wrong original source progress scope")
        manifest = inputs.read(progress["latest_checkpoint"], progress["checkpoint_sha256"], "original-checkpoint")
        inputs.bound_map(manifest["frozen_inputs"], "original-checkpoint-frozen-input")
        if inputs.read(manifest["constants_path"]) != constants:
            raise ValueError("initial checkpoint used different family constants")
        row = next(item for item in frontier_receipt["families"] if item["B"] == b)
        if (
            normalized(row["frontier_path"]) != normalized(manifest["initial_frontier_path"])
            or row["frontier_sha256"] != manifest["initial_frontier_sha256"]
        ):
            raise ValueError("initial checkpoint names another root frontier")
        initial = inputs.read(manifest["initial_frontier_path"], row["frontier_sha256"], "initial-entire-depth2-frontier")
        launch = inputs.read(frontier_folder/f"N26-B{b}-launch.json", row["launch_sha256"], "initial-frontier-launch")
        launch_record = {"path": row["frontier_path"], "command": launch["command"]}
        command_gate(launch_record, manifest, (), "frontier", 0, 2)
        if launch["exit_code"] != 0:
            raise ValueError("initial whole frontier launch failed")
        result = reconstruct_queue(inputs, manifest, initial)
        if any(progress[key] != value for key, value in result[5].items()):
            raise ValueError("original progress overclaims its reconstructed checkpoint")
        queues[b] = (manifest, initial, result)
        completed_records.extend(result[3])
        all_graphs.update((b, faces) for faces in result[4])
        summary = {"B": b, "events": dict(result[6]), **result[5]}
        queue_summaries.append(summary)
        print(json.dumps({"initial_family_queue_freshly_reconstructed": summary}), flush=True)
    area_receipt = inputs.receipt(area_folder)
    base_receipt = inputs.receipt(area_folder, filename="BASE-ACCEPTANCE.json")
    old = inputs.read(area_folder/"CERTIFICATE.json", base_receipt["files"]["CERTIFICATE.json"])
    multi = inputs.read(area_folder/"MULTISLOPE-CERTIFICATE.json", area_receipt["files"]["MULTISLOPE-CERTIFICATE.json"])
    area.base.parameter_gate(old)
    area.parameter_gate(multi)
    if (
        core["complete_base_area_envelope_recomputations"][0]["certificate_sha256"] != binding.sha(area_folder/"CERTIFICATE.json")
        or core["complete_multi_slope_envelope_recomputations"][0]["certificate_sha256"] != binding.sha(area_folder/"MULTISLOPE-CERTIFICATE.json")
        or core["complete_base_area_envelope_recomputations"][0]["all8192_CLOSED_continuous_bins_recomputed"] is not True
        or core["complete_multi_slope_envelope_recomputations"][0]["all8192_CLOSED_continuous_bins_and_16_GLOBAL_supports_recomputed"] is not True
    ):
        raise ValueError("reused completed continuous arithmetic has different coefficient tables")
    source = inputs.read(area_folder/"SOURCE.json", old["source_sha256"])
    inputs.bound_map(source["original_files"], "selected-catalogue-original-provenance")
    catalog_gate(source, completed_records)
    for row in source["catalogs"]:
        original = inputs.read(row["original_path"], row["sha256"], "original-completed-native-catalogue")
        copied = inputs.read(area_folder/row["filename"], row["sha256"], "accepted-area-catalogue-copy")
        if original != copied:
            raise ValueError("initial catalogue copy differs from its actual execution result")
    graphs, source_paths = area.base.source_gate(area_folder, old)
    if set(graphs) != all_graphs or len(graphs) != 13237:
        raise ValueError("completed native graph union differs from exact selected area source")
    cases = inputs.read(area_folder/"CASE-CERTIFICATES.json", multi["case_certificates_sha256"])
    ledger, counts = area.graph_ledger(graphs, cases, multi, old)
    stored = inputs.read(area_folder/"MULTISLOPE-GRAPH-LEDGER.json",
                         area_receipt["files"]["MULTISLOPE-GRAPH-LEDGER.json"])
    if ledger != stored or counts["still_unresolved_graphs"] != 0 or not area_receipt["all_selected_graphs_excluded"]:
        raise ValueError("actual selected graph duals no longer strictly exclude the whole union")
    print(json.dumps({"actual_initial_graph_duals_recomputed": len(graphs),
                      "exact_dual_cases": len(cases), "still_unresolved_graphs": 0}), flush=True)
    part_folder = output/"n26-partial-area-closures-v1"
    # The current inventory omitted this original receipt, including all
    # equal-byte aliases. Do NOT treat its verified flag as an accepted
    # premise. Select its original witnesses as NEW explicit inputs, then
    # independently reconstruct ALL their arithmetic and retention below.
    part_receipt_path = part_folder/"VERIFIED.json"
    part_receipt = inputs.receipt(part_folder, binding.sha(part_receipt_path))
    inputs.roles[linux(part_receipt_path)].add("unbound-original-partial-receipt-NOT-a-reused-acceptance-premise")
    if part_receipt["area_bundle_acceptance_sha256"] != binding.sha(area_folder/"VERIFIED.json"):
        raise ValueError("initial partial area proofs use another completed graph arithmetic")
    cert = inputs.read(part_folder/"PARTIAL-CERTIFICATE.json", part_receipt["files"]["PARTIAL-CERTIFICATE.json"])
    if (
        cert["N"] != 26 or cert["B"] != 14
        or cert["area_acceptance_sha256"] != binding.sha(area_folder/"VERIFIED.json")
        or cert["full_catalog_complete"] is not False or cert["global_optimality_proved"] is not False
        or part_receipt["schema"] != "N26-B14-exact-area-excluded-prefixes-v1"
        or part_receipt["N"] != 26 or part_receipt["B"] != 14
        or part_receipt["executed_checker_sha256"] != binding.sha(partial.__file__)
    ):
        raise ValueError("newly selected original B14 witness has wrong model/arithmetic scope")
    initial14 = inputs.read(part_folder/"INITIAL-FRONTIER.json", cert["initial_frontier_sha256"])
    if initial14 != queues[14][1]:
        raise ValueError("B14 partial replacement starts from a different entire initial frontier")
    reference = queues[14][2][0]
    pending14, excluded14, splits = partial.partition_for(cert, reference, initial14)
    strict_bounds = []
    for case in cert["cases"]:
        value = partial.partial_bound(case, excluded14[tuple(case["prefix"])], old, multi)
        if value >= 0:
            raise ValueError("initial partial prefix lacks a strict all-completion area bound")
        strict_bounds.append({"prefix": case["prefix"], "area_dual_strict_upper": str(value)})
    if strict_bounds != part_receipt["strict_area_bounds"]:
        raise ValueError("initial all-completion prefix ledger differs from actual acceptance")
    if (
        part_receipt["strictly_excluded_whole_transport_subtrees"] != len(excluded14)
        or part_receipt["pending_cover_transport_subtrees"] != len(pending14)
        or part_receipt["pending_prefixes"] != [list(prefix) for prefix in sorted(pending14)]
        or any(part_receipt[field] is not False for field in (
            "family_exhausted", "full_catalog_complete", "unrestricted_reduction_final_joint_acceptance",
            "global_lower_bound_proved", "global_optimality_proved"))
    ):
        raise ValueError("freshly reconstructed B14 arithmetic/retention disagrees with old report")
    transport_rows, families = [], []
    for b, (manifest, initial, result) in queues.items():
        ref, pending, completed, records, graph_union, values, events, replacement = result
        if b == 14:
            covered = lambda prefix: any(prefix[:len(p)] == p for p in excluded14)
            covered_pending, covered_closed = sum(map(covered, pending)), sum(map(covered, completed))
            if (covered_pending, covered_closed) != (20, 6):
                raise ValueError("initial B14 all-prefix/native checkpoint relationship changed")
            active = pending14
        else:
            if graph_union:
                raise ValueError("initial other-family completed catalogue was not empty")
            covered_pending = covered_closed = 0
            active = {prefix: ref.resolve(prefix) for prefix in pending}
        active = {prefix: ref.normalize(state) for prefix, state in active.items()}
        transport_rows.extend({"B": b, **ref.entry(prefix, state, ref.children(state))}
                              for prefix, state in sorted(active.items()))
        families.append({
            "B": b, "I": 26-b, "native_pending_preserved": len(pending),
            "native_completed_subtrees": len(completed),
            "native_pending_wholly_covered_by_area_closure": covered_pending,
            "native_completed_wholly_covered_by_area_closure": covered_closed,
            "active_cover_transport_subtrees": len(active), "family_exhausted": False,
        })
    reconstructed = {
        "schema": "N26-current-cover-transport-frontier-v1",
        "families": families, "pending_states": transport_rows,
        "selected_completed_catalog_graphs": len(graphs),
        "selected_unresolved_catalog_graphs": 0,
        "native_pending_preserved_total": sum(row["native_pending_preserved"] for row in families),
        "active_cover_transport_subtrees_total": len(transport_rows),
        "B14_whole_area_excluded_prefixes": [list(prefix) for prefix in sorted(excluded14)],
        "B14_all_prefix_splits": splits,
        "original_native_checkpoints_unchanged": True,
        "complete_cover_transport_partition_reconstructed": True,
        "full_catalog_complete": False, "unrestricted_reduction_final_joint_acceptance": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
    transport_path = output/"n26-current-cover-transport-frontier-v1.json"
    transport = inputs.read(
        transport_path, binding.sha(transport_path), "freshly-reconstructed-entire-initial-source")
    if {key: value for key, value in transport.items() if key != "files"} != reconstructed:
        raise ValueError("initial entire source did not reconstruct exactly")
    # Unlike a reused native receipt, this entire source object has just been
    # reconstructed. Its path/digest is a NEW explicitly audited dependency.
    inputs.check(transport_path, binding.sha(transport_path), "freshly-reconstructed-entire-initial-source")
    inputs.bound_map(transport["files"], "original-transport-source-prerequisite")
    transport_code = Path(original_transport.__file__)
    if inputs.checked[linux(transport_code)] != binding.sha(transport_code):
        raise ValueError("actual original transport builder changed")
    module_versions[transport_code.name] = binding.sha(transport_code)
    negatives = []
    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("bad actual initial source accepted: " + label)
    manifest, initial, result = queues[14]
    changed = deepcopy(manifest)
    changed["pending_prefixes"].pop()
    reject("lost-original-pending-path", lambda: claim_gate(changed, result[1], result[2]))
    changed = deepcopy(manifest)
    changed["closed_prefixes"].append(changed["closed_prefixes"][0])
    reject("duplicate-original-completed-path", lambda: claim_gate(changed, result[1], result[2]))
    prefix, children, expected = result[7]
    reject("lost-immediate-split-child", lambda: replacement_gate(prefix, children[:-1], expected))
    changed = deepcopy(initial)
    changed["caps"][3] -= 1
    reject("mixed-old-or-changed-initial-cap", lambda: check_frontier(changed, reference, (), 2))
    limited = next(event["limited_run"] for event in manifest["events"] if event["kind"] == "split")
    reject("node-limit-promoted-to-completion", lambda: run_data(inputs, limited, 0))
    changed = deepcopy(source)
    changed["catalogs"].pop()
    reject("lost-completed-catalogue-even-if-empty", lambda: catalog_gate(changed, completed_records))
    changed = deepcopy(cert)
    changed["expected_pending_prefixes"].pop()
    reject("lost-B14-area-replacement-sibling", lambda: partial.partition_for(changed, reference, initial14))
    changed = deepcopy(cert)
    changed["cases"].append(changed["cases"][0])
    reject("double-paid-overlapping-B14-prefix", lambda: partial.partition_for(changed, reference, initial14))
    changed_case = deepcopy(cert["cases"][0])
    changed_case["rational_dual_weights"][0][1] = "-1"
    reject("negative-all-completion-area-dual", lambda: partial.partial_bound(
        changed_case, excluded14[tuple(changed_case["prefix"])], old, multi))
    reject("changed-original-result-digest", lambda: inputs.check(completed_records[0][0]["path"], "0"*64))
    changed_current = {**current, "global_optimality_proved": True}
    reject("initial-audit-promoted-to-global-optimality", lambda: snapshot_gate(changed_current, final, core))
    proof_path = Path("work/n26-initial-source-retention-interface-proof.md")
    for path in (Path(__file__), proof_path):
        inputs.check(path, binding.sha(path), "new-initial-audit-and-continuous-interface")
    # Every selected byte, not the entire273526-file current, is checked again.
    for text, digest in inputs.checked.items():
        if binding.sha(text) != digest:
            raise ValueError("initial prerequisite changed during exact reconstruction")
    inputs.read(current_path, CURRENT_SHA)
    inputs.read(final_path, FINAL_SHA)
    inputs.read(core_path, CORE_SHA)
    missing_historical = {
        text: digest for text, digest in inputs.missing.items()
        if "new-initial-audit-and-continuous-interface" not in inputs.roles[text]
        and text not in (linux(current_path), linux(final_path), linux(core_path))
    }
    report = {
        "schema": "N26-original-initial-source-retention-and-prerequisite-audit-v1",
        "verified": False, "new_formal_geometric_payments": 0,
        "actual_proof_time_current_sha256": CURRENT_SHA,
        "actual_proof_time_independent_final_sha256": FINAL_SHA,
        "qualified_completed_core_interface_audit_sha256": CORE_SHA,
        "original_helpers_match_committed_initial_AND_bound_current_digests": module_versions,
        "actual_four_initial_depth2_frontiers_reconstructed": True,
        "actual_four_full_adaptive_queues_reconstructed": queue_summaries,
        "all160_actual_original_queue_events_preserve_complete_partition": sum(sum(item["events"].values()) for item in queue_summaries) == 160,
        "all14_actual_completed_raw_catalogues_and_copies_bijectively_matched": len(completed_records) == 14,
        "actual_original_graph_union_and_exact_strict_area_duals_recomputed": counts,
        "actual_B14_strict_all_completion_prefix_duals_recomputed": len(strict_bounds),
        "unbound_original_B14_receipt_NOT_trusted_ALL_witness_arithmetic_AND_retention_freshly_validated": True,
        "actual_B14_all_siblings_and20pending6completed_relationship_reconstructed": True,
        "actual_original_combined_transport_source_exactly_reconstructed": True,
        "original_transport_families": families,
        "original_transport_pending_subtrees": len(transport_rows),
        "original_origin_regression_record_bytes_checked_NOT_native_regressions_rerun": original_regression_runs,
        "original_completed_native_search_mathematics_honestly_REUSED_NOT_fresh_all_tree_replay": True,
        "completed8192bin_continuous_tables_honestly_REUSED_NOT_rerun_here": True,
        "qualified_prior_n25_and_explicit_imported_n8_premises_preserved": True,
        "all_selected_inputs_freshly_rehashed_before_AND_after_reconstruction": True,
        "actual_selected_input_count": len(inputs.checked),
        "historical_selected_inputs_missing_from_current_explicit_inventory": missing_historical,
        "historical_selected_missing_count": len(missing_historical),
        "all_selected_missing_including_completed_core_audit_and_new_executor": inputs.missing,
        "missing_input_roles": {text: sorted(inputs.roles[text]) for text in inputs.missing},
        "actual_negative_controls_rejected": negatives,
        "current_formal_frontier_AND_candidate_roots_NOT_changed_by_this_audit": True,
        "advanced_candidate_model_interfaces_and_final_unrestricted_joint_gate_STILL_required": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inputs.checked,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "actual_initial_source_retention_audit_completed_NOT_current_admission": True,
        "actual_original_events": 160, "actual_completed_catalogues": len(completed_records),
        "exact_selected_graph_duals": len(graphs),
        "exact_all_completion_prefix_duals": len(strict_bounds),
        "original_transport_subtrees": len(transport_rows),
        "historical_selected_missing_inputs": len(missing_historical),
        "actual_negative_controls_rejected": len(negatives),
        "new_formal_geometric_payments": 0, "global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
