"""Independent reverse partition, BFS windows and exact initial area duals.

Does not import the new primary initial-source auditor. No native search or
8192-bin table replay is claimed here; those qualified premises stay explicit.
"""

import argparse
from collections import Counter, deque
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import json
import os
from pathlib import Path

from audit_prefix_origin import OriginReference, validate_disk
from audit_prefix_partition import linux
import verify_conditional_force_stage as binding


CURRENT_SHA = "c85e130c935e68e2275e53fa457c9c4d95d8be5416b128f4307a76061057911b"
CORE_SHA = "7d15411a1f1ff89262193de91225f9ebff1962ada84dade81f962fd162f134e7"
CAPS, D, C = (754112, 1555305, 2486507, 3880649), 10**7, 10**12
SLOPES = tuple(F(value, 4) for value in
               (-12, -16, -18, -20, -21, -22, -23, -24, -25, -26, -28, -32, -40, -48, -64, -96))


def normalized(text):
    return os.path.normcase(os.path.abspath(str(binding.local_path(text))))


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate independent initial-source JSON key")
        result[key] = value
    return result


class Reader:
    def __init__(self, inventory):
        self.inventory, self.cache = {}, {}
        for text, digest in inventory.items():
            key = normalized(text)
            if key in self.inventory and self.inventory[key][1] != digest:
                raise ValueError("independent initial-source inventory has conflicting aliases")
            self.inventory[key] = (text, digest)
        self.rehash()

    def check(self, text):
        key = normalized(text)
        if key not in self.inventory:
            raise ValueError("independent source needs an omitted selected prerequisite")
        original, digest = self.inventory[key]
        if binding.sha(text) != digest:
            raise ValueError("independent initial-source prerequisite changed")
        return binding.local_path(text)

    def read(self, text):
        path = self.check(text)
        key = normalized(path)
        if key not in self.cache:
            self.cache[key] = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
        return self.cache[key]

    def rehash(self):
        for text, digest in self.inventory.values():
            if binding.sha(text) != digest:
                raise ValueError("independent initial-source selected content mismatch")


def audit_gate(audit):
    if (
        audit["schema"] != "N26-original-initial-source-retention-and-prerequisite-audit-v1"
        or audit["actual_proof_time_current_sha256"] != CURRENT_SHA
        or audit["qualified_completed_core_interface_audit_sha256"] != CORE_SHA
        or audit["actual_selected_input_count"] != len(audit["input_sha256"])
        or audit["all160_actual_original_queue_events_preserve_complete_partition"] is not True
        or audit["all14_actual_completed_raw_catalogues_and_copies_bijectively_matched"] is not True
        or audit["unbound_original_B14_receipt_NOT_trusted_ALL_witness_arithmetic_AND_retention_freshly_validated"] is not True
        or audit["original_completed_native_search_mathematics_honestly_REUSED_NOT_fresh_all_tree_replay"] is not True
        or audit["completed8192bin_continuous_tables_honestly_REUSED_NOT_rerun_here"] is not True
        or audit["new_formal_geometric_payments"] != 0
        or any(audit[field] is not False for field in (
            "verified", "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("independent audit changed initial source or qualified proof scope")


def partition_set(prefixes):
    result = {tuple(prefix) for prefix in prefixes}
    if len(result) != len(prefixes) or any(
            path[:depth] in result for path in result for depth in range(len(path))):
        raise ValueError("independent partition has duplicate/overlapping leaves")
    return result


def reverse_queue(manifest, initial, reader):
    b = manifest["B"]
    ref = OriginReference(26, b, "dfs", caps=CAPS, scale=D)
    ref.children = lru_cache(None)(ref.children)
    pending = partition_set(manifest["pending_prefixes"])
    completed = partition_set(manifest["closed_prefixes"])
    if pending & completed:
        raise ValueError("independent pending/completed sets overlap")
    original_pending = set(pending)
    raw_records, counts = [], Counter()
    for event in reversed(manifest["events"]):
        prefix, kind = tuple(event["prefix"]), event["kind"]
        counts[kind] += 1
        if kind == "closed":
            if prefix not in completed or prefix in pending:
                raise ValueError("reverse completed transfer has no unique owner")
            record = event["run"]
            data = reader.read(record["path"])
            if (
                record["exit_code"] != 0 or data["complete"] is not True
                or data["operation"] != "solve" or data["N"] != 26 or data["B"] != b
                or data["prefix"] != list(prefix) or data["mode"] != "dfs"
                or data["origin_screen"] is not True or data["screen"] is not True
                or data["caps"] != list(CAPS) or data["scale"] != D
                or data["geometric_reduction_proved"] is not False
                or data["global_optimality_proved"] is not False
            ):
                raise ValueError("independent completed native owner/scope changed")
            reader.check(record["log"])
            raw_records.append((record, data))
            completed.remove(prefix)
            pending.add(prefix)
        elif kind in ("split", "refine"):
            record = event["frontier_run"]
            data = reader.read(record["path"])
            expected = ref.frontier(prefix, 1)
            children = {tuple(row["prefix"]) for row in expected}
            if (
                record["exit_code"] != 0 or data["frontier"] != expected
                or data["origin_screen"] is not True or not children
                or prefix in pending or prefix in completed or not children <= pending
                or any(len(child) != len(prefix)+1 for child in children)
            ):
                raise ValueError("reverse split cannot recover all its actual children")
            if kind == "refine" and len(children) != 1:
                raise ValueError("independent forced refinement has several children")
            if kind == "split":
                limited = event["limited_run"]
                log = reader.check(limited["log"])
                if (
                    limited["exit_code"] != 1 or binding.local_path(limited["path"]).exists()
                    or "REJECTED NODE LIMIT:" not in log.read_text(encoding="utf-8")
                ):
                    raise ValueError("independent limit failure was treated as a proof")
            pending.difference_update(children)
            pending.add(prefix)
        else:
            raise ValueError("independent source has an unknown queue event")
    expected_initial = ref.frontier((), 2)
    if completed or pending != {tuple(row["prefix"]) for row in expected_initial} or initial["frontier"] != expected_initial:
        raise ValueError("reverse160-event induction did not recover the entire initial roots")
    return ref, original_pending, raw_records, counts


def adjacency_for(faces):
    result = [set() for _ in range(26)]
    for face in faces:
        vertices = [i for i in range(26) if face >> i & 1]
        for u, v in combinations(vertices, 2):
            result[u].add(v)
            result[v].add(u)
    return result


def bfs_windows(b, adjacency):
    distances = []
    for start in range(b):
        dist = [99]*26
        dist[start] = 0
        todo = deque([start])
        while todo:
            vertex = todo.popleft()
            if dist[vertex] == 3:
                continue
            for other in adjacency[vertex]:
                if dist[other] == 99:
                    dist[other] = dist[vertex]+1
                    todo.append(other)
        distances.append(dist)
    windows = set()
    for i in range(b):
        for j in range(i+1, b):
            distance = min(distances[u][v] for u in (i, (i+1)%b) for v in (j, (j+1)%b))
            if distance > 3:
                continue
            cap, steps = CAPS[max(1, distance)], j-i
            if min(steps, b-steps)*CAPS[0] <= cap:
                continue
            forward, backward = steps*CAPS[0] < D-cap, (b-steps)*CAPS[0] < D-cap
            if forward and backward:
                raise ValueError("independent graph violates its necessary angular screen")
            mask = sum(1 << owner for owner in range(i+1, j+1))
            if forward:
                windows.add((mask, cap))
            elif backward:
                windows.add((((1 << b)-1)^mask, cap))
    return [list(row) for row in sorted(windows)]


def dual_components(case, multi):
    b, angles = case["B"], case["angle_constraints"]
    mass, gamma = [F(0)]*b, [F(0)]*b
    costs = [{degree: F(0) for degree in range(2,26)} for _ in range(b)]
    total, seen = F(0), set()
    supports = b*len(SLOPES)
    for row, encoded in case["rational_dual_weights"]:
        weight = F(encoded)
        if type(row) is not int or row in seen or not 0 <= row < supports+len(angles)+2*b or weight <= 0:
            raise ValueError("independent area dual has invalid/nonpositive weight")
        seen.add(row)
        if row < supports:
            owner, slope = divmod(row, len(SLOPES))
            mass[owner] += weight
            gamma[owner] -= weight*SLOPES[slope]
            for degree in costs[owner]:
                costs[owner][degree] += weight*F(multi["boundary_intercept_upper_integers"][degree-2][slope], C)
        elif row < supports+len(angles):
            mask, cap = angles[row-supports]
            total += weight*F(cap,D)
            for owner in range(b):
                if mask >> owner & 1:
                    gamma[owner] += weight
        elif row < supports+len(angles)+b:
            owner = row-supports-len(angles)
            gamma[owner] += weight
            total += weight*F(CAPS[0],D)
        else:
            gamma[row-supports-len(angles)-b] -= weight
    if mass != [F(1)]*b:
        raise ValueError("independent area dual lacks exact unit auxiliary mass")
    return total-min(gamma), costs


def graph_case_gate(case, b, adjacency):
    if (
        case["B"] != b or case["boundary_degrees"] != [len(row) for row in adjacency[:b]]
        or case["angle_constraints"] != bfs_windows(b, adjacency)
    ):
        raise ValueError("independent BFS/degree graph-to-case association changed")


def degree_domains(state, b):
    domains = []
    remaining = sum(interior for boundary, interior in state.pending)
    if remaining != 26-state.next_vertex:
        raise ValueError("independent partial future budget changed")
    for vertex in range(26):
        neighbors = {other for other in range(26) if state.adjacency[vertex] >> other & 1}
        minimum = max(2 if vertex < b else 3, len(neighbors))
        if vertex >= state.next_vertex:
            maximum = max((len(boundary)+interior-1 for boundary, interior in state.pending if interior), default=0)
        else:
            maximum = len(neighbors)
            for boundary, interior in state.pending:
                if vertex in boundary:
                    maximum += interior + len(set(boundary)-neighbors-{vertex})
        maximum = min(25, maximum)
        if minimum > maximum:
            raise ValueError("independent partial state has no relaxed degree completion")
        domains.append([minimum, maximum])
    return domains


def partial_dual(case, state, old, multi):
    b = case["B"]
    domains = degree_domains(state,b)
    adjacency = [{other for other in range(26) if mask >> other & 1} for mask in state.adjacency]
    if case["degree_bounds"] != domains or case["angle_constraints"] != bfs_windows(b,adjacency):
        raise ValueError("independent partial dual changed its all-completion domain")
    base, costs = dual_components(case,multi)
    nu = F(case["degree_dual"])
    total = base-nu*(150-2*b)
    for vertex, (lo,hi) in enumerate(domains):
        total += max(
            (costs[vertex][degree] if vertex < b else F(old["interior_area_upper_integers"][degree-2],C))
            +nu*degree for degree in range(lo,hi+1))
    return total


def full_prefix_partition(ref, initial, leaves):
    leaves = partition_set([list(prefix) for prefix in leaves])
    seen = set()
    def visit(prefix, state):
        if prefix in leaves:
            seen.add(prefix)
            return
        if not any(path[:len(prefix)] == prefix for path in leaves):
            raise ValueError("independent partial-area partition lost an entire sibling")
        children = ref.children(state)
        if not children:
            raise ValueError("independent partial-area leaves extend an empty source")
        for index, child in enumerate(children):
            visit(prefix+(index,),child)
    for row in initial["frontier"]:
        prefix = tuple(row["prefix"])
        visit(prefix,ref.resolve(prefix))
    if seen != leaves:
        raise ValueError("independent partial-area leaf lies outside its initial source")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--audit-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("independent initial audit requires a fresh report")
    executor_sha = binding.sha(__file__)
    if binding.sha(args.audit) != args.audit_sha256:
        raise ValueError("independent checker was not given the exact completed primary audit")
    audit = json.loads(args.audit.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    audit_gate(audit)
    reader = Reader(audit["input_sha256"])
    current_path = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
    current = reader.read(current_path)
    if binding.sha(current_path) != CURRENT_SHA:
        raise ValueError("independent checker changed the actual initial proof-time current")
    actual = {normalized(path): digest for path,digest in current["files"].items()}
    missing = {
        text:digest for text,digest in audit["input_sha256"].items()
        if normalized(text) not in actual
        and text not in (
            linux(current_path),
            linux("outputs/n26-current28-six-target-supplemental-independent-final-v1.json"),
            linux("outputs/n26-exact26-core-source-interface-audit-v2.json"))
        and "new-initial-audit-and-continuous-interface" not in audit["missing_input_roles"].get(text, [])
    }
    primary_missing = audit["historical_selected_inputs_missing_from_current_explicit_inventory"]
    if missing != primary_missing or len(missing) != audit["historical_selected_missing_count"]:
        raise ValueError("independent exact missing-prerequisite inventory differs: " + json.dumps({
            "independent_count": len(missing), "primary_count": len(primary_missing),
            "only_independent": sorted(set(missing)-set(primary_missing))[:8],
            "only_primary": sorted(set(primary_missing)-set(missing))[:8],
        }))
    summaries, native_records, graph_union, refs = [], [], set(), {}
    for b in (14,15,16,17):
        progress = reader.read(f"outputs/n26-new-B{b}-progress-v1.json")
        manifest = reader.read(progress["latest_checkpoint"])
        initial = reader.read(manifest["initial_frontier_path"])
        ref,pending,records,events = reverse_queue(manifest,initial,reader)
        refs[b] = (ref,pending,initial)
        native_records.extend(records)
        for record,data in records:
            graph_union.update((b,tuple(row["faces"])) for row in data["survivors"])
        summaries.append({"B":b,"reverse_events":dict(events),"pending":len(pending),"completed":len(records)})
        print(json.dumps({"independent_initial_queue_reversed":summaries[-1]}),flush=True)
    folder = Path("outputs/n26-multislope-area-lower-v1")
    source = reader.read(folder/"SOURCE.json")
    original_paths = {(data["B"],tuple(data["prefix"]),normalized(record["path"])) for record,data in native_records}
    copied_paths = {(row["B"],tuple(row["prefix"]),normalized(row["original_path"])) for row in source["catalogs"]}
    if original_paths != copied_paths or len(original_paths) != 14:
        raise ValueError("independent completed catalogue bijection changed")
    copied_graphs = set()
    for row in source["catalogs"]:
        data = reader.read(folder/row["filename"])
        if binding.sha(folder/row["filename"]) != binding.sha(row["original_path"]):
            raise ValueError("independent selected catalogue is not the original exact bytes")
        copied_graphs.update((row["B"],tuple(graph["faces"])) for graph in data["survivors"])
    if copied_graphs != graph_union or len(graph_union) != 13237:
        raise ValueError("independent selected graph union changed")
    old, multi = reader.read(folder/"CERTIFICATE.json"),reader.read(folder/"MULTISLOPE-CERTIFICATE.json")
    core = reader.read("outputs/n26-exact26-core-source-interface-audit-v2.json")
    if (
        binding.sha("outputs/n26-exact26-core-source-interface-audit-v2.json") != CORE_SHA
        or core["complete_base_area_envelope_recomputations"][0]["certificate_sha256"] != binding.sha(folder/"CERTIFICATE.json")
        or core["complete_multi_slope_envelope_recomputations"][0]["certificate_sha256"] != binding.sha(folder/"MULTISLOPE-CERTIFICATE.json")
    ):
        raise ValueError("independent checker lost identical completed continuous coefficient tables")
    cases = reader.read(folder/"CASE-CERTIFICATES.json")
    case_bounds = []
    for case in cases:
        base,costs = dual_components(case,multi)
        case_bounds.append(base+sum(costs[i][degree] for i,degree in enumerate(case["boundary_degrees"])))
    ledger = reader.read(folder/"MULTISLOPE-GRAPH-LEDGER.json")
    graphs = sorted(graph_union)
    if len(multi["graph_to_case"]) != len(graphs) or len(ledger) != len(graphs):
        raise ValueError("independent graph dual association is incomplete")
    for index,((b,faces),case_id) in enumerate(zip(graphs,multi["graph_to_case"])):
        validate_disk(26,b,faces)
        adjacency = adjacency_for(faces)
        graph_case_gate(cases[case_id],b,adjacency)
        boundary = case_bounds[case_id]*C
        boundary_integer = -((-boundary.numerator)//boundary.denominator)
        upper = boundary_integer+sum(old["interior_area_upper_integers"][len(adjacency[v])-2] for v in range(b,26))
        if upper >= 0 or ledger[index] != [index,case_id,upper,True]:
            raise ValueError("independent exact graph area exclusion differs from strict ledger")
        if (index+1)%3000 == 0:
            print(json.dumps({"independent_initial_graph_BFS_topology_and_duals":index+1}),flush=True)
    partial_folder = Path("outputs/n26-partial-area-closures-v1")
    cert = reader.read(partial_folder/"PARTIAL-CERTIFICATE.json")
    receipt = reader.read(partial_folder/"VERIFIED.json")
    ref,pending_native,initial = refs[14]
    excluded = partition_set([case["prefix"] for case in cert["cases"]])
    kept = partition_set(cert["expected_pending_prefixes"])
    if kept & excluded:
        raise ValueError("independent partial source paid a retained prefix")
    full_prefix_partition(ref,initial,kept|excluded)
    bounds = []
    for case in cert["cases"]:
        state = ref.resolve(tuple(case["prefix"]))
        value = partial_dual(case,state,old,multi)
        if value >= 0:
            raise ValueError("independent all-completion prefix is not strictly excluded")
        bounds.append({"prefix":case["prefix"],"area_dual_strict_upper":str(value)})
    if bounds != receipt["strict_area_bounds"]:
        raise ValueError("independent all-completion partial duals differ")
    native_closed14 = [tuple(data["prefix"]) for record,data in native_records if data["B"] == 14]
    covered = lambda prefix:any(prefix[:len(root)] == root for root in excluded)
    if (sum(map(covered,pending_native)),sum(map(covered,native_closed14))) != (20,6):
        raise ValueError("independent B14 twenty-pending/six-completed relationship changed")
    transport = reader.read("outputs/n26-current-cover-transport-frontier-v1.json")
    expected_rows = []
    for b in (14,15,16,17):
        ref,pending,initial = refs[b]
        for prefix in sorted(kept if b == 14 else pending):
            state = ref.resolve(prefix)
            expected_rows.append({"B":b,**ref.entry(prefix,state,ref.children(state))})
    if transport["pending_states"] != expected_rows or len(expected_rows) != 282:
        raise ValueError("independent original transport states differ")
    negatives = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            negatives.append(label)
        else:
            raise AssertionError("independent initial control accepted: "+label)
    changed = {**audit,"global_optimality_proved":True}
    reject("initial-binding-promoted-to-global-proof",lambda:audit_gate(changed))
    changed = deepcopy(audit)
    changed["input_sha256"].pop(next(iter(changed["input_sha256"])))
    reject("omitted-selected-prerequisite",lambda:audit_gate(changed))
    reject("duplicate-original-leaf",lambda:partition_set([[0,0],[0,0]]))
    lost = set(kept)
    lost.remove(next(iter(lost)))
    ref = refs[14][0]
    reject("missing-B14-retained-sibling",lambda:full_prefix_partition(ref,refs[14][2],lost|excluded))
    changed_case = deepcopy(cases[0])
    changed_case["rational_dual_weights"][0][1] = "-1"
    reject("negative-independent-graph-dual",lambda:dual_components(changed_case,multi))
    b,faces = graphs[0]
    changed_case = deepcopy(cases[multi["graph_to_case"][0]])
    changed_case["boundary_degrees"][0] += 1
    reject("wrong-independent-graph-degree-case",lambda:graph_case_gate(changed_case,b,adjacency_for(faces)))
    changed_case = deepcopy(cert["cases"][0])
    changed_case["degree_bounds"][0][1] += 1
    reject("changed-independent-all-completion-degree-domain",lambda:partial_dual(
        changed_case,ref.resolve(tuple(changed_case["prefix"])),old,multi))
    reader.rehash()
    if binding.sha(args.audit) != args.audit_sha256 or binding.sha(__file__) != executor_sha:
        raise ValueError("primary audit or independent executor changed during reconstruction")
    report = {
        "schema":"N26-independent-initial-source-retention-and-selected-byte-closure-v1",
        "verified":False,"new_formal_geometric_payments":0,
        "primary_audit_sha256":args.audit_sha256,"executed_checker_sha256":executor_sha,
        "actual_proof_time_current_sha256":CURRENT_SHA,
        "selected_initial_prerequisite_byte_closure_independently_rehashed":True,
        "actual_selected_dependencies_rehashed":len(reader.inventory),
        "actual_missing_original_prerequisites_independently_reconstructed":len(missing),
        "all_four_partitions_independently_reversed_to_entire_initial_frontiers":summaries,
        "all13237_graphs_topology_BFS_windows_AND_strict_exact_area_duals_independently_recomputed":True,
        "all_B14_prefix_degree_domains_max_form_duals_AND_complete_sibling_cover_independently_recomputed":len(bounds),
        "all282_original_transport_states_independently_reconstructed":True,
        "original_native_search_AND_completed_continuous_tables_QUALIFIED_REUSE_NOT_fresh_tree_or_bin_replay":True,
        "unbound_original_B14_receipt_NOT_reused_as_an_acceptance_premise":True,
        "actual_independent_negative_controls_rejected":negatives,
        "primary_audit_AND_this_independent_report_require_DISTINCT_future_current_admission":True,
        "current_formal_frontier_AND_candidate_roots_NOT_changed":True,
        "unrestricted_reduction_final_joint_acceptance":False,
        "full_catalog_complete":False,"global_lower_bound_proved":False,
        "global_optimality_proved":False,"n27_started":False,
        "input_sha256":{**audit["input_sha256"],linux(args.audit):args.audit_sha256,linux(__file__):executor_sha},
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "independent_initial_source_and_selected_byte_closure_completed_NOT_current_admission":True,
        "exact_graph_duals":13237,"all_completion_prefix_duals":len(bounds),
        "original_transport_states":282,"missing_original_prerequisites":len(missing),
        "actual_independent_rejection_controls":len(negatives),
        "global_optimality_proved":False,
    }),flush=True)


if __name__ == "__main__":
    main()
