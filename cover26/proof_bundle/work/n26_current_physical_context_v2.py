"""Distinct CURRENT context for expanded physical tables; no frozen v1 edits."""

from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_physical_reuse_source as older
import verify_conditional_force_stage as binding


INITIAL, MIXED, domains, earlier = older.INITIAL, older.MIXED, older.domains, older.earlier
APPEND_SCHEMA = "N26-unaccepted-current538-checked-failed-joint-physical-support-append-v1"
APPEND_CONTROL = "N26-independent-current538-checked-failed-joint-physical-support-append-v1"
REUSE_SCHEMA = "N26-unaccepted-current-root25-expanded-physical-support-reuse-composition-v2"
REUSE_CONTROL = "N26-independent-current-root25-expanded-physical-support-reuse-composition-v2"


def arguments(parser):
    older.arguments(parser)
    parser.add_argument("--expected-supports",type=int,required=True)


def paired(args):
    if (
        binding.sha(args.seed) != args.seed_sha256 or binding.sha(args.seed_controls) != args.seed_controls_sha256
        or not 0 < args.expected_open <= 530 or not 27 <= args.expected_supports <= MIXED.MAX_FULL_SUPPORTS
    ):
        raise ValueError("expanded physical context requires an explicit exact CURRENT pair/count/table")
    seed,control = binding.read(args.seed),binding.read(args.seed_controls)
    allowed = {APPEND_SCHEMA:APPEND_CONTROL,REUSE_SCHEMA:REUSE_CONTROL}
    if (
        seed["schema"] not in allowed or control["schema"] != allowed[seed["schema"]]
        or control["diagnosis_sha256"] != args.seed_sha256
        or seed["source_OPEN_index"] != 25 or control["source_OPEN_index"] != 25
        or seed["remaining_OPEN_leaf_count"] != args.expected_open or control["remaining_OPEN_leaf_count"] != args.expected_open
        or len(seed["nodes"]) != 2999 or len(seed["arithmetic_ledger"]) != 1500-args.expected_open
        or seed["total_whole_original_v4_OPEN_leaves_excluded"] != 984-args.expected_open
        or control["total_whole_original_v4_OPEN_leaves_excluded"] != 984-args.expected_open
        or len(seed["full134rod_supports"]) != args.expected_supports
        or len(seed["fresh_joint_origin_supports"]) != 16
        or seed["nodes"][2641]["kind"] != earlier.ancestor.ancestor.NEW_ANCESTOR_KINDS[1]
        or any(item["verified"] is not False or item["new_geometric_payments"] != 0
               or item["global_lower_bound_proved"] is not False or item["global_optimality_proved"] is not False
               or item["n27_started"] is not False for item in (seed,control))
    ):
        raise ValueError("expanded physical parent changed original owner,counts,table or unpaid scope")
    if seed["schema"] == APPEND_SCHEMA:
        if control["all2999_old_domains_old19support_prefix962rows_and_origin_histories_retained"] is not True:
            raise ValueError("expanded physical initial append lacks actual independent retention")
    elif control["all_old_current_nodes_supports_and_strict_rows_retained"] is not True:
        raise ValueError("expanded physical reusable parent lacks actual independent retention")
    inventory = {}
    for record in (seed,control):
        for text,digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("expanded CURRENT parent prerequisite changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("expanded CURRENT parent prerequisite conflict")
            inventory[text] = digest
    inventory.update({linux(args.seed):args.seed_sha256,linux(args.seed_controls):args.seed_controls_sha256})
    return seed,control,inventory


def inputs(args):
    seed,control,inventory = paired(args)
    original,model,old_kernels,v4,v4_controls,row,old_pending,arcs,original_inventory = INITIAL.source_inputs()
    if seed["actual_source_closed_box"] != row or seed["source_file_sha256"] != v4["source_file_sha256"]:
        raise ValueError("expanded CURRENT source does not bind fresh original26 physical model")
    MIXED.retention_gate(v4,seed)
    for text,digest in original_inventory.items():
        if text in inventory and inventory[text] != digest:
            raise ValueError("expanded original-model digest conflict")
        inventory[text] = digest
    if seed["full134rod_supports"][:3] != v4["full134rod_supports"]:
        raise ValueError("expanded CURRENT source replaced original full134 support prefix")
    for i,donor in enumerate(seed["fresh_joint_origin_supports"]):
        if seed["full134rod_supports"][3+i]["kernel_certificate"] != donor["base_kernel_certificate"]:
            raise ValueError("expanded CURRENT source changed old physical/origin donor binding")
    view = [{"kind":"OPEN"} if node["kind"] in earlier.ORIGIN_KINDS else deepcopy(node) for node in seed["nodes"]]
    leaves = MIXED.partition(original["matrix"],row,view,MIXED.old.prior.prior.tighten,False)
    actual,parents = domains.all_domains(original,row,seed["nodes"])
    for leaf in leaves:
        i = leaf["index"]
        leaf["kind"] = seed["nodes"][i]["kind"]
        if actual[i] is not None and actual[i] != (list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("expanded CURRENT full independent closed domains differ")
    pending = [leaf for leaf in leaves if leaf["kind"] == "OPEN"]
    paid = {leaf["index"] for leaf in leaves if leaf["kind"] not in ("OPEN","EMPTY")}
    if pending != seed["pending_closed_leaf_boxes"] or len(pending) != args.expected_open or paid != {
        leaf["index"] for leaf in seed["arithmetic_ledger"]}:
        raise ValueError("expanded CURRENT source lost old proof or unpaid domain")
    supports = seed["full134rod_supports"]
    kernels = MIXED.full_support_gate(model,supports)
    references = [list(map(F,item["suggestion_point_turns"])) for item in supports]
    inventory.update({linux(__file__):binding.sha(__file__),linux(domains.__file__):binding.sha(domains.__file__)})
    return original,model,seed,control,row,pending,supports,kernels,references,arcs,inventory


def ownership(record,seed,pending):
    by_index = {leaf["index"]:leaf for leaf in pending}
    seen,strict = set(),set()
    for item in record["actual_current_whole_leaf_trials"]:
        leaf,trials = item["actual_current_whole_OPEN_leaf"],item["actual_physical_support_trials"]
        index = leaf["index"]
        if index in seen or by_index.get(index) != leaf or seed["nodes"][index] != {"kind":"OPEN"} or not trials:
            raise ValueError("expanded physical target repeated,clipped,paid or from an ancestor")
        seen.add(index)
        proofs = []
        for trial in trials:
            support,result = trial["full_support_index"],trial["arithmetic_result"]
            if type(support) is not int or not 0 <= support < len(seed["full134rod_supports"]):
                raise ValueError("expanded physical target has unbound support")
            proved = result is not None and result["arithmetic_strict_target_test_passed"] is True
            if trial["strict_entire_physical_leaf"] != proved:
                raise ValueError("expanded physical target changed actual strict/failed class")
            if proved:
                if (
                    trial["certificate"] is None or trial["certificate"]["schema"] != earlier.suggestion.exact.SCHEMA
                    or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0
                    or any(key in trial["certificate"] for key in ("origin_center_label","origin_multiplier"))
                ):
                    raise ValueError("expanded target lacks whole PHYSICAL strict certificate")
                proofs.append(trial)
        selected = item["selected_strict_physical_proof"]
        if item["strict_whole_physical_leaf"] != bool(proofs) or (selected is not None) != bool(proofs) or selected is not None and selected not in proofs:
            raise ValueError("expanded physical target strict subset differs")
        if proofs:
            strict.add(index)
    if (
        record["new_strict_whole_leaf_indices"] != sorted(strict)
        or record["prospective_remaining_OPEN_after_independent_join"] != len(pending)-len(strict)
        or record["old_current_nodes_supports_and_strict_rows_UNMODIFIED"] is not True
    ):
        raise ValueError("expanded physical whole-target count/retention differs")
    return strict
