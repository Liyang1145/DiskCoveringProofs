"""Distinct current reader for honest physical-table append with origin proofs."""

from copy import deepcopy
from fractions import Fraction as F

from audit_prefix_partition import linux
import n26_current_physical_context_v2 as prior
import verify_conditional_force_stage as binding


INITIAL,MIXED,domains,earlier = prior.INITIAL,prior.MIXED,prior.domains,prior.earlier
APPEND_SCHEMA = "N26-unaccepted-current-root25-checked-missing-origin-owner-support-append-v1"
APPEND_CONTROL = "N26-independent-current-root25-checked-missing-origin-owner-support-append-v1"
KIND = "FULL134-TWO-ORIGIN-BRANCHES-ENERGY"


def arguments(parser):
    prior.arguments(parser)


def inventory_gate(inventory):
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("origin append current prerequisite changed: "+text)


def unpaid(record):
    if (record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or any(record[field] is not False for field in
                   ("global_lower_bound_proved","global_optimality_proved","n27_started"))):
        raise ValueError("origin append arithmetic evidence promoted to geometry/global proof")


def paired(args):
    if (
        binding.sha(args.seed) != args.seed_sha256 or binding.sha(args.seed_controls) != args.seed_controls_sha256
        or not 0 < args.expected_open <= 530 or not 27 <= args.expected_supports <= MIXED.MAX_FULL_SUPPORTS
    ):
        raise ValueError("explicit completed current origin append pair and actual counts required")
    seed,controls = binding.read(args.seed),binding.read(args.seed_controls)
    allowed = {prior.APPEND_SCHEMA:prior.APPEND_CONTROL,prior.REUSE_SCHEMA:prior.REUSE_CONTROL,
               APPEND_SCHEMA:APPEND_CONTROL}
    for record in (seed,controls):
        unpaid(record)
    if (
        seed["schema"] not in allowed or controls["schema"] != allowed[seed["schema"]]
        or controls["diagnosis_sha256"] != args.seed_sha256
        or seed["source_OPEN_index"] != 25 or controls["source_OPEN_index"] != 25
        or seed["remaining_OPEN_leaf_count"] != args.expected_open or controls["remaining_OPEN_leaf_count"] != args.expected_open
        or len(seed["nodes"]) != 2999 or len(seed["arithmetic_ledger"]) != 1500-args.expected_open
        or seed["total_whole_original_v4_OPEN_leaves_excluded"] != 984-args.expected_open
        or controls["total_whole_original_v4_OPEN_leaves_excluded"] != 984-args.expected_open
        or len(seed["full134rod_supports"]) != args.expected_supports or len(seed["fresh_joint_origin_supports"]) != 16
        or seed["nodes"][2641]["kind"] != earlier.ancestor.ancestor.NEW_ANCESTOR_KINDS[1]
    ):
        raise ValueError("origin append current pair changed original owner,domains,table or accounting")
    if seed["schema"] == prior.APPEND_SCHEMA:
        if controls["all2999_old_domains_old19support_prefix962rows_and_origin_histories_retained"] is not True:
            raise ValueError("old checked physical append lost actual retention")
    elif controls["all_old_current_nodes_supports_and_strict_rows_retained"] is not True:
        raise ValueError("current origin append pair lacks actual complete independent retention")
    if seed["schema"] == APPEND_SCHEMA and (
        controls["actual_current_support_count"] != args.expected_supports
        or controls["all_old_physical_prefix_and_origin_donors_unchanged_only_selected_new_bases_appended"] is not True
        or controls["BOTH_whole_actual_origin_branches_checked_before_each_new_payment"] is not True
    ):
        raise ValueError("new origin append pair lost its honest support/owner semantics")
    inventory = {}
    for record in (seed,controls):
        inventory_gate(record["input_sha256"])
        for text,digest in record["input_sha256"].items():
            if text in inventory and inventory[text] != digest:
                raise ValueError("current origin append prerequisite conflict")
            inventory[text] = digest
    inventory.update({linux(args.seed):args.seed_sha256,linux(args.seed_controls):args.seed_controls_sha256})
    return seed,controls,inventory


def inputs(args):
    seed,controls,inventory = paired(args)
    original,model,old_kernels,v4,v4_controls,row,old_pending,arcs,old_inventory = INITIAL.source_inputs()
    if seed["actual_source_closed_box"] != row or seed["source_file_sha256"] != v4["source_file_sha256"]:
        raise ValueError("origin append current pair does not bind the freshly reconstructed original model")
    MIXED.retention_gate(v4,seed)
    for text,digest in old_inventory.items():
        if text in inventory and inventory[text] != digest:
            raise ValueError("origin append original model/current digest conflict")
        inventory[text] = digest
    if seed["full134rod_supports"][:3] != v4["full134rod_supports"]:
        raise ValueError("origin append original physical support prefix changed")
    for index,donor in enumerate(seed["fresh_joint_origin_supports"]):
        if seed["full134rod_supports"][3+index]["kernel_certificate"] != donor["base_kernel_certificate"]:
            raise ValueError("origin append historical16origin/physical donor bindings changed")
    view = [{"kind":"OPEN"} if node["kind"] in earlier.ORIGIN_KINDS else deepcopy(node) for node in seed["nodes"]]
    leaves = MIXED.partition(original["matrix"],row,view,MIXED.old.prior.prior.tighten,False)
    actual,parents = domains.all_domains(original,row,seed["nodes"])
    for leaf in leaves:
        index = leaf["index"]
        leaf["kind"] = seed["nodes"][index]["kind"]
        if actual[index] is not None and actual[index] != (list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("origin append independently reconstructed entire domains differ")
    pending = [leaf for leaf in leaves if leaf["kind"] == "OPEN"]
    paid = {leaf["index"] for leaf in leaves if leaf["kind"] not in ("OPEN","EMPTY")}
    if pending != seed["pending_closed_leaf_boxes"] or len(pending) != args.expected_open or paid != {
            leaf["index"] for leaf in seed["arithmetic_ledger"]}:
        raise ValueError("origin append lost an old proof or an unproved whole source domain")
    supports = seed["full134rod_supports"]
    kernels = MIXED.full_support_gate(model,supports)
    references = [list(map(F,support["suggestion_point_turns"])) for support in supports]
    inventory.update({linux(__file__):binding.sha(__file__),linux(domains.__file__):binding.sha(domains.__file__)})
    return original,model,seed,controls,row,pending,supports,kernels,references,arcs,inventory
