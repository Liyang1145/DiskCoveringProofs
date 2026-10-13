"""Serial checked-successor whole-leaf energy; never reset/re-pay v4 leaves."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_root25_v4_balanced_whole_leaf_energy as first
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-latest-root25-width-balanced-whole-leaf-successor-v1"
CONTROL_SCHEMA = "N26-independent-latest-root25-width-balanced-whole-leaf-successor-controls-v1"


def source(args):
    original,model,kernels,base,base_controls,row,base_pending,arcs,inventory = first.source_inputs()
    if binding.sha(args.seed) != args.seed_sha256 or binding.sha(args.seed_controls) != args.seed_controls_sha256:
        raise ValueError("latest whole-leaf continuation needs exact completed predecessor pair")
    seed,controls = binding.read(args.seed),binding.read(args.seed_controls)
    schemas = {
        first.SCHEMA:"N26-independent-root25v4-width-balanced-whole-leaf-energy-controls-v1",
        SCHEMA:CONTROL_SCHEMA,
    }
    expected = schemas.get(seed["schema"])
    if (
        expected is None or controls["schema"] != expected
        or controls["diagnosis_sha256"] != args.seed_sha256
        or seed["source_OPEN_index"] != 25 or controls["source_OPEN_index"] != 25
        or seed["actual_source_closed_box"] != row or controls["actual_source_closed_box"] != row
        or seed["source_file_sha256"] != base["source_file_sha256"]
        or controls["source_file_sha256"] != base["source_file_sha256"]
        or len(seed["pending_closed_leaf_boxes"]) != controls["remaining_OPEN_leaf_count"]
        or seed["remaining_OPEN_leaf_count"] != controls["remaining_OPEN_leaf_count"]
        or any(item["verified"] is not False or item["new_geometric_payments"] != 0
               or item["global_optimality_proved"] is not False for item in (seed,controls))
    ):
        raise ValueError("latest continuation replaced its checked arithmetic source/history")
    producer_path = Path(first.__file__) if seed["schema"] == first.SCHEMA else Path(__file__)
    tester_path = Path("work/test_root25_v4_balanced_whole_leaf_energy.py") if seed["schema"] == first.SCHEMA else Path(
        "work/test_latest_root25_balanced_whole_leaf_energy.py")
    if (
        seed["executed_producer_sha256"] != binding.sha(producer_path)
        or controls["executed_test_sha256"] != binding.sha(tester_path)
    ):
        raise ValueError("latest arithmetic predecessor producer/control executable changed")
    for record in (seed,controls):
        for text,digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("checked whole-leaf predecessor dependency changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("successor original-model dependency identity conflict")
            inventory[text] = digest
    first.mixed.retention_gate(base,seed)
    leaves = first.mixed.partition(original["matrix"],row,seed["nodes"],first.mixed.old.prior.prior.tighten,False)
    other = first.mixed.partition(original["matrix"],row,seed["nodes"],first.mixed.old.prior.prior.independently_contract,True)
    pending = [leaf for leaf in leaves if leaf["kind"] == "OPEN"]
    if leaves != other or pending != seed["pending_closed_leaf_boxes"]:
        raise ValueError("latest predecessor whole closed partition did not reconstruct")
    if set(leaf["index"] for leaf in pending)-set(leaf["index"] for leaf in base_pending):
        raise ValueError("whole-leaf predecessor introduced unsupported new source bounds")
    inventory.update({
        linux(args.seed):args.seed_sha256,linux(args.seed_controls):args.seed_controls_sha256,
        linux(__file__):binding.sha(__file__),
        linux("work/n26-width-balanced-whole-leaf-energy-continuation-proof.md"):binding.sha(
            "work/n26-width-balanced-whole-leaf-energy-continuation-proof.md"),
    })
    return original,model,kernels,seed,controls,row,pending,arcs,inventory


def main():
    parser = argparse.ArgumentParser()
    for name in ("seed","seed-controls","report"):
        parser.add_argument("--"+name,type=Path,required=True)
    parser.add_argument("--seed-sha256",required=True)
    parser.add_argument("--seed-controls-sha256",required=True)
    parser.add_argument("--limit",type=int,default=256)
    parser.add_argument("--parts",type=int,default=8)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.limit <= 4096 or not 1 <= args.parts <= 64:
        raise ValueError("latest whole-leaf continuation needs fresh bounded output")
    original,model,kernels,seed,controls,row,pending,arcs,inventory = source(args)
    by_index = {leaf["index"]:leaf for leaf in pending}
    ranking_key = "numerical_full984_ranking_NOT_a_lower_bound"
    ranking = seed[ranking_key]
    selected = [item for item in ranking if item["actual_OPEN_leaf_index"] in by_index][:args.limit]
    if not selected:
        raise ValueError("latest whole-leaf continuation has no retained source target")
    nodes,ledger = deepcopy(seed["nodes"]),deepcopy(seed["arithmetic_ledger"])
    results,new = [],[]
    print(json.dumps({
        "actual_checked_predecessor_pair_used":True,"prior_OPEN":len(pending),
        "previously_proved_whole_leaves_NOT_repaid":984-len(pending),
        "fresh_selected_whole_leaves":len(selected),
        "formal_geometric_payments":0,
    }),flush=True)
    for number,rank in enumerate(selected,1):
        leaf = by_index[rank["actual_OPEN_leaf_index"]]
        lo,hi = list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))
        reference = [(a+b)/2 for a,b in zip(lo,hi)]
        first.suggestion.exact.full.hull.quadratic.reference_gate(reference,lo,hi,original["matrix"])
        support = rank["suggested_existing_full_support_index"]
        certificate,result,numerical = first.suggestion.suggest(
            kernels[support],original["matrix"],lo,hi,reference,original["radius"],arcs,args.parts)
        strict = result is not None and result["arithmetic_strict_target_test_passed"] is True
        item = {
            "actual_prior_OPEN_leaf":leaf,"full_support_index":support,
            "certificate":certificate,"arithmetic_result":result,
            "numerical_suggestions_NOT_proofs":numerical,"entire_actual_prior_OPEN_leaf_strict":strict,
        }
        results.append(item)
        if strict:
            if nodes[leaf["index"]] != {"kind":"OPEN"}:
                raise ValueError("latest continuation would re-pay a prior strict whole leaf")
            nodes[leaf["index"]] = {
                "kind":first.mixed.KIND,"full_support_index":support,"certificate":certificate}
            ledger.append({**leaf,"kind":first.mixed.KIND,"full_support_index":support,
                           "certificate":certificate,"arithmetic_result":result})
            new.append(item)
        if number%8 == 0 or number == len(selected):
            print(json.dumps({
                "fresh_whole_leaf_checks":number,"of":len(selected),"new_strict_whole_leaves":len(new),
                "current_leaf":leaf["index"],"current_leaf_strict":strict,
                "remaining_OPEN_if_all_checks_finish_now":len(pending)-len(new),
                "formal_geometric_payments":0,
            }),flush=True)
    ledger.sort(key=lambda leaf:leaf["index"])
    remaining = [leaf for leaf in pending if nodes[leaf["index"]] == {"kind":"OPEN"}]
    record = {
        "nodes":nodes,"alternative_supports":seed["alternative_supports"],
        "full134rod_supports":seed["full134rod_supports"],"arithmetic_ledger":ledger,
    }
    retained = first.mixed.retention_gate(seed,record)
    if len(remaining)+len(new) != len(pending):
        raise ValueError("latest whole-leaf successor lost an unpaid source")
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("latest whole-leaf successor input changed during arithmetic")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"actual_source_closed_box":row,
        "source_file_sha256":seed["source_file_sha256"],
        "actual_original_root25v4_sha256":first.SEED_SHA,
        "actual_proof_time_current_sha256":first.CURRENT_SHA,
        "actual_checked_predecessor_diagnosis":linux(args.seed),
        "actual_checked_predecessor_controls":linux(args.seed_controls),
        "actual_checked_predecessor_sha256":args.seed_sha256,
        "actual_checked_predecessor_controls_sha256":args.seed_controls_sha256,
        "prior_OPEN_leaf_count":len(pending),"new_exact_strict_whole_old_OPEN_leaf_count":len(new),
        "remaining_OPEN_leaf_count":len(remaining),
        "total_strict_whole_original_v4_OPEN_leaves":984-len(remaining),
        "all_actual_attempts":results,"new_exact_strict_whole_old_OPEN_leaves":new,
        **record,"pending_closed_leaf_boxes":remaining,
        "immutable_checked_predecessor_node_support_and_strict_ledger_retention":list(retained),
        ranking_key:ranking,
        "unchanged_prior_arithmetic_explicitly_REUSED_NOT_fresh_all_old_leaf_replays":True,
        "fresh_original_source_model_and_all_new_whole_leaf_arithmetic_recomputed":True,
        "no_new_split_or_proper_subbox_relabelled_as_whole_old_OPEN_leaf":True,
        "all_unselected_and_failed_prior_OPEN_domains_retained":True,
        "new_independent_arithmetic_AND_retention_controls_STILL_required":True,
        "entire_latest_source_model_history_geometry_admission_NOT_performed":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "latest_checked_successor_whole_leaf_arithmetic_completed_NOT_geometry_admission":True,
        "new_whole_leaves":len(new),"remaining_OPEN":len(remaining),
        "total_strict_whole_original_v4_OPEN_leaves":984-len(remaining),
        "global_optimality_proved":False,
    }),flush=True)


if __name__ == "__main__":
    main()
