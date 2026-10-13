"""Actual original model and newest root25v4 harmonic LOCAL diagnostics.

Fresh original reference geometry and inverse, never a typed source capsule.
Does not change a forest or make a geometric/current payment.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_effective_resistance_local_entry as harmonic
import n26_full_candidate_face_energy as full
import n26_mixed_full134rod_support_forest as mixed
import n26_sharp_radius_constraints as sharp
import verify_conditional_force_stage as binding


CURRENT = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
FINAL = Path("outputs/n26-current28-six-target-supplemental-independent-final-v1.json")
REFERENCE = Path("outputs/n26-leaf-pinned-candidate-angles-v2/REFERENCE-PINNING.json")
INVERSE = Path("outputs/n26-current-candidate-Dirichlet-overlay-v1/DIRICHLET-KERNEL.json")
CAP = Path("outputs/n26-current-partial-prefix-energy-v1/CAP-CERTIFICATE.json")
SEED = Path("outputs/n26-candidate-root25-preserved-full134rod-regions-forest-diagnosis-v4.json")
SEED_CONTROL = Path("outputs/n26-candidate-root25-preserved-full134rod-regions-independent-controls-v1.json")
CURRENT_SHA = "c85e130c935e68e2275e53fa457c9c4d95d8be5416b128f4307a76061057911b"
SEED_SHA = "4914725c65f3995014a30484f2e4a37428701efe02bbed2edce98f70d96626cc"
CONTROL_SHA = "a9c80ec8bcf6d2d861cbab828e2c3d150d7a230b8a4cef78e5801d651b29a7d0"


def inputs():
    current,final = binding.read(CURRENT),binding.read(FINAL)
    if (
        binding.sha(CURRENT) != CURRENT_SHA or final["current_audit_sha256"] != CURRENT_SHA
        or final["all_current_file_digests_rehashed"] is not True
        or current["candidate_angle_unresolved_closed_boxes"] != 25
        or current["global_optimality_proved"] is not False
    ):
        raise ValueError("harmonic LOCAL diagnostic lost actual accepted current/final ownership")
    selected = [CURRENT,FINAL,REFERENCE,INVERSE,CAP,SEED,SEED_CONTROL]
    for path in (REFERENCE,INVERSE,CAP):
        if current["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("harmonic LOCAL diagnostic original reference/kernel/caps not current-bound")
    if binding.sha(SEED) != SEED_SHA or binding.sha(SEED_CONTROL) != CONTROL_SHA:
        raise ValueError("harmonic LOCAL diagnostic reset the actual root25v4 history")
    seed,control = binding.read(SEED),binding.read(SEED_CONTROL)
    if (
        control["diagnosis_sha256"] != SEED_SHA or seed["source_OPEN_index"] != 25
        or seed["verified"] is not False or control["verified"] is not False
        or seed["new_geometric_payments"] != 0 or control["new_geometric_payments"] != 0
        or len(seed["pending_closed_leaf_boxes"]) != 984
    ):
        raise ValueError("harmonic LOCAL diagnostic changed unadmitted arithmetic history scope")
    reference,inverse = binding.read(REFERENCE),binding.read(INVERSE)
    stress = Path("outputs/n26-positive-stress-v1")
    local = Path("outputs/n26-centered-local-barrier-v2")
    transport = Path("outputs/n26-candidate-transport-control-v1")
    # This reconstructs the actual source geometry/reference inputs. It does
    # NOT replay every later candidate forest or call a current source cache.
    data = harmonic.base.source_gate(stress,local,transport,reference)
    selected.extend(data[5])
    prepared = harmonic.prepare(*data[:5],reference,inverse)
    model = full.model_gate(data[0],reference,data[3])
    cap = binding.read(CAP)
    radius = F(current["r_strict_interval"][1])
    caps,_ = sharp.cap_gate(radius,cap,harmonic.base.arcs)
    terminal = data[3]["states"][-1]
    spec = {"N":26,"B":16,"next":26,"faces":terminal["faces"]}
    matrix,_ = sharp.constraint_matrix(spec,caps)
    if matrix is None:
        raise ValueError("actual known candidate source lost its necessary sharp domain")
    owner = Path("outputs/n26-current-candidate-owned-forest-v8")
    accepted = binding.read(owner/"VERIFIED.json")
    for name,digest in seed["source_file_sha256"].items():
        path = owner/name
        if binding.sha(path) != digest or accepted["files"][name] != digest:
            raise ValueError("harmonic LOCAL diagnostic changed the retained actual candidate owner")
        selected.append(path)
    selected.append(owner/"VERIFIED.json")
    row = next(item for item in binding.read(owner/"PENDING-ANGLES.json") if item["index"] == 25)
    if row != seed["actual_source_closed_box"]:
        raise ValueError("harmonic LOCAL diagnostic clipped its actual whole source root")
    parts = mixed.partition(matrix,row,seed["nodes"],mixed.old.prior.prior.tighten,False)
    other = mixed.partition(matrix,row,seed["nodes"],mixed.old.prior.prior.independently_contract,True)
    pending = [leaf for leaf in parts if leaf["kind"] == "OPEN"]
    if parts != other or pending != seed["pending_closed_leaf_boxes"]:
        raise ValueError("fresh original model did not reconstruct all actual root25v4 closed leaf domains")
    modules = (
        harmonic, harmonic.original_pin, harmonic.base, harmonic.energy,
        harmonic.energy.dirichlet, full, mixed, sharp,
    )
    for module in modules:
        selected.append(Path(module.__file__))
    selected.extend((
        Path(harmonic.base.iv.__file__),Path(harmonic.base.geo.__file__),
        Path(harmonic.base.arcs.__file__),
        Path("work/n26-effective-resistance-local-entry-proof.md"),Path(__file__),
    ))
    inventory = {linux(path):binding.sha(path) for path in selected}
    return prepared,seed,control,pending,cap,model,inventory


def root_hull(leaf,tiny):
    return [
        [str(min(F(a),F(x))),str(max(F(b),F(y)))]
        for a,b,(x,y) in zip(leaf["lower"],leaf["upper"],tiny)
    ]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve harmonic LOCAL arithmetic evidence")
    prepared,seed,control,pending,cap,model,inventory = inputs()
    print(json.dumps({
        "fresh_original92rod_reference_and_exact46ground_inverse_reconstructed":True,
        "independent_actual134rod_source_bijection_also_checked_NOT_used_for_LOCAL":True,
        "actual_root25v4_OPEN_domains_reconstructed":len(pending),
        "minimum_path_over_effective_resistance_ratio":float(min(
            prepared["old_path_resistance"][16+i]/value
            for i,value in enumerate(prepared["effective_resistance"]))),
    }),flush=True)
    tiny = cap["known_candidate_tiny_angle_cells"]
    middle = [(F(a)+F(b))/2 for a,b in tiny]
    calibration = []
    for numerator in (1,2,3,5,8,10,15,20,30,50,80,100):
        width = F(numerator,10**8)
        cells = [
            [str(min(m-width,F(a))),str(max(m+width,F(b)))]
            for m,(a,b) in zip(middle,tiny)
        ]
        result = harmonic.evaluate(prepared,cells)
        calibration.append({"proposed_symmetric_halfwidth":str(width),"result":result})
        print(json.dumps({
            "harmonic_LOCAL_halfwidth_trial":str(width),
            "old_path_max_error":float(F(result["same_cells_old_path_pin_maximum_center_error_upper"])),
            "new_harmonic_max_error":float(F(result["maximum_original_center_error_upper"])),
            "old_passes":result["same_cells_old_path_pin_enters_original_LOCAL"],
            "new_passes":result["arithmetic_entire_closed_box_enters_original_LOCAL"],
        }),flush=True)
    leaves,new_payable,old_payable,invalid = [],[],[],0
    for number,leaf in enumerate(pending,1):
        cells = root_hull(leaf,tiny)
        try:
            result = harmonic.evaluate(prepared,cells)
        except ValueError as error:
            invalid += 1
            leaves.append({"leaf_index":leaf["index"],"not_LOCAL_payable":True,"retained_reason":str(error)})
        else:
            new = result["arithmetic_entire_closed_box_enters_original_LOCAL"]
            old = result["same_cells_old_path_pin_enters_original_LOCAL"]
            leaves.append({
                "leaf_index":leaf["index"],"new_LOCAL_arithmetic_passed":new,
                "old_path_LOCAL_arithmetic_passed":old,
                "new_maximum_center_error_upper":result["maximum_original_center_error_upper"],
                "old_maximum_center_error_upper":result["same_cells_old_path_pin_maximum_center_error_upper"],
            })
            if new:
                new_payable.append({"actual_root25v4_OPEN_leaf":leaf,"result":result})
            if old:
                old_payable.append(leaf["index"])
        if number%100 == 0:
            print(json.dumps({"actual_root25v4_OPEN_harmonic_LOCAL_checks":number,
                              "of":len(pending),"new_arithmetic_LOCAL":len(new_payable)}),flush=True)
    improved = [row for row in calibration if
                row["result"]["arithmetic_entire_closed_box_enters_original_LOCAL"]
                and not row["result"]["same_cells_old_path_pin_enters_original_LOCAL"]]
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("harmonic LOCAL original input changed during arithmetic")
    report = {
        "schema":"N26-unaccepted-actual-original92rod-harmonic-LOCAL-strengthening-diagnostic-v1",
        "verified":False,"new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "actual_proof_time_current_sha256":CURRENT_SHA,
        "actual_root25v4_diagnosis_sha256":SEED_SHA,
        "actual_root25v4_independent_controls_sha256":CONTROL_SHA,
        "fresh_original_reference_root_geometry_positive_rods_and_exact_inverse_reconstructed":True,
        "full134rod_model_independently_checked_but_NOT_relabelled_as_original_LOCAL":True,
        "no_typed_context_or_diagnostic_model_cache_imported":True,
        "actual_all984_latest_root25v4_OPEN_domains_freshly_reconstructed":True,
        "all46_effective_resistances_below_explicit_positive_path_bounds":True,
        "calibration_actual_closed_root_hulls":calibration,
        "new_closed_LOCAL_hulls_not_payable_by_old_path_bound":len(improved),
        "all984_actual_root25v4_OPEN_LOCAL_tests":leaves,
        "actual_latest_OPEN_leaf_NEW_LOCAL_arithmetic_witnesses":new_payable,
        "actual_latest_OPEN_leaf_NEW_LOCAL_arithmetic_count":len(new_payable),
        "actual_latest_OPEN_leaf_old_path_LOCAL_arithmetic_indices":old_payable,
        "actual_latest_OPEN_hulls_failing_original_short_arc_interface_retained":invalid,
        "all_old_nodes_supports_strict_ledgers_and_OPEN_states_UNMODIFIED":True,
        "original52_coordinate_LOCAL_allowance_unchanged":"7/800000",
        "independent_effective_resistance_and_LOCAL_arithmetic_controls_STILL_required":True,
        "ENTIRE_latest_source_model_history_geometry_admission_NOT_performed":True,
        "unrestricted_reduction_final_joint_acceptance":False,
        "full_catalog_complete":False,"global_lower_bound_proved":False,
        "global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "actual_harmonic_LOCAL_arithmetic_scan_completed_NOT_geometry_admission":True,
        "new_calibration_closed_hulls_not_old_path_LOCAL":len(improved),
        "actual_root25v4_OPEN_leaves_NEW_LOCAL":len(new_payable),
        "old_path_LOCAL":len(old_payable),"all984_old_OPEN_leaves_UNMODIFIED":True,
        "global_optimality_proved":False,
    }),flush=True)


if __name__ == "__main__":
    main()
