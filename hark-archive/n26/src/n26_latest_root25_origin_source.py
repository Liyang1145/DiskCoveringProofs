"""Fresh actual model and checked920-OPEN source for NEW origin arithmetic.

Original input reconstruction, exact mode/source identities and complete
closed domain retention; NOT full later geometry/current-source admission.
"""

from pathlib import Path

from audit_prefix_partition import linux
import probe_root25_v4_balanced_whole_leaf_energy as original_source
import verify_conditional_force_stage as binding


SEED = Path("outputs/n26-root25-balanced-whole-leaf-successor-v2.json")
CONTROLS = Path("outputs/n26-root25-balanced-whole-leaf-successor-independent-controls-v2.json")
SEED_SHA = "7fd490f90fcf38bec2dafb8fd1c9a87312c1aab21013724ff718da1f09740d7a"
CONTROL_SHA = "49cd01453a0277b14ad02f323c0dc15bdbd7f4c4a14a6d93bd399f56dab46eca"


def source():
    original,model,kernels,v4,v4_controls,row,old_pending,arcs,inventory = original_source.source_inputs()
    if binding.sha(SEED) != SEED_SHA or binding.sha(CONTROLS) != CONTROL_SHA:
        raise ValueError("origin arithmetic changed the latest independently checked920-OPEN pair")
    seed,controls = binding.read(SEED),binding.read(CONTROLS)
    if (
        seed["schema"] != "N26-unaccepted-latest-root25-width-balanced-whole-leaf-successor-v1"
        or controls["schema"] != "N26-independent-latest-root25-width-balanced-whole-leaf-successor-controls-v1"
        or controls["diagnosis_sha256"] != SEED_SHA
        or seed["actual_source_closed_box"] != row or controls["actual_source_closed_box"] != row
        or seed["source_file_sha256"] != v4["source_file_sha256"]
        or controls["source_file_sha256"] != v4["source_file_sha256"]
        or seed["remaining_OPEN_leaf_count"] != 920 or controls["remaining_OPEN_leaf_count"] != 920
        or seed["total_strict_whole_original_v4_OPEN_leaves"] != 64
        or any(item["verified"] is not False or item["new_geometric_payments"] != 0
               or item["global_optimality_proved"] is not False for item in (seed,controls))
    ):
        raise ValueError("origin arithmetic reset/relabelled actual checked successor/source")
    for record in (seed,controls):
        for text,digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("origin checked predecessor input changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("origin original-model/predecessor dependency identity conflict")
            inventory[text] = digest
    original_source.mixed.retention_gate(v4,seed)
    leaves = original_source.mixed.partition(
        original["matrix"],row,seed["nodes"],original_source.mixed.old.prior.prior.tighten,False)
    other = original_source.mixed.partition(
        original["matrix"],row,seed["nodes"],original_source.mixed.old.prior.prior.independently_contract,True)
    pending = [leaf for leaf in leaves if leaf["kind"] == "OPEN"]
    if leaves != other or pending != seed["pending_closed_leaf_boxes"] or len(pending) != 920:
        raise ValueError("actual complete920-OPEN domain partition did not reconstruct")
    inventory.update({linux(SEED):SEED_SHA,linux(CONTROLS):CONTROL_SHA,linux(__file__):binding.sha(__file__)})
    return original,model,kernels,seed,controls,row,pending,arcs,inventory
