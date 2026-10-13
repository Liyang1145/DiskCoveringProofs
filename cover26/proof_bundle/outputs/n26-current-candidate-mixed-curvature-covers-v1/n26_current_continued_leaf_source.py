"""Semantic replay of the actually accepted continued candidate leaf tree."""

from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import load_trig
import n26_current_leaf_angle_source as original
import verify_continued_leaf_angles as continuation


def input_gate(source_folder, old_leaf_folder, correlated, sharp, historical, pinning_basis,
               stress, local, transport, pinning, caps):
    values = original.input_gate(old_leaf_folder, correlated, sharp, historical, pinning_basis,
                                 stress, local, transport, pinning, caps)
    accepted, inventory = original.leaf.bound(source_folder)
    inventory.extend(values["inventory"])
    for module in (original, continuation, original.leaf):
        name = Path(module.__file__).name
        if original.leaf.sha(module.__file__) != accepted["files"][name]:
            raise ValueError("continued candidate loader imported different sealed arithmetic")
    proposal = json.loads((source_folder / "PROPOSAL.json").read_text(encoding="utf-8"))
    continuation.proposal_gate(values["source"], old_leaf_folder, proposal)
    nodes, result, pending, ledger, empty, local_paid = continuation.replay_and_close(
        values, proposal, load_trig(source_folder)[0])
    sources = {
        "starting_partition": original.leaf.sha(old_leaf_folder / "VERIFIED.json"),
        "pinning_reference": original.leaf.sha(pinning / "VERIFIED.json"),
        "sharp_caps": original.leaf.sha(caps / "VERIFIED.json"),
        "stress": original.leaf.sha(stress / "VERIFIED.json"),
        "local": original.leaf.sha(local / "VERIFIED.json"),
        "transport": original.leaf.sha(transport / "VERIFIED.json")}
    certificate = {"schema": "N26-continued-leaf-pinned-closed-angular-tree-v1",
                   "radius_scope": "same-root-Rstar", "spec": values["source"]["spec"],
                   "source_acceptance_sha256": sources, "nodes": nodes}
    if (certificate != json.loads((source_folder / "CERTIFICATE.json").read_text(encoding="utf-8"))
            or pending != json.loads((source_folder / "PENDING-ANGLES.json").read_text(encoding="utf-8"))
            or ledger != json.loads((source_folder / "LOWER-LEDGER.json").read_text(encoding="utf-8"))
            or any(accepted[key] != value for key, value in result.items())
            or empty != accepted["automatically_paid_sharp_empty_indices"]
            or local_paid != accepted["automatically_paid_sharp_local_indices"]
            or accepted["source_acceptance_sha256"] != sources):
        raise ValueError("accepted continued candidate tree did not semantically replay")
    original.leaf.lineage_gate(values["source"]["nodes"], nodes)
    tiny = [tuple(map(F, row)) for row in values["cap"]["known_candidate_tiny_angle_cells"]]
    retained = any(row["kind"] in ("LOCAL", "SHARP_LOCAL") and all(
        F(a) <= x <= y <= F(b) for a, b, (x, y) in zip(
            row.get("sharp_lower", row["lower"]), row.get("sharp_upper", row["upper"]), tiny))
        for row in ledger)
    if (not retained or not accepted["known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf"]
            or F(result["leaf_specific_pinning_maximum_center_error_upper"]) >= F(7, 800000)):
        raise ValueError("continued candidate source lost its exact root or unchanged local entry allowance")
    inventory.extend([Path(__file__), Path(original.__file__), Path(continuation.__file__)])
    return {**values, "source": certificate, "accepted": accepted, "pending": pending,
            "ledger": ledger, "inventory": inventory}
