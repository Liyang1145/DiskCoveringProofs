"""Unaccepted fresh stationary-flow payments for the other twelve current types."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import load_trig
import n26_correlated_arc_force as force
from probe_retained_joint_force import RetainingJointSolver
from verify_selected_type_trees import SCOPE, bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    for key in ("source", "source-replay", "registry", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--groups", nargs="+", type=int,
                        default=[16, 17, 18, 19, 20, 21, 25, 26, 27, 30, 33, 40])
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.source)
    registry, _ = bound(args.registry)
    if (read(args.source_replay) != accepted or accepted["radius_scope"] != SCOPE
            or accepted["source_acceptance_sha256"] != sha(args.registry / "VERIFIED.json")
            or accepted["r_strict_interval"] != registry["r_strict_interval"]):
        raise ValueError("other-type force discovery needs an actual matching older source and registry")
    domains = {row["group_index"]: row["matrix"] for row in read(args.registry / "DOMAINS.json")}
    groups = {row["group_index"]: row for row in read(args.source / "PENDING-TYPES.json")}
    radius, arcs = F(accepted["radius_upper"]), load_trig(args.registry)[0]
    proposals = []
    for index in args.groups:
        group = groups[index]
        solver = RetainingJointSolver(group["spec"])
        for box in group["closed_OPEN_boxes"]:
            cached = Path(__file__).with_name(f"n26-other-type{index}-{box['index']}-hybrid-proposal-v1.json")
            if cached.exists():
                discovered = read(cached)
                if (discovered["source_acceptance_sha256"] != sha(args.source / "VERIFIED.json")
                        or discovered["spec"] != group["spec"]
                        or discovered["source_closed_OPEN_box"] != box
                        or len(discovered["nodes"]) != 1
                        or discovered["nodes"][0]["kind"] != "CORRELATED_FORCE"):
                    raise ValueError("cached single-leaf discovery does not match exact old source")
                cert = discovered["nodes"][0]["certificate"]
                diagnostic = {"reused_discovery_sha256": sha(cached)}
            else:
                result = solver.solve_retained(
                    list(map(F, box["lower"])), list(map(F, box["upper"])), domains[index], radius)
                cert = result["stationary_flow_candidate_retained_even_if_unpaid"]
                diagnostic = {"floating_joint_radius_not_a_lower_bound": result["floating_joint_radius"]}
            checked = force.force_check(group["spec"], box["lower"], box["upper"],
                                        domains[index], cert, arcs) if cert is not None else None
            paid = checked is not None and F(checked["required_radius_lower"]) > radius
            proposals.append({"group_index": index, "spec": group["spec"],
                              "source_OPEN_index": box["index"], "source_closed_OPEN_box": box,
                              "certificate": cert, "discovery_proposed_paid": paid,
                              "discovery_whole_box_force_check": checked, "diagnostic": diagnostic})
            print(json.dumps({"verified": False, "group_index": index,
                              "source_OPEN_index": box["index"], "proposed_paid": paid}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-whole-current-OPEN-correlated-force-payments-v1",
        "verified": False, "radius_scope": SCOPE, "radius_upper": str(radius),
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "source_registry_acceptance_sha256": sha(args.registry / "VERIFIED.json"),
        "groups": args.groups, "proposals": proposals,
        "all_unpaid_and_unvisited_source_OPEN_retained": True,
        "independent_current_source_lineage_and_force_acceptance_still_required": True,
        "global_optimality_proved": False,
    }, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "total_source_boxes": len(proposals),
                      "proposed_paid": sum(row["discovery_proposed_paid"] for row in proposals)}), flush=True)


if __name__ == "__main__":
    main()
