"""Unaccepted discovery seed from every actually accepted registry tree."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from verify_selected_type_trees import bound, coverage_gate, read
from verify_terminal_catalog import local_path, sha


def main():
    parser = argparse.ArgumentParser()
    for key in ("registry", "registry-replay", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.registry)
    if read(args.registry_replay) != accepted:
        raise ValueError("registry seed needs an actual matching published replay")
    manifest = read(args.registry / "MANIFEST.json")
    pool_folder = local_path(manifest["source_pool"])
    pool, _ = bound(pool_folder)
    if (read(local_path(manifest["source_pool_replay"])) != pool
            or pool["radius_upper"] != accepted["radius_upper"]
            or pool["radius_scope"] != accepted["radius_scope"]):
        raise ValueError("discovery source proof pool changed radius or actual replay")
    table = read(args.registry / "SOURCE-CATALOG.json")
    certificate = read(args.registry / "CERTIFICATE.json")
    classification = {row["group_index"]: row for row in read(args.registry / "CLASSIFICATION.json")}
    pending = {row["group_index"]: row for row in read(args.registry / "PENDING-TYPES.json")}
    pool_trees = {row["group_index"]: row for row in read(pool_folder / "CERTIFICATE.json")["types"]}
    proposals = []
    for current in certificate["types"]:
        if current["kind"] == "REUSE":
            row = deepcopy(pool_trees[current["pool_type_index"]])
            if row["spec"] != current["spec"]:
                raise ValueError("reused seed must have the identical complete canonical spec")
            row["group_index"] = current["group_index"]
        elif current["kind"] == "TREE":
            row = {key: deepcopy(value) for key, value in current.items() if key != "kind"}
        else:
            raise ValueError("unknown accepted registry proof source")
        status = classification[row["group_index"]]
        row["replayed_discovery_counts"] = {
            "radius_at_most_Rstar_type_excluded": status["radius_at_most_Rstar_type_excluded"],
            "unresolved_closed_boxes": status["unresolved_closed_boxes"]}
        row["pending"] = deepcopy(pending[row["group_index"]]["closed_OPEN_boxes"])
        proposals.append(row)
    coverage_gate(proposals, table)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-selected-canonical-type-sharp-trees-v1",
        "verified": False, "radius_scope": accepted["radius_scope"],
        "catalog_acceptance_sha256": accepted["catalog_acceptance_sha256"],
        "cap_acceptance_sha256": pool["source_acceptance_sha256"]["caps"],
        "registry_acceptance_sha256": sha(args.registry / "VERIFIED.json"),
        "all_prior_non_OPEN_nodes_and_complete_closed_splits_included": True,
        "proposals": proposals, "all_unresolved_type_boxes_retained": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"discovery_only": True, "full_competitor_types": len(proposals),
                      "retained_OPEN_boxes": sum(len(row["pending"]) for row in proposals)}), flush=True)


if __name__ == "__main__":
    main()
