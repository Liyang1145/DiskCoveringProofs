"""Map discovery trees by full canonical face code, never by group number."""

import argparse
import json
from pathlib import Path

from n26_force import load_trig
from n26_sharp_radius_constraints import cap_gate, constraint_matrix
from n26_sharp_type_tree import replay
from fractions import Fraction as F
from verify_selected_type_trees import SCOPE, bound, read
import verify_terminal_catalog as catalog


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--old-catalog", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--seed", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    for folder in (args.catalog, args.old_catalog, args.caps):
        bound(folder)
    values = catalog.input_gate(args.catalog)
    table = catalog.reconstruct(args.catalog, *values[1:])
    seed, cap, arcs = read(args.seed), read(args.caps / "CERTIFICATE.json"), load_trig(args.caps)[0]
    if (seed["radius_scope"] != SCOPE
            or seed["catalog_acceptance_sha256"] != catalog.sha(args.old_catalog / "VERIFIED.json")
            or seed["cap_acceptance_sha256"] != catalog.sha(args.caps / "VERIFIED.json")):
        raise ValueError("expanded discovery seed changed old graph or radius source")
    caps, _ = cap_gate(F(cap["radius_upper"]), cap, arcs)
    old = {(row["spec"]["B"], tuple(row["spec"]["faces"])): row for row in seed["proposals"]}
    if len(old) != len(seed["proposals"]):
        raise ValueError("old discovery has duplicate full canonical types")
    proposals, transfers, fresh = [], [], []
    for index, group in enumerate(table["groups"]):
        if any(table["rows"][j]["same_canonical_type_as_known_candidate"] for j in group["member_indices"]):
            continue
        previous = old.get((group["B"], tuple(group["canonical_faces"])))
        if previous is None:
            fresh.append(index)
            continue
        spec = {"N": 26, "B": group["B"], "next": 26, "faces": group["canonical_faces"]}
        if spec != previous["spec"]:
            raise ValueError("expanded canonical code has a different full rod complex")
        matrix = constraint_matrix(spec, caps)[0]
        result, pending, _ = replay(spec, matrix, F(cap["radius_upper"]), previous["nodes"], arcs)
        proposals.append({**previous, "group_index": index,
                          "replayed_discovery_counts": result, "pending": pending})
        transfers.append({"new_group_index": index, "old_discovery_group_index": previous["group_index"],
                          "identical_full_canonical_spec": True})
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-selected-canonical-type-sharp-trees-v1", "verified": False,
        "catalog_acceptance_sha256": catalog.sha(args.catalog / "VERIFIED.json"),
        "cap_acceptance_sha256": catalog.sha(args.caps / "VERIFIED.json"),
        "radius_scope": SCOPE, "proposals": proposals,
        "old_seed_sha256": catalog.sha(args.seed), "explicit_full_code_transfers": transfers,
        "new_competitor_group_indices_requiring_fresh_root_trees": fresh,
        "all_missing_new_types_require_fresh_roots_not_silent_skips": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"discovery_only": True, "transported_codes": transfers,
                      "fresh_competitor_groups": fresh}), flush=True)


if __name__ == "__main__":
    main()
