"""Unaccepted transfer of accepted energy parameters to an identical full type."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from verify_selected_type_trees import bound, read
from verify_terminal_catalog import local_path, sha


def main():
    parser = argparse.ArgumentParser()
    for key in ("old-overlay", "new-registry", "new-registry-replay", "output", "kernels-output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.kernels_output.exists():
        raise FileExistsError("fresh energy catalogue transfer paths required")
    old, _ = bound(args.old_overlay)
    new, _ = bound(args.new_registry)
    if (read(args.new_registry_replay) != new or old["radius_upper"] != new["radius_upper"]
            or old["radius_scope"] != new["radius_scope"]
            or old["r_strict_interval"] != new["r_strict_interval"]):
        raise ValueError("energy parameter transfer changed radius, scope or actual new source replay")
    old_source = local_path(read(args.old_overlay / "MANIFEST.json")["source_registry"])
    old_pending = {row["group_index"]: row for row in read(old_source / "PENDING-TYPES.json")}
    new_pending = {(row["spec"]["B"], tuple(row["spec"]["faces"])): row
                   for row in read(args.new_registry / "PENDING-TYPES.json")}
    old_domains = {row["group_index"]: row["matrix"] for row in read(old_source / "DOMAINS.json")}
    new_domains = {row["group_index"]: row["matrix"] for row in read(args.new_registry / "DOMAINS.json")}
    proposal = deepcopy(read(args.old_overlay / "PROPOSAL.json"))
    kernels = deepcopy(read(args.old_overlay / "KERNELS.json"))
    mapping = {}
    for index in sorted({row["group_index"] for row in proposal["proposals"]}):
        previous = old_pending[index]
        current = new_pending.get((previous["spec"]["B"], tuple(previous["spec"]["faces"])))
        if (current is None or current["spec"] != previous["spec"]
                or current["closed_OPEN_boxes"] != previous["closed_OPEN_boxes"]
                or new_domains[current["group_index"]] != old_domains[index]):
            raise ValueError("energy transfer requires the exact same full spec, matrix and source OPEN boxes")
        mapping[index] = current["group_index"]
    for row in proposal["proposals"]:
        row["group_index"] = mapping[row["group_index"]]
    for row in kernels:
        row["group_index"] = mapping[row["group_index"]]
    args.kernels_output.write_text(json.dumps(kernels, separators=(",", ":")) + "\n", encoding="utf-8")
    proposal.update({
        "verified": False, "registry_acceptance_sha256": sha(args.new_registry / "VERIFIED.json"),
        "kernels_sha256": sha(args.kernels_output),
        "old_accepted_energy_overlay_sha256": sha(args.old_overlay / "VERIFIED.json"),
        "full_type_code_transfers": [{"old_group_index": i, "new_group_index": j,
                                     "identical_full_spec_radius_matrix_and_all_source_OPEN_boxes": True}
                                    for i, j in sorted(mapping.items())],
        "independent_current_source_replay_and_standalone_acceptance_still_required": True})
    args.output.write_text(json.dumps(proposal, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"discovery_only": True, "transferred_complete_type_indices": mapping,
                      "exact_source_OPEN_boxes_preserved": True}), flush=True)


if __name__ == "__main__":
    main()
