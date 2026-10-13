"""Read-only collection diagnostics; not full old-proof content admission."""

import json
import n26_import_n25_source_common as prior


def main():
    accepted, binding = prior.read(prior.SOURCE), prior.read(prior.BINDING)
    prior.scope_gate(accepted, binding)
    inventory, old_count = prior.collect_prior_inventory(accepted, [])
    print(json.dumps({
        "read_only_N25_fixed_inventory_collection_passed": True,
        "prior_prerequisites": old_count, "prior_and_global_entry_bindings": len(inventory),
        "dependency_content_NOT_rehashed_by_this_preflight": True,
        "actual_import_acceptance_NOT_created": True,
    }), flush=True)


if __name__ == "__main__":
    main()
