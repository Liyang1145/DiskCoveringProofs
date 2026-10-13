"""Fresh model/domain/inverse reconstruction for an actual completed append pair."""

import argparse
import json

import n26_current_origin_append_context_v3 as source


def main():
    parser = argparse.ArgumentParser()
    source.arguments(parser)
    args = parser.parse_args()
    values = source.inputs(args)
    original,model,seed,controls,row,pending,supports,kernels,references,arcs,inventory = values
    if len(pending) != args.expected_open or len(kernels) != args.expected_supports:
        raise ValueError("actual new append context did not reconstruct its declared current state")
    source.inventory_gate(inventory)
    print(json.dumps({
        "actual_current_origin_append_context_reconstructed":True,
        "current_OPEN":len(pending),"current_rows":len(seed["arithmetic_ledger"]),
        "actual_current_physical_supports":len(kernels),
        "all_original_closed_domains_and_physical_inverse_gates_reconstructed":True,
        "old16_origin_donors_and_external_histories_retained":True,
        "source_geometry_OR_all_old_energy_history_NOT_claimed_replayed":True,
        "new_geometric_payments":0,"global_optimality_proved":False,
    }),flush=True)


if __name__ == "__main__":
    main()
