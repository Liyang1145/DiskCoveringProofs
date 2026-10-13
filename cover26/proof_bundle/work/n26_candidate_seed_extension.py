"""Exact ownership and immutable-node contract for an accepted forest seed.

This contract creates no geometric payment. The unchanged original forest
replayer proves complete closed-half geometry on the resulting full tree.
"""


def gate(row, seed, extension):
    index = row["index"]
    if (
        type(index) is not int
        or type(seed["source_OPEN_index"]) is not int
        or type(extension["source_OPEN_index"]) is not int
        or seed["source_OPEN_index"] != index
        or extension["source_OPEN_index"] != index
        or seed["actual_source_closed_box"] != row
        or extension["actual_source_closed_box"] != row
    ):
        raise ValueError("seeded candidate extension changed exact current root ownership")
    old, new = seed["nodes"], extension["nodes"]
    if not isinstance(old, list) or not old or not isinstance(new, list) or len(new) < len(old):
        raise ValueError("seeded candidate extension lost an accepted original node")
    for number, node in enumerate(old):
        if not isinstance(node, dict) or node.get("kind") not in ("SPLIT", "ENERGY", "LOCAL", "EMPTY", "OPEN"):
            raise ValueError("candidate seed has an unknown node kind")
        if node["kind"] != "OPEN" and new[number] != node:
            raise ValueError("seeded candidate extension changed a prior paid leaf or closed split")
    return {
        "source_OPEN_index": index,
        "accepted_seed_nodes": len(old),
        "accepted_seed_OPEN_leaves": sum(node["kind"] == "OPEN" for node in old),
        "accepted_seed_non_OPEN_nodes_retained_identically": sum(node["kind"] != "OPEN" for node in old),
        "accepted_seed_ENERGY_leaves_retained_identically": sum(node["kind"] == "ENERGY" for node in old),
        "new_nodes": len(new) - len(old),
        "old_paid_leaves_and_closed_splits_retained_identically": True,
        "source_full_closed_root_retained_identically": True,
    }
