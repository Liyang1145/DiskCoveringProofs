"""Collapse an existing whole-angle tree using NEW exact larger-ball local leaves.

No solver import. Final mathematical acceptance freshly checks every retained
leaf and the entire root-domain partition; omitted old subtrees are replaced
only by newly certified local boxes.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import exact_graph as exact
from replay_n25_tight_domain import inputs, replay
from replay_n25_endpoint_domain import inputs as old_inputs
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    with gzip.open(args.tree, "rt", encoding="utf8") as stream:
        old = json.load(stream, object_pairs_hook=no_duplicate_keys)
    sign = old["parameter_sign"]
    constants, masks, newlocal, bound, core = inputs(sign)
    assert old["complete"] and not old["pending"]
    assert old["faces"] == masks and old["input_sha256"] == old_inputs(sign)[3]
    oldnodes = old["nodes"]
    assert all(node is not None for node in oldnodes)
    faces, edges, V = exact.graph(16, 25, masks)
    matrix = exact.kernel.angle_bounds(16, 25, faces, constants)
    D = constants["angle_scale"]
    lo, hi = exact.rootbox(matrix, D)
    nodes, stack = [None], [(0, 0, lo, hi)]
    visited = set()
    collapses = 0
    while stack:
        source, target, lo, hi = stack.pop()
        assert 0 <= source < len(oldnodes) and source not in visited
        visited.add(source)
        oldnode = oldnodes[source]
        box = exact.kernel.tighten(matrix, lo, hi, D)
        if box is None:
            nodes[target] = {"kind": "EMPTY"}
            continue
        lo, hi = box
        margin = newlocal(lo, hi)
        if margin is not None and margin > 0:
            nodes[target] = {"kind": "LOCAL"}
            collapses += int(oldnode["kind"] == "SPLIT")
            continue
        assert oldnode["kind"] in ("DUAL", "SPLIT", "LOCAL")
        if oldnode["kind"] != "SPLIT":
            nodes[target] = oldnode
            continue
        axis, cut = oldnode["axis"], F(oldnode["mid"])
        assert type(axis) is int and 0 <= axis < 15 and lo[axis] < cut < hi[axis]
        children = oldnode["children"]
        assert len(children) == 2 and children[0] != children[1]
        child = len(nodes)
        nodes.extend([None, None])
        nodes[target] = {"kind": "SPLIT", "axis": axis, "mid": str(cut),
                         "children": [child, child+1]}
        left, right = list(hi), list(lo)
        left[axis], right[axis] = cut, cut
        stack.extend([(children[0], child, list(lo), left), (children[1], child+1, right, list(hi))])
    payload = {"N": 25, "B": 16, "parameter_sign": sign, "core_centers": 25, "faces": masks,
               "nodes": nodes, "pending": [], "complete": True, "input_sha256": bound,
               "source_tree_sha256": sha(args.tree), "source_sha256": sha(Path(__file__)),
               "omitted_old_subtrees_replaced_by_new_exact_local_boxes": True,
               "global_optimality_proved": False}
    result = replay(payload)
    assert result["entire_angle_domain_proved"]
    with gzip.open(args.output, "wt", encoding="utf8") as stream:
        json.dump(payload, stream, separators=(",", ":"))
    report = dict(result, tree_sha256=sha(args.output), old_nodes=len(oldnodes),
                  old_split_subtrees_collapsed=collapses, source_tree_sha256=sha(args.tree),
                  source_sha256=sha(Path(__file__)),
                  replay_source_sha256=sha(ROOT / "replay_n25_tight_domain.py"))
    outreport = args.output.with_suffix(".prune-replay.json")
    assert not outreport.exists()
    outreport.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N25 tighter-ball complete tree reaccepted:", len(oldnodes), "->", len(nodes),
          "nodes;", collapses, "old split subtrees collapsed; not a global cover proof", flush=True)


if __name__ == "__main__":
    main()
