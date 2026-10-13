"""Propose exact graph payments while exhausting a fixed simple-hole family."""
from pathlib import Path
import argparse
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from probe_groups import make
import exact_graph as exact
from eight_rod_angles import constants_gate, exclusion
from n25_outer_search import read, publish
from stream_catalog import sha
from general_paid_collar_kernel import start_states, children

assert __debug__


def propose(collar, constants, max_nodes, max_force_nodes=1):
    N, B, centers, outer = (collar[k] for k in ("N", "B", "centers", "faces"))
    initial = start_states(N, B, centers, outer)
    nodes = []
    force_cache = {}
    calls = 0
    started = time.monotonic()

    def visit(state):
        nonlocal calls
        index = len(nodes);nodes.append(None)
        base = {"state": state}
        calls += 1
        if calls > max_nodes:
            nodes[index] = {**base, "kind": "FRONTIER"}
            return index
        graph_key = (state["next"], tuple(state["faces"]))
        if graph_key not in force_cache:
            angle = exclusion(B, state["next"], state["faces"], constants)
            if angle is not None:
                force_cache[graph_key] = {"kind": "ANGLE", **angle}
            else:
                force_nodes, diagnostic = make(B, state["next"], state["faces"], constants,
                                               max_force_nodes, route_weak=False)
                if force_nodes is None:
                    force_cache[graph_key] = None
                else:
                    result = exact.verify(B, state["next"], state["faces"], force_nodes, constants)
                    force_cache[graph_key] = {"kind": "FORCE", "force_nodes": force_nodes, "exact_result": result}
        if force_cache[graph_key] is not None:
            nodes[index] = {**base, **force_cache[graph_key]}
            return index
        following = children(state, N, B)
        if following is None:
            nodes[index] = {**base, "kind": "FULL_PENDING"}
        elif not following:
            nodes[index] = {**base, "kind": "DEAD"}
        else:
            indices = [visit(child) for child in following]
            nodes[index] = {**base, "kind": "SPLIT", "children": indices}
        if calls % 100 == 0:
            print("Paid hole branch states:", calls, "distinct force graphs:", len(force_cache),
                  "seconds:", round(time.monotonic()-started, 2), flush=True)
        return index

    roots = [visit(state) for state in initial]
    return {"schema": "proof-paid-general-collar-branch-tree-v1", "N": N, "B": B,
            "collar_centers": centers, "collar_faces": outer, "roots": roots, "nodes": nodes,
            "max_proposal_states": max_nodes, "max_force_nodes": max_force_nodes,
            "distinct_graph_proposals": len(force_cache), "seconds": time.monotonic()-started}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--collar", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--limit", type=int, default=20000)
    ap.add_argument("--force-limit", type=int, default=1)
    args = ap.parse_args()
    assert not args.output.exists() and 1 <= args.limit <= 100000
    collar = read(args.collar)
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    constants_gate(constants)
    payload = propose(collar, constants, args.limit, args.force_limit)
    payload.update(source_collar_sha256=sha(args.collar), constants_sha256=sha(constants_path),
                   kernel_sha256=sha(ROOT / "general_paid_collar_kernel.py"), source_sha256=sha(Path(__file__)),
                   whole_family_payment_requires_independent_replay=True, global_optimality_proved=False)
    publish(args.output, payload)
    from collections import Counter
    print("Paid hole proposal tree produced:", dict(Counter(n["kind"] for n in payload["nodes"])),
          "independent replay required", flush=True)


if __name__ == "__main__":
    main()
