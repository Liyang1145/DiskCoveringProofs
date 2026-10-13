"""Own N23/N24 strict completion-family proposals; no nonstrict core shortcuts."""
from pathlib import Path
import argparse
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from probe_collar_batches import make
import exact_graph as exact
from stream_catalog import sha
from n25_outer_search import read, publish
from small_order_filling_kernel import start_states, children, constants_gate, angle_exclusion

assert __debug__


def propose(collar, constants, max_nodes=10000, force_limit=31, force_enabled=True):
    N, B, centers, outer = (collar[key] for key in ("N", "B", "centers", "faces"))
    cap8 = constants_gate(constants, N, B)
    assert 1 <= max_nodes <= 100000 and 1 <= force_limit <= 10001
    nodes, cache, calls, started = [], {}, 0, time.monotonic()
    def visit(state):
        nonlocal calls
        index = len(nodes)
        nodes.append(None)
        base = {"state": state}
        calls += 1
        if calls > max_nodes:
            nodes[index] = {**base, "kind": "FRONTIER"}
            return index
        key = (state["next"], tuple(state["faces"]))
        if force_enabled and key not in cache:
            payment = angle_exclusion(B, state["next"], state["faces"], constants, cap8)
            if payment is None:
                force_nodes, _ = make(B, state["next"], state["faces"],
                                      constants, force_limit, route_weak=False)
                if force_nodes is not None:
                    payment = {
                        "kind": "FORCE", "force_nodes": force_nodes,
                        "exact_result": exact.verify(
                            B, state["next"], state["faces"], force_nodes, constants)}
            cache[key] = payment
        if force_enabled and cache[key] is not None:
            nodes[index] = {**base, **cache[key]}
            return index
        following = children(state, N, B)
        if following is None:
            nodes[index] = {**base, "kind": "FULL_PENDING"}
        elif not following:
            nodes[index] = {**base, "kind": "DEAD"}
        else:
            nodes[index] = {**base, "kind": "SPLIT", "children": [visit(child) for child in following]}
        return index
    roots = [visit(state) for state in start_states(N, B, centers, outer)]
    return {
        "schema": "small-order-own-constant-complete-collar-branch-tree-v1",
        "N": N, "B": B, "collar_centers": centers, "collar_faces": outer,
        "radius_upper": constants["radius_upper"], "cap8": cap8,
        "roots": roots, "nodes": nodes, "max_proposal_states": max_nodes,
        "force_limit": force_limit, "force_enabled": force_enabled,
        "distinct_graph_proposals": len(cache), "seconds": time.monotonic()-started,
        "global_optimality_proved": False}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--collar", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--limit", type=int, default=10000)
    ap.add_argument("--force-limit", type=int, default=31)
    ap.add_argument("--no-force-control", action="store_true")
    args = ap.parse_args()
    assert not args.output.exists()
    collar = read(args.collar)
    constantspath = ROOT.parent / f"evidence/core-reduction/constants/n{collar['N']}.json"
    payload = propose(collar, read(constantspath), args.limit, args.force_limit,
                      not args.no_force_control)
    payload.update(
        source_collar_sha256=sha(args.collar), constants_sha256=sha(constantspath),
        kernel_sha256=sha(ROOT / "small_order_filling_kernel.py"),
        source_sha256=sha(Path(__file__)), whole_family_payment_requires_independent_replay=True)
    publish(args.output, payload)
    print("Own-order complete-family proposal:", collar["N"], collar["B"],
          len(payload["nodes"]), "nodes; separate replay required", flush=True)


if __name__ == "__main__":
    main()
