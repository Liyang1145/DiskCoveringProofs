"""Refine the ENTIRE weaker endpoint-core domain, never borrow full-core bounds.

Numerical conic outputs only propose leaves. An independent stdlib replay is
required even for a partial tree. An unfinished tree is not a core theorem.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import os
import time

os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import numpy as np
import exact_graph as exact
from candidate_domain import configure
from replay_n25_endpoint_domain import inputs, replay
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sign", type=int, choices=(-1, 1), required=True)
    ap.add_argument("--limit", type=int, default=1001)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--resume", type=Path)
    args = ap.parse_args()
    assert args.limit >= 1 and not args.output.exists()
    args.output.mkdir(parents=True)
    constants, masks, anchorcheck, bound, core = inputs(args.sign)
    B, N = 16, 25
    faces, edges, V, solver = configure(B, N, masks, constants)
    matrix = exact.kernel.angle_bounds(B, N, faces, constants)
    scale = constants["angle_scale"]
    lower, upper = exact.rootbox(matrix, scale)
    nodes, stack = [None], [(0, lower, upper)]
    if args.resume is not None:
        with gzip.open(args.resume, "rt", encoding="utf8") as stream:
            previous = json.load(stream)
        replay(previous)
        assert previous["parameter_sign"] == args.sign and not previous["complete"]
        assert previous["input_sha256"] == bound and previous["faces"] == masks
        nodes = previous["nodes"]
        stack = [(p["index"], list(map(F, p["lo"])), list(map(F, p["hi"])))
                 for p in previous["pending"]]
    processed = 0
    counts = Counter(node["kind"] for node in nodes if node is not None)
    started = time.monotonic()
    while stack and len(nodes) <= args.limit:
        index, lo, hi = stack.pop()
        assert nodes[index] is None
        box = exact.kernel.tighten(matrix, lo, hi, scale)
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
        else:
            lo, hi = box
            localmargin = anchorcheck(lo, hi)
            if localmargin is not None and localmargin > 0:
                nodes[index] = {"kind": "LOCAL"}
            else:
                force, x, diagnostic = solver.solve_slsqp(lo, hi)
                if force is not None:
                    assert exact.kernel.force_margin(B, V, edges, lo, hi, force,
                                                     F(constants["radius_upper"])) > 0
                    nodes[index] = {"kind": "DUAL", "certificate": force}
                else:
                    widths = [h-l for l, h in zip(lo, hi)]
                    assert max(widths) > 0, "unpaid singleton must not be accepted"
                    q = np.asarray(x[:2*(B-1)]).reshape(-1, 2)
                    deficits = 1-np.sum(q*q, axis=1)
                    axis = max(range(B-1), key=lambda j:
                               max(0., float(deficits[j])) if widths[j] > F(1, 10**12) else -1)
                    if not np.isfinite(deficits[axis]) or deficits[axis] < 1e-10 or widths[axis] <= 0:
                        axis = max(range(B-1), key=lambda j: widths[j])
                    cut = (lo[axis]+hi[axis])/2
                    child = len(nodes)
                    nodes.extend([None, None])
                    nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(cut),
                                    "children": [child, child+1]}
                    left, right = list(hi), list(lo)
                    left[axis], right[axis] = cut, cut
                    stack.extend([(child+1, right, list(hi)), (child, list(lo), left)])
        counts[nodes[index]["kind"]] += 1
        processed += 1
        if processed % 100 == 0:
            print("N25 reduced core", args.sign, "nodes", len(nodes), "unpaid", len(stack),
                  "paid leaves", counts["DUAL"]+counts["LOCAL"]+counts["EMPTY"],
                  "seconds", round(time.monotonic()-started, 1), flush=True)
    payload = {"N": N, "B": B, "parameter_sign": args.sign, "core_centers": N,
               "faces": masks, "nodes": nodes, "complete": not stack,
               "pending": [{"index": i, "lo": list(map(str, lo)), "hi": list(map(str, hi))}
                           for i, lo, hi in stack],
               "input_sha256": bound, "source_sha256": sha(Path(__file__)),
               "global_optimality_proved": False,
               "scope": "specified 61-node endpoint core necessary angle domain, not all covers"}
    if args.resume is not None:
        payload["resume_input_sha256"] = sha(args.resume)
    treepath = args.output / "endpoint-angle-tree.json.gz"
    with gzip.open(treepath, "wt", encoding="utf8") as stream:
        json.dump(payload, stream, separators=(",", ":"))
    checked = replay(payload)
    checked.update(tree_sha256=sha(treepath), proposal_source_sha256=sha(Path(__file__)),
                   source_sha256=sha(ROOT / "replay_n25_endpoint_domain.py"))
    (args.output / "PARTITION-REPLAY.json").write_text(json.dumps(checked, indent=2), encoding="utf8")
    print("N25 reduced-domain partition exact PASS:", checked["counts"],
          "unpaid", checked["pending_boxes"], "entire domain proved", checked["entire_angle_domain_proved"],
          flush=True)


if __name__ == "__main__":
    main()
