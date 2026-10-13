"""Per-instance grouped exact force proposals for streamed n22..25 datasets."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import time
import numpy as np
import exact_graph as exact
from candidate_domain import configure
from stream_catalog import sha
from group_catalog import canonical, canonical_full

ROOT = Path(__file__).resolve().parent
assert __debug__


def make(B, N, masks, constants, limit, route_weak=False):
    faces, edges, V, solver = configure(B, N, masks, constants)
    matrix = exact.kernel.angle_bounds(B, N, faces, constants)
    D = constants["angle_scale"]
    lower, upper = exact.rootbox(matrix, D)
    nodes = [None]
    pending = [(0, lower, upper)]
    while pending and len(nodes) <= limit:
        index, lo, hi = pending.pop()
        box = exact.kernel.tighten(matrix, lo, hi, D)
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lo, hi = box
        force, x, diagnostic = solver.solve_slsqp(lo, hi)
        if force is not None:
            assert exact.kernel.force_margin(B, V, edges, lo, hi, force, F(constants["radius_upper"])) > 0
            nodes[index] = {"kind": "DUAL", "certificate": force}
            continue
        if index == 0 and route_weak and (
                N < constants["N"] or len(masks) < 2*constants["N"]-B-2):
            numeric = solver.fixed_unit_anchor_proposal(x)
            if numeric is not None and numeric["radius_float"] < float(F(constants["radius_upper"]))-1e-5:
                return None, {"nodes_proposed": 1, "pending_boxes": 1,
                              "routing_reason": "weakened graph numerically realizable; restore omitted constraints",
                              "untrusted_numeric_diagnostic": numeric, "not_a_certified_cover": True}
        widths = [h-l for l, h in zip(lo, hi)]
        if max(widths) <= 0:
            return None, {"nodes_proposed": len(nodes), "pending_boxes": len(pending)+1,
                          "routing_reason": "unsolved zero-width domain, not an exclusion"}
        anchors = np.asarray(x[:2*(B-1)]).reshape(-1, 2)
        deficits = 1-np.sum(anchors*anchors, axis=1)
        axis = max(range(B-1), key=lambda j: max(0., float(deficits[j])) if widths[j] > F(1, 10**12) else -1)
        if deficits[axis] < 1e-10 or widths[axis] <= 0:
            axis = max(range(B-1), key=lambda j: widths[j])
        cut = (lo[axis]+hi[axis])/2
        child = len(nodes)
        nodes.extend([None, None])
        nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(cut), "children": [child, child+1]}
        left, right = list(hi), list(lo)
        left[axis], right[axis] = cut, cut
        pending.extend([(child+1, right, list(hi)), (child, list(lo), left)])
    if pending:
        return None, {"nodes_proposed": len(nodes), "pending_boxes": len(pending)}
    return nodes, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--limit", type=int, default=1)
    ap.add_argument("--only-pending-from", type=Path)
    ap.add_argument("--count", type=int)
    ap.add_argument("--route-weak-realizable", action="store_true")
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    data = json.loads(args.groups.read_text())
    assert data["verified_embeddings_during_generation"]
    N, B = data["N"], data["B"]
    constantspath = ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"
    constants = json.loads(constantspath.read_text())
    assert constants["N"] == N and constants["verified"]
    groups = data["groups"]
    groups_sha = sha(args.groups)
    if N < 25:
        candidate = json.loads((ROOT.parent / f"evidence/n{N}/core-system.json").read_text())
        candidateB = candidate["B"]
        fullfaces = candidate["all_faces"]
    else:
        candidate = json.loads((ROOT.parent / "evidence/n25-algebraic-upper-round2/geometry.json").read_text())
        candidateB, fullfaces = 16, candidate["faces"]
    known = None
    if B == candidateB:
        fullmasks = sorted(sum(1 << v for v in face) for face in fullfaces)
        code = (canonical_full(N, B, fullmasks) if data["threshold"] == 0 else
                canonical(N, B, fullmasks, data["threshold"])[0])
        known = next((group["id"] for group in groups if tuple(group["faces"]) == code), None)
        assert known is not None or not data["full_selected_catalog_scanned"]
    if args.only_pending_from:
        old = json.loads(args.only_pending_from.read_text())
        assert old["groups_sha256"] == groups_sha
        unpaid = {r["group"] for r in old["outcomes"] if r["status"] == "pending"}
        groups = [g for g in groups if g["id"] in unpaid]
    if args.count:
        groups = groups[:args.count]
    outcomes = []
    started = time.monotonic()
    totals = Counter()
    covered = 0
    with (args.output / "outcomes.jsonl").open("w", encoding="utf8") as ledger:
        for group in groups:
            nodes, failure = make(B, group["centers"], group["faces"], constants, args.limit,
                                  args.route_weak_realizable)
            if nodes is None:
                outcome = {"group": group["id"], "status": "pending", **failure}
            else:
                assert group["id"] != known, "Known attaining candidate must not be strictly excluded"
                result = exact.verify(B, group["centers"], group["faces"], nodes, constants)
                payload = {"N": N, "B": B, "partial_centers": group["centers"], "faces": group["faces"],
                           "nodes": nodes, "groups_sha256": groups_sha,
                           "constants_sha256": sha(constantspath), "radius_upper": constants["radius_upper"]}
                path = args.output / f"group-{group['id']:07}.json.gz"
                with gzip.open(path, "wt", encoding="utf8") as stream:
                    json.dump(payload, stream, separators=(",", ":"))
                outcome = {"group": group["id"], "status": "excluded", **result,
                           "members": group["members"], "tree_sha256": sha(path)}
                covered += group["members"]
            totals[outcome["status"]] += 1
            outcomes.append(outcome)
            ledger.write(json.dumps(outcome, separators=(",", ":"))+"\n")
            if len(outcomes) % 500 == 0:
                ledger.flush()
                print("N", N, "B", B, "groups", len(outcomes), "excluded", totals["excluded"],
                      "pending", totals["pending"], "seconds", round(time.monotonic()-started, 2), flush=True)
    report = {"N": N, "B": B, "groups_sha256": groups_sha, "outcomes": outcomes,
              "excluded_groups": totals["excluded"], "pending_groups": totals["pending"],
              "catalog_members_excluded": covered, "requested_groups_complete": len(outcomes) == len(groups),
              "whole_catalog_exclusion_proved": False, "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__))}
    report["known_attaining_group_control"] = known
    (args.output / "SUMMARY.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Group stage finished", N, B, totals, flush=True)


if __name__ == "__main__":
    main()
