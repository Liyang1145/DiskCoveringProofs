"""Unaccepted continuation using root-specific necessary angle constraints."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import angular_domain, tighten, load_trig
from probe_direct_arc_force import DirectArcSolver
import probe_sharp_radius_angle_caps as caps_probe
import verify_refined_candidate_angles as checker


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--pinning-basis", type=Path, required=True)
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--pinning", type=Path, required=True)
    parser.add_argument("--cap-discovery", type=Path, required=True)
    parser.add_argument("--checks", type=int, default=160)
    parser.add_argument("--branch-depth", type=int, default=16)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = checker.bound(args.source)
    pin_report, _ = checker.bound(args.pinning)
    pin_proposal = json.loads((args.pinning / "CERTIFICATE.json").read_text())
    data = checker.refined.source_gate(
        args.pinning_basis, args.stress, args.local, args.transport, pin_proposal)
    pin_result = checker.refined.derive(*data[:5], pin_proposal)
    if any(pin_report[key] != value for key, value in pin_result.items()):
        raise ValueError("discovery did not replay its accepted pinning source")
    source = json.loads((args.source / "CERTIFICATE.json").read_text())
    spec = source["spec"]
    final = data[3]["states"][-1]
    if spec != {"N": 26, "B": 16, "next": 26, "faces": final["faces"]}:
        raise ValueError("sharp discovery source graph differs")
    radius_upper = F(json.loads((args.stress / "VERIFIED.json").read_text())["modified_root_check"]["r_strict_interval"][1])
    cells = [tuple(map(F, r)) for r in pin_result["closed_anchor_angle_cells"]]
    arcs = load_trig(args.source)[0]
    previous, pending, ledger = checker.sharp.replay(spec, radius_upper, cells, source["nodes"], arcs)
    if (any(accepted[key] != value for key, value in previous.items())
            or pending != json.loads((args.source / "PENDING-ANGLES.json").read_text())):
        raise ValueError("sharp discovery lost its accepted OPEN frontier")
    trial = json.loads(args.cap_discovery.read_text())
    scale, caps, margins = caps_probe.caps_for(radius_upper, len(trial["scale"]) - 1, arcs)
    if (str(scale) != trial["scale"] or list(map(str, caps)) != trial["caps"]
            or trial["source_angle_acceptance_sha256"] != checker.sharp.pin.sha(args.source / "VERIFIED.json")):
        raise ValueError("sharp cap discovery constants or source changed")
    sharp_matrix, reason = caps_probe.domain(spec, caps, scale)
    if sharp_matrix is None:
        raise ValueError("known candidate graph rejected by proposed sharp caps")
    old_matrix = angular_domain(spec)
    nodes = deepcopy(source["nodes"])
    stack = [(r["index"], list(map(F, r["lower"])), list(map(F, r["upper"])), 0) for r in pending]
    stack.sort(key=lambda r: sum(float(b - a)**2 for a, b in zip(r[1], r[2])), reverse=True)
    solver = DirectArcSolver(spec)
    count, diagnostics = 0, []
    center = [(a + b) / 2 for a, b in cells]
    while stack and count < args.checks:
        index, lower, upper, depth = stack.pop()
        if depth >= args.branch_depth:
            continue
        old_box = tighten(old_matrix, lower, upper)
        count += 1
        if old_box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = old_box
        box = caps_probe.tighten(sharp_matrix, scale, lower, upper)
        if box is None:
            nodes[index] = {"kind": "SHARP_EMPTY"}
        else:
            sharp_lower, sharp_upper = box
            if all(a <= lo <= hi <= b for lo, hi, (a, b) in zip(sharp_lower, sharp_upper, cells)):
                nodes[index] = {"kind": "SHARP_LOCAL"}
                continue
            cert, status = solver.solve_sharp(sharp_lower, sharp_upper, radius_upper)
            diagnostics.append({"node_index": index, **status})
            if cert is not None:
                nodes[index] = {"kind": "SHARP_FORCE", "cert": cert}
            else:
                widths = [float(b - a) for a, b in zip(sharp_lower, sharp_upper)]
                axis = max(range(15), key=lambda i: widths[i] * (status["anchor_force_norm_proposal"][i] + 1e-12))
                middle = (sharp_lower[axis] + sharp_upper[axis]) / 2
                if not lower[axis] < middle < upper[axis]:
                    continue
                children = [len(nodes), len(nodes) + 1]
                nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
                nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(middle), "children": children}
                left_upper, right_lower = list(upper), list(lower)
                left_upper[axis], right_lower[axis] = middle, middle
                children_boxes = [
                    (children[0], list(lower), left_upper, depth + 1),
                    (children[1], right_lower, list(upper), depth + 1),
                ]
                children_boxes.sort(key=lambda r: sum(float((a + b) / 2 - c)**2
                                                      for a, b, c in zip(r[1], r[2], center)))
                stack.extend(children_boxes)
        if count % 20 == 0:
            print(json.dumps({"unaccepted_sharp_boxes_probed": count,
                              "nodes": len(nodes),
                              "SHARP_FORCE": sum(n["kind"] == "SHARP_FORCE" for n in nodes),
                              "SHARP_EMPTY": sum(n["kind"] == "SHARP_EMPTY" for n in nodes),
                              "SHARP_LOCAL": sum(n["kind"] == "SHARP_LOCAL" for n in nodes)}), flush=True)
    counts = {kind: sum(n["kind"] == kind for n in nodes)
              for kind in ("SPLIT", "FORCE", "LOCAL", "EMPTY", "OPEN",
                           "SHARP_FORCE", "SHARP_LOCAL", "SHARP_EMPTY")}
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-root-cap-aware-angular-continuation-v1",
        "verified": False, "spec": spec, "radius_scope": "same-root-Rstar",
        "source_acceptance_sha256": checker.sharp.pin.sha(args.source / "VERIFIED.json"),
        "source_certificate_sha256": checker.sharp.pin.sha(args.source / "CERTIFICATE.json"),
        "pinning_acceptance_sha256": checker.sharp.pin.sha(args.pinning / "VERIFIED.json"),
        "cap_discovery_sha256": checker.sharp.pin.sha(args.cap_discovery),
        "scale": str(scale), "caps": list(map(str, caps)),
        "strict_sine_margins": list(map(str, margins)),
        "nodes": nodes, "proposed_counts": counts, "discovery_checks": count,
        "diagnostics": diagnostics,
        "independent_sharp_constraint_interface_and_full_tree_replay_pending": True,
        "global_optimality_proved": False,
    }, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "proposed_counts": counts,
                      "independent_sharp_constraint_acceptance_pending": True}), flush=True)


if __name__ == "__main__":
    main()
