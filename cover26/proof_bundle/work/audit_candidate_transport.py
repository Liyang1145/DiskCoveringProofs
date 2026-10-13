"""Known continuous cover survives the unrestricted N26 combinatorial screens.

This regression does not prove screen soundness for every cover. It provides a
full known-feasible path test, with geometry transported from the bound root.
"""

import argparse
from collections import defaultdict, deque
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess

from audit_prefix_origin import OriginReference, validate_disk
from audit_prefix_partition import WORK, check_frontier, native_command, publish
from new_upper_scope import sha
from n26_force import CAPS, D, angular_domain, rootbox
from verify_degree_area import load_trig


def component_budget(faces, boundary, paid):
    if len(boundary) == 2:
        return 0
    remaining = faces - paid
    root_edge = frozenset(boundary[:2])
    initial = [f for f in remaining if root_edge <= f]
    if len(initial) != 1:
        return None
    edges = defaultdict(list)
    for face in remaining:
        nodes = sorted(face)
        for i in range(3):
            for j in range(i + 1, 3):
                edges[nodes[i], nodes[j]].append(face)
    seen, pending = set(), [initial[0]]
    while pending:
        face = pending.pop()
        if face in seen:
            continue
        seen.add(face)
        nodes = sorted(face)
        for i in range(3):
            for j in range(i + 1, 3):
                pending.extend(f for f in edges[nodes[i], nodes[j]] if f not in seen)
    vertices = set().union(*seen)
    if not set(boundary) <= vertices:
        return None
    return len(vertices - set(boundary))


def compatible(child, label_map, target):
    paid = set()
    for mask in child.faces:
        nodes = [i for i in range(26) if mask >> i & 1]
        if any(i not in label_map for i in nodes):
            return False
        face = frozenset(label_map[i] for i in nodes)
        if face not in target or face in paid:
            return False
        paid.add(face)
    for boundary, budget in child.pending:
        actual = [label_map[i] for i in boundary]
        if component_budget(target, actual, paid) != budget:
            return False
    return True


def target_path(target):
    reference = OriginReference(26, 16, "dfs", caps=CAPS, scale=D)
    state = reference.initial()
    label_map = {i: i for i in range(16)}
    prefix, rows = (), []
    while True:
        state = reference.normalize(state)
        children = reference.children(state)
        rows.append(reference.entry(prefix, state, children))
        if not state.pending:
            if len(state.faces) != 34 or state.next_vertex != 26 or not compatible(state, label_map, target):
                raise ValueError("candidate path ends at a different full disk")
            return prefix, label_map, rows
        pending = list(state.pending)
        boundary, inside = pending[reference.pick(pending)]
        a, b = label_map[boundary[0]], label_map[boundary[1]]
        paid = {frozenset(label_map[i] for i in range(26) if mask >> i & 1) for mask in state.faces}
        incident = [face for face in target - paid if {a, b} <= face]
        if len(incident) != 1:
            raise ValueError("known triangulation root face is not unique")
        w = next(iter(incident[0] - {a, b}))
        matches = []
        for index, child in enumerate(children):
            mapping = label_map.copy()
            if child.next_vertex == state.next_vertex + 1:
                if w in mapping.values():
                    continue
                mapping[state.next_vertex] = w
            if compatible(reference.normalize(child), mapping, target):
                matches.append((index, child, mapping))
        if len(matches) != 1:
            raise ValueError("known covering triangulation was rejected or branch was ambiguous")
        index, state, label_map = matches[0]
        prefix += (index,)
        if len(prefix) > 34:
            raise ValueError("candidate path does not decrease the face budget")


def geometric_intervals(system, certificate):
    radius = F(1, 10**80)
    x = [F(int(n), int(certificate["Qx"])) for n in certificate["xnum"]]
    box = [(v - radius, v + radius) for v in x]
    from verify_same_root_cover import ivnorm, ivcross, ivdiv
    import verify_contact_root as exact
    centers = [[exact.point(0) if m["variable"] is None else exact.scale(m["sign"], box[m["variable"]])
                for m in row] for row in system["center_map"]]
    anchors = []
    for i in range(16):
        a, b = centers[i], centers[(i + 1) % 16]
        h, k = [exact.scale(F(1, 2), exact.sub(exact.add(exact.point(1), ivnorm(p)), box[13]))
                for p in (a, b)]
        det = ivcross(a, b)
        anchors.append([
            ivdiv(exact.sub(exact.mul(h, b[1]), exact.mul(a[1], k)), det),
            ivdiv(exact.sub(exact.mul(a[0], k), exact.mul(h, b[0])), det)])
    return anchors


def positive_control(matrix, anchors, arcs):
    """An explicit quarter-cell angular cover containing the exact anchors."""
    from verify_same_root_cover import ivcross
    step = 2**24
    # Candidate discovery values propose the tiny angle cells only.
    import math
    approx = [math.atan2(float((a[1][0] + a[1][1]) / 2),
                         float((a[0][0] + a[0][1]) / 2)) / (2 * math.pi) % 1
              for a in anchors]
    origin = approx[0]
    rotation = []
    root_lower, root_upper = rootbox(matrix)
    for i in range(1, 16):
        t = (approx[i] - origin) % 1
        n = int(t * step)
        lower, upper = F(n - 1, step), F(n + 2, step)
        # Exact cross signs verify the angular cell of q_i relative to q_0.
        def endpoint(turns):
            co, si = arcs.sincos_turn(turns)
            return [(F(co[0], arcs.SCALE), F(co[1], arcs.SCALE)),
                    (F(si[0], arcs.SCALE), F(si[1], arcs.SCALE))]
        import verify_contact_root as exact
        q0, qi = anchors[0], anchors[i]
        relative = [exact.add(exact.mul(qi[0], q0[0]), exact.mul(qi[1], q0[1])),
                    ivcross(q0, qi)]
        if ivcross(endpoint(lower), relative)[0] <= 0 or ivcross(relative, endpoint(upper))[0] <= 0:
            raise ValueError("exact candidate anchor not proved inside proposed angle cell")
        # For widths < half-turn these two signs select the short angular cell.
        if not root_lower[i - 1] <= lower <= upper <= root_upper[i - 1]:
            raise ValueError("known candidate angle cell outside the necessary root domain")
        rotation.append((lower, upper))
    # Every direct/closed angle difference is satisfied on the whole cell.
    angular = [(F(0), F(0)), *rotation]
    for i in range(16):
        for j in range(16):
            if i == j:
                continue
            if angular[j][1] - angular[i][0] > F(matrix[i][j], D):
                raise ValueError(f"known candidate tiny angle cell violates difference {i}->{j}")
    return [list(map(str, row)) for row in rotation]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    folder = WORK.parent / "outputs/n26-same-root-cover-v2"
    accepted = json.loads((folder / "VERIFIED.json").read_text())
    for name, digest in accepted["files"].items():
        if sha(folder / name) != digest:
            raise ValueError("changed root-cover evidence")
    system = json.loads((folder / "SYSTEM.json").read_text())
    certificate = json.loads((folder / "ROOT-CERTIFICATE.json").read_text())
    faces = [sum(1 << v for v in row) for row in system["all_faces"]]
    validate_disk(26, 16, faces)
    target = {frozenset(row) for row in system["all_faces"]}
    prefix, mapping, states = target_path(target)
    anchors = geometric_intervals(system, certificate)
    arcs = load_trig()[0]
    final = states[-1]
    spec = {"N": 26, "B": 16, "next": 26, "faces": final["faces"]}
    cells = positive_control(angular_domain(spec), anchors, arcs)
    args.output.mkdir(parents=True)
    binary = WORK / "prefix-origin-v1/peel_prefix_origin.linux"
    native_path = args.output / "NATIVE-FINAL.json"
    log_path = args.output / "NATIVE-LAUNCH.json"
    command = native_command(binary, ["26", "16", str(native_path), str(D), *map(str, CAPS),
                                     "0", "dfs", "frontier", ",".join(map(str, prefix)), "0", "1"])
    run = subprocess.run(command, capture_output=True, timeout=30)
    launch = {"exit_code": run.returncode, "command": command,
              "stdout": run.stdout.decode("utf-8", errors="replace"),
              "stderr": run.stderr.decode("utf-8", errors="replace")}
    publish(log_path, launch)
    if run.returncode:
        raise ValueError("native kernel rejected the known exact covering candidate")
    native = json.loads(native_path.read_text())
    ref = OriginReference(26, 16, "dfs", caps=CAPS, scale=D)
    check_frontier(native, ref, prefix, 0)
    path_file = args.output / "CANDIDATE-PATH.json"
    publish(path_file, {"prefix": list(prefix), "native_to_exact_candidate_labels": mapping,
                        "states": states, "exact_rotated_anchor_cells": cells})
    report = {
        "schema": "N26-known-full-cover-positive-transport-screen-control-v1",
        "verified": True,
        "known_same_root_cover_survives_all_combinatorial_screens": True,
        "full_peeling_transitions": len(prefix), "introduced_centers": 26,
        "complete_center_faces": 34, "B": 16, "I": 10,
        "all_necessary_angle_differences_satisfied_on_exact_anchor_cells": True,
        "native_final_state_independently_matched": True,
        "proves_screen_soundness_for_every_cover": False,
        "global_optimality_proved": False,
        "files": {str(p): sha(p) for p in (
            Path(__file__), folder / "VERIFIED.json", folder / "SYSTEM.json",
            folder / "ROOT-CERTIFICATE.json", path_file, native_path, log_path, binary)}
    }
    publish(args.output / "VERIFIED.json", report)
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
