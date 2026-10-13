"""Known exact covering root survives every introduced partial candidate graph."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from n26_force import CAPS, D
import n26_sharp_partial_domains as independent
import n26_sharp_radius_constraints as constraints
import verify_selected_type_trees as typed
from verify_terminal_catalog import local_path, sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--types", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    accepted, inventory = typed.bound(args.types)
    values = typed.input_gate(args.types)
    manifest, reports, paths, table, radius, caps, arcs, certificate, positive, root_values = values
    inventory.extend(paths)
    if (not positive["original_exact_root_strictly_inside_all_tiny_cells"]
            or accepted["radius_upper"] != str(radius)):
        raise ValueError("partial controls lack the same exact candidate root")
    candidate = typed.read(args.types / "CATALOG-SOURCE/CANDIDATE-PATH.json")
    cap = typed.read(args.types / "CAP-SOURCE/CERTIFICATE.json")
    cells = [(F(0), F(0)), *[tuple(map(F, row)) for row in cap["known_candidate_tiny_angle_cells"]]]
    full = candidate["states"][-1]
    full_spec = {"N": 26, "B": 16, "next": 26, "faces": full["faces"]}
    full_matrix = independent.matrix(full_spec, caps)[0]
    if full_matrix != constraints.constraint_matrix(full_spec, caps)[0] or full_matrix is None:
        raise ValueError("known candidate full sharp matrix did not independently replay")
    ref = OriginReference(26, 16, "dfs", caps=CAPS, scale=D)
    controls = []
    for state in candidate["states"]:
        prefix = tuple(state["prefix"])
        resolved = ref.resolve(prefix)
        if ref.entry(prefix, resolved, ref.children(resolved)) != state:
            raise ValueError("partial candidate control is not the accepted exact prefix state")
        spec = {"N": 26, "B": 16, "next": state["next"], "faces": state["faces"]}
        matrix, derivation = independent.matrix(spec, caps)
        actual, _ = constraints.constraint_matrix(spec, caps)
        if matrix is None or matrix != actual:
            raise ValueError("partial necessary constraints falsely reject the known candidate")
        if any(full_matrix[i][j] > matrix[i][j] for i in range(16) for j in range(16)):
            raise ValueError("a partial domain is spuriously tighter than its completed candidate domain")
        if any(cells[j][1] - cells[i][0] > F(matrix[i][j], constraints.SCALE)
               for i in range(16) for j in range(16) if i != j):
            raise ValueError("known exact root tiny angular box was cut by a partial matrix")
        controls.append({"prefix": state["prefix"], "introduced_centers": state["next"],
                         "existing_faces": len(state["faces"]),
                         "both_independent_matrices_agree": True,
                         "completed_domain_implies_every_partial_difference_bound": True,
                         "entire_exact_root_tiny_angle_box_satisfies_partial_matrix": True})
    inventory.extend([Path(__file__), Path(independent.__file__), Path(constraints.__file__),
                      Path(typed.__file__)])
    digests = {linux(path): sha(path) for path in inventory}
    for text, digest in digests.items():
        if sha(local_path(text)) != digest:
            raise ValueError("partial candidate-control bytes changed during binding")
    report = {"schema": "N26-same-root-all-partial-candidate-sharp-domain-positive-controls-v1",
              "verified": True, "radius_scope": typed.SCOPE, "radius_upper": str(radius),
              "same_root_cover_and_exact_tiny_angle_containment_replayed": True,
              "all_candidate_prefix_states_checked": len(controls),
              "all_35_partial_domains_include_known_exact_cover": len(controls) == 35,
              "independent_BFS_Floyd_and_all_pairs_Bellman_Ford_agree_at_every_prefix": True,
              "all_completed_domain_bounds_imply_partial_bounds": True,
              "controls": controls, "global_optimality_proved": False, "files": digests}
    if len(controls) != 35:
        raise ValueError("partial positive control omitted a candidate prefix")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "controls")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
