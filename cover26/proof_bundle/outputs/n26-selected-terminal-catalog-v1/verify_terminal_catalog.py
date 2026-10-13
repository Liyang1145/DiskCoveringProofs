"""Selected current terminal catalogue, with exact native/Python code agreement."""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from n26_force import CAPS, D
from n26_terminal_canonical import canonical, check_bijection


BINARY_SHA = "b07a612b71d7535a3d667dc764bcafadd104e14b6ce560f6810e56cfc9ba3a25"
CPP_SHA = "a76a8ce6c0ee0ee0f513ae9eba086d5b6d1b6b3e39440ab0cac59ef5638620c9"


def local_path(text):
    text = str(text).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper() + ":" + text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/" + text[0].lower() + text[2:])
    return Path(text)


def sha(path):
    return hashlib.sha256(local_path(path).read_bytes()).hexdigest()


def input_gate(folder):
    manifest = json.loads((folder / "MANIFEST.json").read_text())
    stage = local_path(manifest["source_stage"])
    accepted = json.loads((folder / "SOURCE-ACCEPTANCE.json").read_text())
    if (not accepted["verified"] or accepted["global_optimality_proved"]
            or sha(stage / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or sha(folder / "SOURCE-ACCEPTANCE.json") != manifest["source_acceptance_sha256"]
            or accepted["files"]["FRONTIER.json"] != sha(folder / "SOURCE-FRONTIER.json")
            or accepted["files"]["TRACE.json"] != sha(folder / "SOURCE-TRACE.json")):
        raise ValueError("terminal catalogue source stage is unbound")
    for name, digest in accepted["files"].items():
        if sha(stage / name) != digest:
            raise ValueError("terminal source stage bytes changed")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("terminal catalogue input changed")
    if (sha(stage / "peel_prefix_origin.linux") != BINARY_SHA
            or sha(stage / "peel_prefix_origin.cpp") != CPP_SHA):
        raise ValueError("terminal native canonical kernel changed")
    frontier = json.loads((folder / "SOURCE-FRONTIER.json").read_text())
    trace = json.loads((folder / "SOURCE-TRACE.json").read_text())
    control = json.loads((folder / "CANDIDATE-ACCEPTANCE.json").read_text())
    candidate = json.loads((folder / "CANDIDATE-PATH.json").read_text())
    if (not control["verified"] or not control["known_same_root_cover_survives_all_combinatorial_screens"]
            or sha(folder / "CANDIDATE-PATH.json") != control["files"][manifest["candidate_path_key"]]):
        raise ValueError("selected terminal catalogue has no bound candidate positive control")
    for text, digest in control["files"].items():
        if sha(text) != digest:
            raise ValueError("candidate positive-control dependency changed")
    runs = json.loads((folder / "NATIVE-RUNS.json").read_text())
    return manifest, stage, accepted, frontier, trace, candidate, runs


def reconstruct(folder, stage, accepted, frontier, trace, candidate, runs):
    selected = [(int(b), tuple(p)) for b, paths in trace["terminal_pending_prefixes"].items() for p in paths]
    selected.sort()
    if len(selected) != sum(row["unresolved_terminal_subtrees"] for row in accepted["families"]):
        raise ValueError("selected terminal count differs from accepted stage")
    if len(runs) != len(selected):
        raise ValueError("native selected terminal coverage incomplete")
    references = {b: OriginReference(26, b, "dfs", caps=CAPS, scale=D) for b in (14, 15, 16, 17)}
    rows, groups, candidate_matches = [], {}, []
    candidate_code = canonical(26, 16, candidate["states"][-1]["faces"])
    for index, ((b, prefix), run) in enumerate(zip(selected, runs)):
        if run["index"] != index or run["B"] != b or run["prefix"] != list(prefix):
            raise ValueError("native terminal list reordered or duplicated")
        state = references[b].resolve(prefix)
        actual = references[b].entry(prefix, state, references[b].children(state))
        if state.pending or state.next_vertex != 26:
            raise ValueError("selected catalogue contains a nonterminal state")
        matches = [row for row in frontier["pending_states"] if row["B"] == b and row["prefix"] == list(prefix)]
        if len(matches) != 1 or matches[0] != {"B": b, **actual}:
            raise ValueError("selected terminal vanished from current frontier")
        result_path, launch_path = folder / run["result"], folder / run["launch"]
        if sha(result_path) != run["result_sha256"] or sha(launch_path) != run["launch_sha256"]:
            raise ValueError("terminal native evidence bytes changed")
        launch = json.loads(launch_path.read_text())
        expected = ["/lib64/ld-linux-x86-64.so.2", linux(stage / "peel_prefix_origin.linux"),
                    "26", str(b), linux(result_path), str(D), *map(str, CAPS), "1", "dfs", "solve",
                    ",".join(map(str, prefix)), "0", "1"]
        if launch["exit_code"] != 0 or launch["command"] != expected:
            raise ValueError("wrong selected terminal native invocation")
        native = json.loads(result_path.read_text())
        code = canonical(26, b, list(state.faces))
        for mapping in code["canonical_bijections"]:
            check_bijection(26, b, list(state.faces), code["faces"], mapping)
        if (native["N"] != 26 or native["B"] != b or native["prefix"] != list(prefix)
                or not native["complete"] or native["family_complete"]
                or not native["screen"] or not native["origin_screen"] or native["operation"] != "solve"
                or native["scale"] != D or native["caps"] != list(CAPS)
                or native["calls"] != 1 or native["rooted"] != 1 or native["orbits"] != 1
                or native["survivors"] != [{"faces": code["faces"], "stabilizer": code["stabilizer"]}]):
            raise ValueError("native and exact dictionary-based canonical traversal differ")
        key = (b, tuple(code["faces"]))
        group = groups.setdefault(key, {"B": b, "canonical_faces": code["faces"],
                                        "stabilizer": code["stabilizer"], "member_indices": []})
        if group["stabilizer"] != code["stabilizer"]:
            raise ValueError("isomorphic selected types have inconsistent stabilizers")
        group["member_indices"].append(index)
        is_candidate = b == 16 and code["faces"] == candidate_code["faces"]
        if is_candidate:
            candidate_matches.append(index)
        rows.append({"index": index, "B": b, "prefix": list(prefix), "faces": list(state.faces),
                     "canonical": code, "same_canonical_type_as_known_candidate": is_candidate,
                     "radius_lower_bound_complete": False})
    if not any(row["B"] == 16 and row["prefix"] == candidate["prefix"] for row in rows):
        raise ValueError("known full candidate terminal lost from selected catalogue")
    return {"schema": "N26-selected-current-terminal-canonical-catalogue-v1",
            "rows": rows, "groups": [groups[key] for key in sorted(groups)],
            "selected_terminal_paths": len(rows), "distinct_selected_canonical_types": len(groups),
            "selected_candidate_type_paths": len(candidate_matches),
            "selected_candidate_type_member_indices": candidate_matches,
            "all_vertex_bijections_and_face_images_checked": True,
            "all_selected_native_and_python_canonical_codes_matched": True,
            "global_combinatorial_frontier_nodes_removed": 0,
            "full_catalog_complete": False, "global_optimality_proved": False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    manifest, stage, accepted, frontier, trace, candidate, runs = input_gate(args.input)
    table = reconstruct(args.input, stage, accepted, frontier, trace, candidate, runs)
    table_path = args.input / "CATALOG.json"
    if table_path.exists():
        if json.loads(table_path.read_text()) != table:
            raise ValueError("selected terminal canonical table differs")
    else:
        table_path.write_text(json.dumps(table, separators=(",", ":")) + "\n", encoding="utf-8")
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid selected catalogue accepted: " + label)

    bad = deepcopy(trace)
    next(paths for paths in bad["terminal_pending_prefixes"].values() if paths).pop()
    reject("missing-selected-terminal", lambda: reconstruct(args.input, stage, accepted, frontier, bad, candidate, runs))
    reject("missing-native-terminal-run", lambda: reconstruct(
        args.input, stage, accepted, frontier, trace, candidate, runs[:-1]))
    bad_frontier = deepcopy(frontier)
    first = table["rows"][0]
    bad_frontier["pending_states"] = [row for row in bad_frontier["pending_states"]
                                     if not (row["B"] == first["B"] and row["prefix"] == first["prefix"])]
    reject("terminal-discarded-from-current-frontier", lambda: reconstruct(
        args.input, stage, accepted, bad_frontier, trace, candidate, runs))
    mapping = deepcopy(first["canonical"]["canonical_bijections"][0])
    mapping["vertex_to_canonical"][1] = mapping["vertex_to_canonical"][0]
    reject("nonbijective-canonical-relabel", lambda: check_bijection(
        26, first["B"], first["faces"], first["canonical"]["faces"], mapping))
    wrong_code = list(first["canonical"]["faces"])
    wrong_code[0] ^= 1 << 25
    reject("wrong-canonical-face-image", lambda: check_bijection(
        26, first["B"], first["faces"], wrong_code, first["canonical"]["canonical_bijections"][0]))
    files = ["MANIFEST.json", "SOURCE-ACCEPTANCE.json", "SOURCE-FRONTIER.json", "SOURCE-TRACE.json",
             "CANDIDATE-ACCEPTANCE.json", "CANDIDATE-PATH.json", "NATIVE-RUNS.json", "CATALOG.json",
             *manifest["copied_files"], *[name for run in runs for name in (run["result"], run["launch"])]]
    report = {"schema": "N26-accepted-selected-terminal-canonical-catalogue-v1", "verified": True,
              "source_stage_acceptance_sha256": manifest["source_acceptance_sha256"],
              "source_pending_subtrees": len(frontier["pending_states"]),
              "selected_terminal_paths": table["selected_terminal_paths"],
              "distinct_selected_canonical_types": table["distinct_selected_canonical_types"],
              "selected_candidate_type_paths": table["selected_candidate_type_paths"],
              "all_explicit_terminal_paths_preserved_and_reconstructed": True,
              "all_selected_native_and_python_canonical_codes_matched": True,
              "explicit_vertex_bijections_and_all_face_images_checked": True,
              "current_global_combinatorial_frontier_nodes_removed": 0,
              "new_geometric_lower_bounds_accepted": 0, "formal_machine_geometry_proof": False,
              "full_catalog_complete": False, "global_lower_bound_proved": False,
              "global_optimality_proved": False, "negative_controls_rejected": negatives,
              "files": {name: sha(args.input / name) for name in dict.fromkeys(files)},
              "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_terminal_catalog.py"]:
        raise ValueError("executed terminal checker differs from sealed one")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
