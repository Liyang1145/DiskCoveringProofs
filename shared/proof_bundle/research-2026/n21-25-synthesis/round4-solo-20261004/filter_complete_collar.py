"""Pay and partition every row of an already-complete old collar catalog.

This is not a new enumeration. Eight-rod cycles, strict sparse injections,
and fixed complete-family payments are independently checked per source row.
"""
from pathlib import Path
from collections import Counter
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import canonical, validate
from n25_outer_search import read, publish, bind, unchanged
from verify_sparse_maps_fast import library_gate, batch_match
from eight_rod_angles import constants_gate, exclusion, verify_cycle
from completion_family_gate import validate_outer_payment
from complete_simple_collar import simple_holes

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("catalog", "library", "maps", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--closure", type=Path, action="append", default=[])
    ap.add_argument("--batch-size", type=int, default=512)
    args = ap.parse_args()
    catalog, output = args.catalog.resolve(), args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    assert 1 <= args.batch_size <= 2048
    constants, library, table, files = library_gate(args.library.resolve())
    constants_gate(constants)
    B = library["B"]
    source, terminal = read(catalog / "SUMMARY.json"), read(catalog / "NATIVE-TERMINAL.json")
    assert source["verified"] and source["complete_necessary_outer_collar_overapproximation"]
    assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
    assert (source["N"], source["B"]) == (25, B)
    unchanged(source["files_relative_to_workspace"])
    files.update(source["files_relative_to_workspace"])
    groupspath = catalog / "GROUPS.json"
    assert sha(groupspath) == source["groups_sha256"] and groupspath.stat().st_size <= 128*1024**2
    data = read(groupspath)
    total = data["group_count"]
    assert (data["N"], data["B"], data["threshold"]) == (25, B, 1)
    assert data["full_selected_catalog_scanned"] and data["members_are_necessary_weak_graphs_not_full_types"]
    assert len(data["groups"]) == data["selected_types"] == data["catalog_types"] == total == source["unpaid_weak_graphs"]
    maps = read(args.maps)
    assert maps["verified"] and maps["schema"] == "fresh-sparse-library-explicit-map-controls-v1"
    assert maps["B"] == B and maps["library_sha256"] == sha(args.library)
    assert maps["source_sha256"] == sha(ROOT / "verify_sparse_maps_fast.py")
    assert maps["matcher_include_sha256"] == sha(ROOT / "sparse_outer_matcher.inc")
    assert maps["matcher_binary_sha256"] == sha(ROOT / "sparse_outer_match-linux")
    assert maps["all_source_trees_fresh_exact_replayed"] and maps["explicitly_checked_native_maps"] > 0
    assert maps["independent_python_existence_controls"] > 0
    assert set(maps["negative_controls_rejected"]) == {"wrong-anchor-offset", "center-collision", "missing-image-face"}
    files.update(maps["files_relative_to_workspace"])
    patterns = {}
    for path in args.closure:
        closure = read(path)
        assert closure["verified"] and closure["schema"] == "single-collar-strict-full-completion-closure-v1"
        assert (closure["N"], closure["B"]) == (25, B) and closure["pending_completions"] == 0
        assert closure["strictly_excluded"] == closure["full_completion_types"] > 0
        assert closure["known_attaining_core_lower_paid"] == 0
        assert closure["source_sha256"] == sha(ROOT / "close_strict_collar_family.py")
        assert closure["complete_this_simple_hole_completion_family"]
        assert closure["every_full_disk_and_exact_outer_face_map_rechecked"]
        assert closure["radius_threshold"] == constants["radius_upper"]
        unchanged(closure["files_relative_to_workspace"])
        files.update(closure["files_relative_to_workspace"])
        centers, faces = closure["collar_centers"], closure["collar_faces"]
        assert simple_holes(centers, B, faces) == closure["holes"]
        code, mapping = canonical(centers, B, faces, 1)
        pattern = {
            "id": len(patterns), "full_order": 25, "B": B, "centers": centers, "faces": faces,
            "holes": closure["holes"], "lower_mode": "no_full_simple_disk_realization_with_all_rods_at_most_U25",
        }
        validate_outer_payment(pattern, 25, B, list(code), mapping)
        assert code not in patterns
        patterns[code] = {"pattern": pattern, "map": mapping, "closure_sha256": sha(path)}
        bind(files, path)
    for path in (
        Path(__file__), args.library, args.maps, groupspath, catalog / "SUMMARY.json",
        catalog / "NATIVE-TERMINAL.json", ROOT / "verify_sparse_maps_fast.py",
        ROOT / "eight_rod_angles.py", ROOT / "completion_family_gate.py",
        ROOT / "CLOSED-BOUNDARY-FAN-TRANSFER.md", ROOT / "EIGHT-ROD-ANGLE-SOURCE.md",
        ROOT / "sparse_outer_match.cpp", ROOT / "sparse_outer_match-linux", ROOT / "sparse_outer_matcher.inc",
        HIGH / "group_catalog.py",
    ):
        bind(files, path)
    unchanged(files)
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": 25, "B": B, "parent_weak_graphs": total,
        "files_relative_to_workspace": files, "not_a_new_enumeration": True,
        "global_optimality_proved": False,
    })
    byid = {o["id"]: o for o in library["obstacles"]}
    counts, processed, previous = Counter(), 0, None
    payments, residual = output / "PAYMENTS.jsonl", output / "RESIDUAL.jsonl"
    with payments.open("x", encoding="ascii") as ledger, residual.open("x", encoding="ascii") as remaining:
        remaining.write(json.dumps({"schema": "complete-paid-old-collar-residual-v1", "N": 25, "B": B,
                                    "source_catalog_sha256": sha(groupspath),
                                    "members_are_weak_graphs_not_full_types": True},
                                   separators=(",", ":"))+"\n")
        for batch, first in enumerate(range(0, total, args.batch_size)):
            rows = data["groups"][first:first+args.batch_size]
            directory = output / f"maps-{batch:06}"
            directory.mkdir()
            answers = batch_match(table, [row["faces"] for row in rows], directory, 25, B)
            assert len(answers) == len(rows)
            maps_hash = sha(directory / "NATIVE-MAPS.json")
            for local, (row, answer) in enumerate(zip(rows, answers, strict=True)):
                gid, centers, faces = row["id"], row["centers"], row["faces"]
                assert gid == processed == first+local and row["members"] == 1
                assert B <= centers <= 25 and faces == sorted(set(faces)) and faces
                code = tuple(faces)
                assert previous is None or previous < code
                previous = code
                assert all(type(mask) is int and 0 < mask < 1 << centers and mask.bit_count() == 3
                           and mask & ((1 << B)-1) for mask in faces)
                used = 0
                for mask in faces:
                    used |= mask
                assert used == (1 << centers)-1
                sparse = None
                if answer["obstacle"] >= 0:
                    obstacle = byid[answer["obstacle"]]
                    mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
                    validate(25, B, obstacle["faces"], mapping, faces)
                    sparse = {"obstacle": obstacle["id"], "map": mapping,
                              "native_maps_sha256": maps_hash,
                              "native_request": local}
                cycle = None if sparse is not None else exclusion(B, centers, faces, constants)
                if cycle is not None:
                    assert verify_cycle(B, centers, faces, cycle["cycle"], constants) == cycle["exact_cycle_check"]
                    payment = {"kind": "strict-eight-rod-integer-angle-cycle", **cycle}
                elif sparse is not None:
                    payment = {"kind": "strict-sparse-source-injection", **sparse}
                elif code in patterns:
                    record = patterns[code]
                    checked = validate_outer_payment(record["pattern"], 25, B, faces, record["map"])
                    assert checked["payment_requires_full_simple_disk_completion"]
                    payment = {"kind": "strict-full-simple-disk-completion-family",
                               "pattern": record["pattern"]["id"], "map": record["map"],
                               "closure_sha256": record["closure_sha256"],
                               "not_a_standalone_geometric_weak_graph_exclusion": True}
                else:
                    payment = None
                if payment is None:
                    remaining.write(json.dumps(row, separators=(",", ":"))+"\n")
                    counts["unpaid"] += 1
                else:
                    ledger.write(json.dumps({"parent_group": gid, **payment}, separators=(",", ":"))+"\n")
                    counts[payment["kind"]] += 1
                processed += 1
            ledger.flush()
            remaining.flush()
            if batch % 10 == 0:
                print("Complete-parent postfilter:", processed, "/", total,
                      dict(counts), flush=True)
    assert processed == total == sum(counts.values())
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-old-collar-independent-paid-partition-v1", "N": 25, "B": B,
        "all_complete_parent_rows_processed_once": True, "parent_weak_graphs": total,
        "all_successful_native_sparse_injections_explicitly_checked": True,
        "all_accepted_angle_cycles_independently_integer_replayed": True,
        "all_topology_payments_checked_against_exact_outer_face_images": True,
        "payment_counts": dict(counts), "residual_weak_graphs": counts["unpaid"],
        "all_needed_full_simple_disk_lower_bounds_paid": counts["unpaid"] == 0,
        "parent_groups_sha256": sha(groupspath), "payments_sha256": sha(payments),
        "residual_sha256": sha(residual), "files_relative_to_workspace": files,
        "source_sha256": sha(Path(__file__)), "not_a_new_enumeration": True,
        "not_a_global_n25_proof": True, "global_optimality_proved": False,
    })
    print("Complete old-collar paid partition accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
