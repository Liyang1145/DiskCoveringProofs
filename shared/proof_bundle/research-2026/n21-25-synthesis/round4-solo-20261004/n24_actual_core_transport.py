"""Exact N24 own23-center/20-face core injection into actual full24-center leaves."""
from pathlib import Path
from itertools import permutations
from collections import Counter
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from complete_simple_collar import bits
from cross_order_strict_transfer import validate_disk

assert __debug__
COREPATH = ROOT / "n24-core-fresh-v1/VERIFIED.json"
SYSTEMPATH = ROOT / "n23-n24-archive-core-inputs-20261005-v1/n24/core-system.json"


def own_core_gate():
    proof, system = read(COREPATH), read(SYSTEMPATH)
    assert proof["verified"] and proof["schema"] == "isolated-N24-same-root-upper-local-and-entire-core-replay-v1"
    assert (proof["N"], proof["B"], proof["core_centers"]) == (24, 15, 23)
    assert proof["source_sha256"] == sha(ROOT / "replay_isolated_n24_core_prerequisites.py")
    assert proof["system_sha256"] == sha(SYSTEMPATH)
    for flag in (
        "exact_root_interval_and_same_root_entire_disk_upper_freshly_recomputed",
        "all_114_local_principal_minors_and_perturbation_gap_freshly_recomputed",
        "all_69215_core_angle_nodes_freshly_mathematically_replayed",
        "LOCAL_leaves_require_actual_fresh_root_and_isolation_not_historical_flags",
        "specified_core_lower_bound_nonstrict_same_root_not_strict_upper_exclusion"):
        assert proof[flag]
    assert (system["N"], system["B"], system["G"], system["D"]) == (24, 15, 114, 219)
    assert len(system["center_core_nodes"]) == 24
    assert system["center_core_nodes"][19] is None
    assert [v for v in system["center_core_nodes"] if v is not None] == list(range(15, 38))
    masks = sorted(sum(1 << (system["center_core_nodes"][v]-15) for v in face)
                   for face in system["active_faces"])
    assert masks == proof["core_faces"] and len(masks) == 20
    assert system["edges"][:30] == (
        [[i, 15+i] for i in range(15)]+[[i, 15+(i+1) % 15] for i in range(15)])
    converted = []
    for j, rawface in enumerate(system["active_faces"]):
        witness = system["old_node_to_core"][str(15+24+j)]
        nodes = [system["center_core_nodes"][v] for v in rawface]
        assert all(v is not None for v in nodes)
        assert system["edges"][30+3*j:33+3*j] == [[witness, v] for v in nodes]
        converted.extend(
            tuple(sorted((38+masks.index(sum(1 << (v-15) for v in nodes)), v))) for v in nodes)
    assert len(system["edges"]) == 90
    expected = [tuple(sorted((38+j, 15+v))) for j, mask in enumerate(masks) for v in bits(mask)]
    assert sorted(converted) == sorted(expected)
    for name, field in (
        ("root-verified.json", "fresh_root_report_sha256"),
        ("upper-verified.json", "fresh_upper_report_sha256"),
        ("FRESH-LOCAL-ISOLATION.json", "fresh_local_report_sha256"),
        ("FRESH-ANGLE-REPLAY.json", "fresh_angle_report_sha256")):
        assert sha(COREPATH.parent / name) == proof[field]
    for path, digest in proof["frozen_files"].items():
        assert sha(path) == digest
    assert proof["constants_sha256"] == sha(ROOT.parent / "evidence/core-reduction/constants/n24.json")
    return proof


def validate_embedding(mapping, target_centers, target_faces, proof):
    assert proof["N"] == 24 and proof["B"] == 15 and proof["core_centers"] == 23
    assert type(target_centers) is int and target_centers == 24
    validate_disk(24, 15, target_faces)
    centers, anchors = mapping["centers"], mapping["anchors"]
    assert type(centers) is list and len(centers) == 23
    assert all(type(v) is int and 0 <= v < target_centers for v in centers)
    assert len(set(centers)) == 23
    sign, shift = mapping["orientation"], mapping["shift"]
    assert type(sign) is int and sign in (1, -1)
    assert type(shift) is int and 0 <= shift < 15
    assert centers[:15] == [(shift+sign*j) % 15 for j in range(15)]
    assert all(v >= 15 for v in centers[15:])
    assert type(anchors) is list and anchors == [(shift+sign*j-(sign < 0)) % 15 for j in range(15)]
    assert all(type(v) is int for v in anchors)
    for j in range(15):
        assert {centers[j], centers[(j+1) % 15]} == {anchors[j], (anchors[j]+1) % 15}
    image_masks = [sum(1 << centers[v] for v in bits(mask)) for mask in proof["core_faces"]]
    assert len(set(image_masks)) == 20 and set(image_masks) <= set(target_faces)
    target_witnesses = [15+24+target_faces.index(mask) for mask in image_masks]
    assert len(set(target_witnesses)) == 20
    # Explicit source→target vertex map for every center, anchor and witness.
    vertices = anchors+[15+v for v in centers]+target_witnesses
    assert len(vertices) == 58 and len(set(vertices)) == 58
    source_edges = (
        [(i, 15+i) for i in range(15)]+[(i, 15+(i+1) % 15) for i in range(15)]
        +[(38+j, 15+v) for j, mask in enumerate(proof["core_faces"]) for v in bits(mask)])
    target_edges = {
        tuple(sorted(edge)) for edge in
        ([(i, 15+i) for i in range(15)]+[(i, 15+(i+1) % 15) for i in range(15)]
         +[(39+j, 15+v) for j, mask in enumerate(target_faces) for v in bits(mask)])}
    assert all(tuple(sorted((vertices[u], vertices[v]))) in target_edges for u, v in source_edges)
    return {
        "verified": True, "source_centers": 23, "target_centers": 24,
        "source_active_faces": 20, "target_full_faces": 31, "mapped_anchor_and_face_rods": 90,
        "correct_reflected_anchor_offset": True, "actual_full_source_not_outer_group_identity": True,
        "same_root_nonstrict_core_not_strict_upper_exclusion": True}


def find_embedding(target_centers, target_faces, proof):
    assert target_centers == 24
    validate_disk(24, 15, target_faces)
    source_faces = [bits(mask) for mask in proof["core_faces"]]
    targets = [set(bits(mask)) for mask in target_faces]
    source_adj, target_adj = [set() for _ in range(23)], [set() for _ in range(24)]
    source_incident, target_counts = [[] for _ in range(23)], Counter()
    for index, face in enumerate(source_faces):
        for v in face:
            source_incident[v].append(index)
            source_adj[v].update(set(face)-{v})
    for face in targets:
        for v in face:
            target_adj[v].update(face-{v})
            target_counts[v] += 1
    for sign in (1, -1):
        for shift in range(15):
            assignment = [(shift+sign*j) % 15 for j in range(15)]+[None]*8
            domains = {}
            for v in range(15, 23):
                necessary = {assignment[u] for u in source_adj[v] if u < 15}
                domains[v] = {
                    u for u in range(15, 24)
                    if necessary <= target_adj[u] and len(source_adj[v]) <= len(target_adj[u])
                    and len(source_incident[v]) <= target_counts[u]}
            if any(not value for value in domains.values()):
                continue
            def possible(used):
                for face in source_faces:
                    assigned = {assignment[v] for v in face if assignment[v] is not None}
                    rest = [v for v in face if assignment[v] is None]
                    if not rest:
                        if assigned not in targets:
                            return False
                        continue
                    found = False
                    for target in targets:
                        if not assigned <= target:
                            continue
                        available = target-assigned
                        if len(available) != len(rest) or available & used:
                            continue
                        if any(all(image in domains[v] for v, image in zip(rest, order, strict=True))
                               for order in permutations(available)):
                            found = True
                            break
                    if not found:
                        return False
                return True
            def search(used):
                if not possible(used):
                    return None
                pending = [v for v in range(15, 23) if assignment[v] is None]
                if not pending:
                    mapping = {
                        "centers": list(assignment),
                        "anchors": [(shift+sign*j-(sign < 0)) % 15 for j in range(15)],
                        "orientation": sign, "shift": shift}
                    validate_embedding(mapping, 24, target_faces, proof)
                    return mapping
                v = min(pending, key=lambda u: (len(domains[u]-used), -len(source_incident[u]), u))
                for image in sorted(domains[v]-used):
                    assignment[v] = image
                    result = search(used | {image})
                    if result is not None:
                        return result
                assignment[v] = None
                return None
            answer = search(set(assignment[:15]))
            if answer is not None:
                return answer
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    stage, output = args.stage.resolve(), args.output.resolve()
    assert stage.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    proof = own_core_gate()
    inputs = read(stage / "INPUT-BINDINGS.json")
    assert (inputs["N"], inputs["B"]) == (24, 15)
    found, unmatched, completed, frozen = [], [], 0, {}
    with (stage / "JOBS.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            descriptor = json.loads(line, object_pairs_hook=no_duplicate_keys)
            directory = stage / f"batch-{descriptor['job']:06}"
            terminalpath, summarypath = directory / "TERMINAL.json", directory / "SUMMARY.json"
            if not terminalpath.exists() or not summarypath.exists():
                continue
            terminal, summary = read(terminalpath), read(summarypath)
            assert terminal["actual_exit_code"] == 0 and terminal["actual_child_terminal_observed"]
            assert summary["source_sha256"] == sha(ROOT / "small_order_parent_fillings.py")
            completed += 1
            for item in summary["outcomes"]:
                if item["status"] != "pending-complete-family":
                    continue
                family = directory / f"parent-{item['parent_index']:07}"
                old, exact = read(family / "PROPOSAL.json"), read(family / "EXACT.json")
                assert exact["verified"] and exact["pending_complete_leaves"] > 0
                assert sha(family / "PROPOSAL.json") == item["proof_sha256"]
                assert sha(family / "EXACT.json") == item["exact_sha256"]
                for nodeindex, node in enumerate(old["nodes"]):
                    if node["kind"] != "FULL_PENDING":
                        continue
                    state = node["state"]
                    mapping = find_embedding(state["next"], state["faces"], proof)
                    result = {
                        "parent_index": item["parent_index"], "family": str(family),
                        "node_index": nodeindex, "full_faces": state["faces"],
                        "actual_worker_report_sha256": sha(summarypath),
                        "original_proposal_sha256": sha(family / "PROPOSAL.json")}
                    if mapping is None:
                        unmatched.append(result)
                    else:
                        found.append({**result, "core_to_actual_complete_map": mapping,
                                      "transport": validate_embedding(mapping, 24, state["faces"], proof)})
                for path in (summarypath, terminalpath, family / "INPUT-COLLAR.json",
                             family / "PROPOSAL.json", family / "EXACT.json"):
                    frozen[str(path)] = sha(path)
    for path in (Path(__file__), COREPATH, SYSTEMPATH):
        frozen[str(path)] = sha(path)
    output.mkdir()
    publish(output / "OBSERVATION.json", {
        "N": 24, "B": 15, "actually_completed_worker_batches": completed,
        "matched_actual_full_leaves": found, "unmatched_actual_full_leaves": unmatched,
        "old_complete_core_mathematics_reused_under_exact_own_graph_identity": True,
        "not_a_whole_family_or_parent_payment_until_original_branch_tree_reaccepted": True,
        "source_sha256": sha(Path(__file__)), "frozen_files": frozen,
        "global_optimality_proved": False})
    print("Actual N24 full-leaf own core identity search:", len(found),
          "matched", len(unmatched), "unmatched; no whole-family payment yet", flush=True)


if __name__ == "__main__":
    main()
