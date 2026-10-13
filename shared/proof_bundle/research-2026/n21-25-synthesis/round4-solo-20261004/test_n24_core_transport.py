"""Own exact core identity controls and literal entire accepted-source location."""
from pathlib import Path
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish
from stream_catalog import sha
from group_catalog import canonical, canonical_full
from n24_actual_core_transport import own_core_gate, find_embedding, validate_embedding, SYSTEMPATH, COREPATH
from small_order_collar_lower_pipeline import source_gate, rows

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    proof, system = own_core_gate(), read(SYSTEMPATH)
    full = sorted(sum(1 << v for v in face) for face in system["all_faces"])
    code = list(canonical_full(24, 15, full))
    mapping = find_embedding(24, code, proof)
    assert mapping is not None
    validate_embedding(mapping, 24, code, proof)
    identity = [i for i in range(24) if system["center_core_nodes"][i] is not None]
    positive_maps = []
    for sign, shift in ((1, 0), (1, 7), (-1, 0), (-1, 4), (-1, 14)):
        labels = [(shift+sign*j) % 15 for j in range(15)]+list(range(15, 24))
        transformed = sorted(sum(1 << labels[v] for v in range(24) if mask >> v & 1) for mask in full)
        m = {
            "centers": [labels[v] for v in identity],
            "anchors": [(shift+sign*j-(sign < 0)) % 15 for j in range(15)],
            "orientation": sign, "shift": shift}
        result = validate_embedding(m, 24, transformed, proof)
        assert find_embedding(24, transformed, proof) is not None
        positive_maps.append({"orientation": sign, "shift": shift, "map": m, "result": result})
    refuses = []
    def reject(name, centers, faces, testmap=mapping, testproof=proof):
        try:
            validate_embedding(testmap, centers, faces, testproof)
        except (AssertionError, KeyError, ValueError):
            refuses.append(name)
        else:
            raise AssertionError("invalid own core transport accepted: "+name)
    wrong = deepcopy(mapping)
    wrong["centers"][-1] = wrong["centers"][-2]
    reject("noninjective-centers", 24, code, wrong)
    wrong = deepcopy(mapping)
    wrong["centers"][-1] = 14
    reject("internal-center-to-boundary", 24, code, wrong)
    wrong = deepcopy(mapping)
    wrong["anchors"][0] = wrong["anchors"][1]
    reject("wrong-boundary-anchor", 24, code, wrong)
    reflected = positive_maps[2]["map"]
    refl_faces = sorted(sum(1 << ((-v) % 15 if v < 15 else v)
                            for v in range(24) if mask >> v & 1) for mask in full)
    wrong = deepcopy(reflected)
    wrong["anchors"] = [(-j) % 15 for j in range(15)]
    reject("reflection-without-one-anchor-offset", 24, refl_faces, wrong)
    reject("target-not-full24", 23, code)
    reject("deleted-full-face", 24, code[:-1])
    wrongproof = deepcopy(proof)
    wrongproof["N"] = 23
    reject("N23-core-cannot-pay-N24", 24, code, testproof=wrongproof)
    stage = ROOT / "n24-B15-s1"
    source = source_gate(stage)
    outercode, outermap = canonical(24, 15, full, 1)
    matches = []
    for original in rows(stage, source):
        if original["faces"] == list(outercode):
            assert original["centers"] == len(outermap["centers"])
            matches.append(original)
    assert len(matches) == 1, "actual complete source must retain own attaining outer"
    observation = read(ROOT / "n24-B15-actual-core-leaf-observation-v1/OBSERVATION.json")
    assert observation["unmatched_actual_full_leaves"]
    actual_bad = observation["unmatched_actual_full_leaves"][0]["full_faces"]
    assert find_embedding(24, actual_bad, proof) is None
    reject("actual-full-pending-graph-does-not-contain-core", 24, actual_bad)
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N24-own-core-full-type-subgraph-transport-controls-and-attaining-parent-identity-v1",
        "N": 24, "B": 15, "source_core_centers": 23, "active_core_faces": 20,
        "true_candidate_full31face_positive_and_five_correct_dihedral_maps": positive_maps,
        "negative_actual_core_transport_controls_rejected": refuses,
        "actual_entire_necessary_source_attaining_parent": matches[0],
        "actual_attaining_outer_exactly_present_in_complete_original_source": True,
        "complete_parent_source_acceptance_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json"),
        "whole_completion_family_and_actual_parent_adoption_not_performed_here": True,
        "own_nonstrict_core_proof_sha256": sha(COREPATH), "system_sha256": sha(SYSTEMPATH),
        "source_sha256": sha(Path(__file__)),
        "transport_source_sha256": sha(ROOT / "n24_actual_core_transport.py"),
        "global_optimality_proved": False})
    print("N24 own exact full-core transport controls and actual attaining parent identity accepted:",
          matches[0]["id"], "; no whole-parent payment", flush=True)


if __name__ == "__main__":
    main()
