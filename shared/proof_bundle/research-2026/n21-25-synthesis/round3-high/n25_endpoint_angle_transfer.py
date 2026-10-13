"""Exact graph/rod/geometry isomorphism transports the paid whole-angle theorem.

Given any realization of the positive core, relabel by the displayed cyclic
map and rotate the image of negative q0 to (1,0). This is a negative-core
realization in its own complete necessary angle domain. No geometry symmetry
is assumed for that arbitrary realization.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import n25_anchor_isolation as field
from stream_catalog import sha, no_duplicate_keys
from replay_n25_endpoint_domain import inputs

ROOT = Path(__file__).resolve().parent
Q = field.Q
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def check_isomorphism(negative, positive, pointmap):
    assert sorted(pointmap) == list(range(61))
    assert pointmap[:16] == [(j+2) % 16 for j in range(16)]
    target_edges = {frozenset(edge) for edge in positive["edges"]}
    images = {frozenset((pointmap[u], pointmap[v])) for u, v in negative["edges"]}
    assert images == target_edges and len(images) == 92
    centermap = [pointmap[16+j]-16 for j in range(25)]
    assert sorted(centermap) == list(range(25))
    assert centermap[:16] == [(j+2) % 16 for j in range(16)]
    for j in range(16):
        assert {centermap[j], centermap[(j+1) % 16]} == {
            pointmap[j], (pointmap[j]+1) % 16}
    faces = {tuple(sorted(face)) for face in positive["faces"]}
    assert {tuple(sorted(centermap[j] for j in face)) for face in negative["faces"]} == faces
    return centermap


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    replaypath = ROOT / "evidence/n25-endpoint-negative-angle-complete-independent-resume1.json"
    replay = read(replaypath)
    assert replay["verified"] and replay["entire_angle_domain_proved"] and replay["pending_boxes"] == 0
    assert replay["nodes"] == 426937
    assert replay["source_sha256"] == sha(ROOT / "replay_n25_endpoint_domain.py")
    treepath = ROOT / "evidence/n25-endpoint-negative-angle-prefix600001-resume1/endpoint-angle-tree.json.gz"
    assert replay["tree_sha256"] == sha(treepath)
    const, masks, _, bound, negative = inputs(-1)
    _, positivemasks, _, positivebound, positive = inputs(1)
    assert replay["input_sha256"] == bound == positivebound
    characterpath = ROOT / "evidence/n25-stress-character-resume2.json"
    character = read(characterpath)
    assert character["verified"] and character["source_sha256"] == sha(ROOT / "n25_stress_character.py")
    assert character["field_arithmetic_sha256"] == sha(ROOT.parent / "n25_algebraic_upper.py")
    record = next(row for row in character["generators"] if row["generator"] == "rotation_pi_over_4")
    rotation = record["point_permutation"]
    assert sorted(rotation) == list(range(73)) and rotation[:16] == [(j+2) % 16 for j in range(16)]
    assert record["fibre_character"] == -1
    targetlabels = {old: i for i, old in enumerate(positive["old_nodes_retained"])}
    pointmap = [targetlabels[rotation[old]] for old in negative["old_nodes_retained"]]
    centermap = check_isomorphism(negative, positive, pointmap)
    halfsqrt2 = Q.Q2(0, F(1, 2))
    for i, point in enumerate(negative["points_Qsqrt2"]):
        x, y = [Q.Q2(*v) for v in point]
        rotated = [halfsqrt2*(x-y), halfsqrt2*(x+y)]
        expected = [Q.Q2(*v) for v in positive["points_Qsqrt2"][pointmap[i]]]
        assert rotated == expected
    paidweights = {frozenset(edge): Q.Q2(*w) for edge, w in
                   zip(positive["edges"], positive["weights_Qsqrt2"], strict=True)}
    for edge, w in zip(negative["edges"], negative["weights_Qsqrt2"], strict=True):
        assert paidweights[frozenset(pointmap[v] for v in edge)] == Q.Q2(*w)
    rejected = []
    bad = list(pointmap)
    bad[16], bad[17] = bad[17], bad[16]
    for label, mapping in (("wrong-center-permutation", bad),
                           ("noninjective-point-map", [pointmap[1]]+pointmap[1:]),
                           ("wrong-anchor-cyclic-order", list(range(61)))):
        try:
            check_isomorphism(negative, positive, mapping)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("invalid full-angle transport accepted", label))
    report = {"verified": True, "N": 25, "B": 16,
              "negative_endpoint_whole_angle_replayed": True,
              "positive_endpoint_whole_angle_transferred": True,
              "both_endpoint_core_lower_bounds": True,
              "radius": "1/(sqrt(6)+sqrt(3))", "radius_squared": "1-2*sqrt(2)/3",
              "nodes_per_core": 61, "rods_per_core": 92,
              "negative_to_positive_point_map": pointmap,
              "negative_to_positive_center_map": centermap,
              "negative_to_positive_anchor_map": pointmap[:16],
              "candidate_geometry_rotated_exactly": True,
              "arbitrary_realization_symmetry_assumed": False,
              "normalization_for_arbitrary_realization": "relabel then rigidly rotate mapped q0 to (1,0)",
              "closed_domain_anchor_order_preserved": True,
              "negative_replay_sha256": sha(replaypath), "negative_tree_sha256": sha(treepath),
              "input_sha256": bound, "character_sha256": sha(characterpath),
              "source_sha256": sha(Path(__file__)), "negative_controls_rejected": rejected,
              "field_source_sha256": sha(ROOT.parent / "n25_algebraic_upper.py"),
              "global_optimality_proved": False,
              "scope": "two smaller specified positive cores entire angle domains, not all topologies"}
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Both N25 61-node cores WHOLE-ANGLE LOWER BOUNDS paid by fresh replay + exact cyclic isomorphism;",
          "no unrestricted-optimality claim", flush=True)


if __name__ == "__main__":
    main()
