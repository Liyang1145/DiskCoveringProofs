"""Exact own25 half-core/circle family budget, no generic core transplant."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
import exact_graph as exact
sys.path.insert(0, str(exact.kernel.ARCS))
import exact_arcs as arcs

assert __debug__
CONSTANTSPATH = ROOT.parent / "evidence/core-reduction/constants/n25.json"
UPPERPATH = ROOT / "n25-exact-upper-fresh/VERIFIED.json"


def gate(constants, upper):
    assert constants["verified"] and type(constants["N"]) is int and constants["N"] == 25
    assert upper["verified"] and upper["actual_cover_radius_equals_r"]
    assert upper["statement"] == "The specified 25 equal disks cover the entire closed unit disk with radius 1/(sqrt(6)+sqrt(3))"
    U, D = F(constants["radius_upper"]), constants["angle_scale"]
    assert U == F(239146311738101, 10**15) and 0 < U < F(1, 4)
    # R^2=1-2sqrt2/3, so U>R iff (3/2(1-U^2))^2<2.
    alpha = F(3, 2)*(1-U*U)
    assert alpha > 0 and alpha*alpha < 2
    assert F(upper["r_strict_interval"][1]) < U
    q = U/(1-2*U)
    assert q < F(1, 2)
    assert constants["ratio_core"] == str(q)
    assert D == 10**7
    caps = constants["angle_caps"]+[4058615]
    assert caps == [768677, 1587443, 2546859, 4058615]
    sine_gaps = []
    for k, cap in enumerate(caps, 1):
        lower = F(arcs.sincos_turn(F(cap, 2*D))[1][0], arcs.SCALE)
        gap = lower-k*U
        assert gap > 0
        sine_gaps.append(str(gap))
    circle_gap = D-13*caps[0]
    assert circle_gap > 0
    direct_lower = F(arcs.sincos_turn(F(1, 26))[1][0], arcs.SCALE)
    assert direct_lower > U
    assert constants["minimum_boundary_cells"] == 14
    assert constants["minimum_interior_cells"] == 8
    assert constants["maximum_boundary_cells"] == 17
    assert constants["families"] == [[14, 11], [15, 10], [16, 9], [17, 8]]
    return {
        "radius_upper": str(U), "exact_root_squared_comparison_gap": str(2-alpha*alpha),
        "quarter_radius_gap": str(F(1, 4)-U),
        "normalized_core_radius_upper": str(q), "strict_half_core_gap": str(F(1, 2)-q),
        "direct_13_boundary_capacity_sine_gap": str(direct_lower-U),
        "strict_integer_circle_budget_gap_D_minus13A": circle_gap,
        "own_two_four_six_eight_rod_caps": caps, "own_positive_exact_sine_gaps": sine_gaps,
        "necessary_boundary_internal_families": constants["families"]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    constants, upper = read(CONSTANTSPATH), read(UPPERPATH)
    result = gate(constants, upper)
    refused = []
    for field, value in (
        ("N", 24), ("verified", False), ("radius_upper", "1/4"), ("radius_upper", "1/3"),
        ("radius_upper", "61325412542131/250000000000000"), ("angle_scale", 1000000),
        ("angle_caps", [788872, 1632237, 2632431]), ("angle_caps", [768676, 1587443, 2546859]),
        ("minimum_boundary_cells", 13), ("minimum_interior_cells", 7),
        ("maximum_boundary_cells", 18), ("families", [[14, 11], [15, 10], [17, 8]]),
        ("ratio_core", "1/2")):
        wrong = deepcopy(constants)
        wrong[field] = value
        try:
            gate(wrong, upper)
        except (AssertionError, KeyError):
            refused.append(field+"-"+str(len(refused)))
        else:
            raise AssertionError("incorrect own25 budget accepted: "+field)
    wrong = deepcopy(upper)
    wrong["actual_cover_radius_equals_r"] = False
    try:
        gate(constants, wrong)
    except AssertionError:
        refused.append("no-same-root-whole-disk-upper")
    else:
        raise AssertionError("unbound whole disk upper accepted")
    assert len(refused) == 14
    output.mkdir()
    paths = (
        Path(__file__), CONSTANTSPATH, UPPERPATH, arcs.__file__,
        ROOT / "NECESSARY-OUTER-COLLAR-ARBITRARY-COVER-INDUCTION-v1.md")
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "own-N25-exact-root-and-half-core-boundary-family-budget-v1",
        "N": 25, **result, "negative_scope_and_threshold_controls_rejected": refused,
        "half_core_uses_self_contained_arbitrary_seven_disk_lower_not_candidate_optimality": True,
        "written_cover_and_simple_graph_transport_requires_bound_induction": True,
        "no_N23_N24_force_core_or_radius_threshold_transplanted": True,
        "frozen_files": {str(Path(path).resolve()): sha(path) for path in paths},
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    print("Own25 exact arbitrary-cover family budget accepted: B14/15/16/17, I>=8;",
          "14 refusals; not full global proof", flush=True)


if __name__ == "__main__":
    main()
