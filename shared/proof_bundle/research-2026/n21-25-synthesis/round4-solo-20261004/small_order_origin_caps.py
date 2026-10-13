"""Exact N23/N24 angle caps, with the unchanged general eight-rod cycle law."""
from pathlib import Path
from fractions import Fraction as F
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


def parameters(N):
    assert type(N) is int and N in (23, 24)
    path = ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"
    constants = read(path)
    assert constants["verified"] and constants["N"] == N
    U = F(constants["radius_upper"])
    expected = {23: F(249953776586051, 10**15), 24: F(61325412542131, 250000000000000)}
    assert U == expected[N] and 0 < U < F(1, 4)
    D = constants["angle_scale"]
    assert D == 10**7
    lo, hi = constants["angle_caps"][-1], D//2-1
    while hi-lo > 1:
        mid = (hi+lo)//2
        lower = F(arcs.sincos_turn(F(mid, 2*D))[1][0], arcs.SCALE)
        if lower > 4*U:
            hi = mid
        else:
            lo = mid
    cap8 = hi
    caps = constants["angle_caps"]+[cap8]
    assert 0 < 2*caps[0] < caps[1] < caps[2] < caps[3] < D//2
    margins = []
    for k, cap in enumerate(caps, 1):
        lower = F(arcs.sincos_turn(F(cap, 2*D))[1][0], arcs.SCALE)
        assert lower > k*U
        margins.append(str(lower-k*U))
    return constants, cap8, {
        "N": N, "angle_scale": D, "caps2_4_6_8": caps,
        "radius_upper": str(U), "positive_exact_sine_margins": margins,
        "constants_sha256": sha(path), "eight_rod_integer_cycle_source_sha256": sha(ROOT / "eight_rod_possible.inc"),
        "independent_eight_rod_cycle_checker_sha256": sha(ROOT / "eight_rod_angles.py"),
        "exact_arcs_source_sha256": sha(Path(arcs.__file__)),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    output.mkdir()
    reports = [parameters(N)[2] for N in (23, 24)]
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "small-order-own-radius-eight-rod-exact-caps-v1",
        "orders": reports, "all_eight_rod_caps_derive_from_each_own_exact_threshold": True,
        "no_N25_threshold_transported_to_N23_N24": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("N23/N24 own exact eight-rod caps accepted:", [r["caps2_4_6_8"] for r in reports], flush=True)


if __name__ == "__main__":
    main()
