"""Replay the exact core count above the enlarged minimum owner norm."""
import argparse
import json
from pathlib import Path

from polar_tables import CORE_CAPS, R, SCALE, TURN, beta
from weighted_rings import verify_weighted_rings

TEST = 345_500_000
LOWER = 901_500_000


def verify(source):
    p = json.loads(source.read_text(encoding="utf-8"))
    if p["test_radius"] != TEST or [rec["outer"] for rec in p["cases"]] != [11,12]:
        raise ValueError("unexpected scope for the auxiliary count")
    if not 0 < 3*TEST-SCALE < SCALE-TEST or 2*TEST >= SCALE:
        raise ValueError("invalid auxiliary core ranges")
    for rec in p["cases"]:
        n = rec["outer"]
        rings = rec["rings"]
        if not rings or any(not 0 < s <= SCALE or w <= 0 for s,w in rings):
            raise ValueError("invalid ring weights")
        inner_hi = SCALE-TEST if n == 11 else 3*TEST-SCALE
        counts = verify_weighted_rings(
            TEST, rings, [(n,SCALE-TEST,SCALE,rec["caps"][0]),
                          (13-n,0,inner_hi,rec["caps"][1])])
        print(f"PASS 13 disks: at test radius 0.3455, at most ten large-norm disks ({n} excluded in {sum(counts)} boxes).")

    s = LOWER-R-1000
    if TEST*s < R*SCALE or s <= 2*R:
        raise ValueError("the scaled core lies outside the auxiliary count")
    full = beta(s,s-R,s+R)
    if 16*full >= TURN:
        raise ValueError("eight disks may cover the core circle")
    if 2*(8*full+beta(s,s-R,CORE_CAPS[4])) >= TURN:
        raise ValueError("nine disks may cover the core circle with the fourth norm cap")
    print(f"PASS B=14: D1 >= {LOWER}/1e9 forces exactly ten of the thirteen inner disks to reach radius {s}/1e9.")

    for lower, anchors, phases in [(LOWER,8,4),(905_600_000,9,4)]:
        core = lower-R-1000
        clearance = TURN*(phases-1)//(2*anchors*phases)
        if (beta(core,core-R,CORE_CAPS[3]) >= clearance
                or 2*anchors*beta(core,core-R,core+R) >= TURN):
            raise ValueError("invalid core anchor phase reduction")
        print(f"PASS B=14: D1 >= {lower}/1e9 admits {anchors} distinct core anchors in one of four phases, omitting a minimum-norm core disk.")

    for lower,small in [(LOWER,5),(903_910_000,4),(912_250_000,3)]:
        core = lower-R-1000
        best = beta(core,core-R,core+R)
        short = beta(core,core-R,CORE_CAPS[3])
        if not 0<short<best or 2*((10-small)*best+small*short)>=TURN:
            raise ValueError("unproved core norm multiplicity")
        print(f"PASS B=14: D1 >= {lower}/1e9 allows at most {small-1} of the ten core norms at or below 0.498.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    verify(parser.parse_args().source)
