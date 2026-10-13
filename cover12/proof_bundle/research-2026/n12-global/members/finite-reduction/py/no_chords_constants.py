"""no_chords_constants.py -- exact rational verification of the constant chain used in
lead/NINE-RING-NO-CHORDS.md (independent of decimal inverse-trig evaluation).

Chain to verify (all comparisons exact, integer/Fraction arithmetic only):
  C1  U < 4/11                                   (U = registered C182 rational)
  C2  4/11 < 3/8 < sqrt(2-sqrt 2)/2 = sin(pi/8)  (so r<=U < sin(pi/8), arc<pi/4)
  C3  2U < 8/11
  C4  sin(41/50) >= 41/50 - (41/50)^3/6 > 8/11   (Taylor, first two alternating terms)
  C5  sin(373/1000) >= 373/1000 - (373/1000)^3/6 > 4/11
  C6  => asin(2r) < 41/50 and asin r < 373/1000 for r <= U
  C7  41/50 + 6*373/1000 = 1529/500 = 3.058
  C8  3(sqrt 6 - sqrt 2) > 1529/500           (inscribed regular dodecagon: pi > 12 sin(pi/12))
  C9  hence asin(2r) + 6 asin r < 3.058 < pi
Usage: py -3 -B no_chords_constants.py
"""
from __future__ import annotations

from fractions import Fraction as F

U = F(22568935234031792038557518369, 62500000000000000000000000000)


def main():
    checks = []

    def chk(name, ok, detail=""):
        checks.append((name, bool(ok), detail))
        print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

    # C1
    chk("C1 U < 4/11", U < F(4, 11), f"U={U} vs 4/11")

    # C2: 4/11 < 3/8 and 3/8 < sqrt(2-sqrt2)/2  <=>  sqrt2 < 23/16  <=>  2 < 529/256
    chk("C2a 4/11 < 3/8", F(4, 11) < F(3, 8), "32 < 33")
    chk("C2b sqrt2 < 23/16 (=> 3/8 < sin(pi/8))", 2 * 256 < 529,
        "(23/16)^2=529/256 > 2=512/256")
    chk("C2c sin(pi/8) = sqrt(2-sqrt2)/2", True, "identity")

    # C3
    chk("C3 2U < 8/11", 2 * U < F(8, 11), "")

    # C4: 41/50 - (41/50)^3/6 > 8/11
    a = F(41, 50)
    t4 = a - a ** 3 / 6
    chk("C4 sin(41/50) lower bound > 8/11", t4 > F(8, 11),
        f"{t4} = {t4.numerator}/{t4.denominator} > 8/11 ({t4.numerator*11} > {8*t4.denominator})")

    # C5: 373/1000 - (373/1000)^3/6 > 4/11
    b = F(373, 1000)
    t5 = b - b ** 3 / 6
    chk("C5 sin(373/1000) lower bound > 4/11", t5 > F(4, 11),
        f"{t5} > 4/11")

    # C6: monotonicity of asin on [0,1] and 41/50, 373/1000 in (0,1)
    chk("C6a 41/50 in (0,1)", 0 < F(41, 50) < 1, "")
    chk("C6b 373/1000 in (0,1)", 0 < F(373, 1000) < 1, "")
    chk("C6c 2r <= 2U < 8/11 < sin(41/50) => asin(2r) < 41/50",
        (2 * U < F(8, 11)) and (F(8, 11) < t4), "asin increasing")
    chk("C6d r <= U < 4/11 < sin(373/1000) => asin r < 373/1000",
        (U < F(4, 11)) and (F(4, 11) < t5), "asin increasing")

    # C7
    s = F(41, 50) + 6 * F(373, 1000)
    chk("C7 sum = 1529/500 = 3.058", s == F(1529, 500), f"{s}")

    # C8: 3(sqrt6 - sqrt2) > 1529/500  <=>  sqrt6 - sqrt2 > 1529/1500
    #   (sqrt6-sqrt2)^2 = 8 - 4 sqrt3, and 8 - 4 sqrt3 > (1529/1500)^2
    #   <=> 4 sqrt3 < 8 - (1529/1500)^2  <=> 3 < ((8 - (1529/1500)^2)/4)^2
    rhs = 8 - (F(1529, 1500)) ** 2
    lhsq = rhs / 4
    chk("C8 3(sqrt6-sqrt2) > 1529/500", 3 < lhsq ** 2,
        f"4sqrt3 < {rhs} <=> 3 < (rhs/4)^2 = {lhsq**2}")

    # C9: pi > 12 sin(pi/12) = 3(sqrt6-sqrt2) (inscribed regular dodecagon perimeter)
    chk("C9 pi > 12 sin(pi/12) > 1529/500", True,
        "inscribed regular 12-gon: 2*pi > 12*2*sin(pi/12)")

    fails = [c for c in checks if not c[1]]
    print(f"\n{len(checks) - len(fails)}/{len(checks)} exact checks passed")
    if fails:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
