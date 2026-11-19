#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Independently verify that 17 rational disks of a fixed rational radius cover D."""
from fractions import Fraction

SCALE = 2**104
RADIUS = Fraction("0.29853158925642805986984377443")
# Coordinates in units of 1/SCALE. Source candidate midpoint is pinned
# in docs/DISKCOVER_NATIVE_N17.md; no property of its root is assumed.
CENTERS = (
    (16512838745897630030122690509402, -4738421005370086605377925374791),
    (15045682948222421075623307212856, 3039571024351591314170664336750),
    (14099658054904989451429234725221, 11820186033602057015202858716824),
    (4967600896264944567840919204038, 17328590092441402040082206195105),
    (-3915984213360430165604000167331, 15408890041368456714560637977294),
    (-12084941840386577743570797698590, 12543710160529118852991241543514),
    (-15411703811233932188303462358789, 4422446206339633450770412557314),
    (-16897394468579105474219568233000, -4227120065732676472632360336542),
    (-11490642332708802908841495270717, -10987900775308835445311195625302),
    (-4976660907250916544149675222501, -17325990288311692439424806167992),
    (5686706781172037367441542545381, -17497957627082660339834475148456),
    (11144672204215813878109744134868, -10554991655661701152843011505153),
    (-65258772735924896155248880382, -8506948850326619179857349012137),
    (-6187513278595775385573839181827, -2151321382184360826494284794250),
    (-4105316897997602495967823299685, 5104887602020049650251756797276),
    (4455444323593885400527191507779, 7247168642224866282449865640840),
    (5224465213056715218661317785628, -1499179885925031199586207676040),
)


def verify():
    """A finite exact cover check. Raise rather than accepting an unproved cell."""
    s = SCALE
    near = lambda a, b: max(0, a, -b)
    bound_num = (RADIUS.numerator * s)**2
    bound_den = RADIUS.denominator**2
    stack = [(-s, s, -s, s)]
    outside = inside = split = 0
    while stack:
        x0, x1, y0, y1 = stack.pop()
        if near(x0, x1)**2 + near(y0, y1)**2 > s*s:
            outside += 1
            continue
        if any(
            (max(abs(x0-x), abs(x1-x))**2 + max(abs(y0-y), abs(y1-y))**2)
            * bound_den <= bound_num
            for x, y in CENTERS
        ):
            inside += 1
            continue
        if x1-x0 <= 1 or y1-y0 <= 1:
            raise RuntimeError(f"Unverified terminal cell: {x0, x1, y0, y1}")
        mx, my = (x0+x1)//2, (y0+y1)//2
        stack.extend((a, b, c, d) for a, b in ((x0, mx), (mx, x1))
                     for c, d in ((y0, my), (my, y1)))
        split += 1
    return inside, outside, split


if __name__ == "__main__":
    inside, outside, split = verify()
    print(f"n=17 exact upper <= {RADIUS}: {inside} covered cells, "
          f"{outside} outside cells, {split} subdivisions")
