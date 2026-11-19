"""Integer arithmetic certificate for the global lower bound 0.3545."""
from exclude11 import ANGLE_GRID, GRID, PI_LOWER, cosine_table, max_half_angle

RADIUS = 354500

# Radii are in units of 1/10000. Weights need not be normalized.
WEIGHTS = (
    {
        3950: 9608, 4000: 9207, 4050: 8823, 4100: 8491, 4150: 8153,
        4200: 7851, 4250: 7569, 4300: 7280, 4350: 7033, 4400: 6777,
        4450: 6536, 4500: 6317, 4550: 6082, 4600: 5880, 4650: 5671,
        4700: 5464, 4750: 5277, 4800: 5076, 4850: 4894, 4900: 4710,
        4950: 4521, 5000: 4348, 5050: 4163, 5100: 3984, 5150: 3811,
        5200: 3619, 5250: 3449, 5300: 3257, 5350: 3071, 5400: 2874,
        5450: 2678, 5500: 2448, 5550: 2268, 5600: 1938, 5650: 1821,
        5700: 1246, 5750: 1274, 5800: 45, 6550: 29, 10000: 812458,
    },
    {
        3200: 43205, 3300: 32429, 3400: 31188, 3500: 16145, 3600: 17709,
        3700: 34724, 3800: 37267, 3900: 21808, 4100: 1066, 4200: 12489,
        4300: 11589, 4400: 10785, 4500: 10037, 4600: 9355, 4700: 8691,
        4800: 8098, 4900: 7467, 5000: 6956, 5100: 6262, 5200: 5904,
        5300: 4933, 5400: 4988, 5500: 3120, 5600: 4188, 5700: 2145,
        10000: 647453,
    },
)


def certify_lower_bound():
    # Radius below sin(pi/8) requires at least nine boundary disks.
    table = cosine_table()
    break_point = GRID-RADIUS
    maxima = [[0, 0], [0, 0]]
    radii = sorted(set().union(*(row.keys() for row in WEIGHTS)))
    for category, (start, stop) in enumerate(((0, break_point), (break_point, GRID))):
        for left in range(start, stop, 50):
            right = min(left+50, stop)
            angles = {
                s: max_half_angle(table, 100*s, left, right, RADIUS)
                for s in radii
            }
            for k, weights in enumerate(WEIGHTS):
                angle = sum(w*angles[s] for s, w in weights.items())
                maxima[k][category] = max(maxima[k][category], angle)

    for k, (m, weights, (inner, outer)) in enumerate(zip((9, 10), WEIGHTS, maxima)):
        if k == 1:
            assert outer <= inner
        margin = PI_LOWER*sum(weights.values())-(12-m)*inner-m*outer
        assert margin > 0
        print(f"m={m}: caps {inner}, {outer}; margin {margin} (integer units)")


if __name__ == "__main__":
    certify_lower_bound()
