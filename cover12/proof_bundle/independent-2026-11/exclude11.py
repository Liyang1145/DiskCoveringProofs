"""Integer certificate excluding 11 or 12 boundary disks at radius 0.361103."""
from bisect import bisect_left
from math import factorial, isqrt

GRID = 10**6
RADIUS = 361103
ANGLE_GRID = 100000
COS_SCALE = 10**12
PI_LOWER = 314159
PI_UPPER = 314160

# Each inner-center interval has width 0.006.
WEIGHTS = (
    {37: 305, 100: 695},
    {38: 283, 100: 717},
    {38: 283, 100: 717},
    {35: 4, 39: 260, 100: 736},
    {34: 19, 35: 20, 40: 232, 100: 728},
    {34: 49, 35: 3, 40: 229, 100: 719},
    {33: 33, 34: 21, 35: 16, 36: 18, 37: 1, 41: 202, 100: 708},
    {32: 14, 33: 59, 34: 5, 35: 16, 36: 18, 37: 1, 41: 197, 100: 690},
    {32: 62, 33: 11, 34: 22, 35: 21, 36: 14, 37: 16, 38: 2, 42: 173, 100: 679},
    {31: 37, 32: 37, 33: 24, 34: 23, 35: 19, 36: 18, 37: 13, 38: 14, 39: 3, 43: 150, 100: 661},
    {31: 95, 33: 26, 34: 22, 35: 19, 36: 18, 37: 13, 38: 14, 39: 3, 43: 146, 100: 645},
    {30: 61, 31: 34, 32: 30, 33: 25, 34: 22, 35: 19, 36: 16, 37: 15, 38: 12, 39: 12, 40: 4, 44: 125, 100: 623},
    {29: 39, 30: 116, 32: 27, 33: 24, 34: 20, 35: 18, 36: 15, 37: 14, 38: 11, 39: 11, 40: 4, 44: 117, 100: 582},
    {29: 134, 30: 19, 31: 35, 32: 28, 33: 23, 34: 20, 35: 17, 36: 15, 37: 14, 38: 12, 39: 10, 40: 10, 41: 6, 45: 99, 100: 559},
)

def cosine_table():
    denominator = factorial(16) * ANGLE_GRID**16
    coefficients = [
        (-1)**k * (denominator // (factorial(2*k)*ANGLE_GRID**(2*k)))
        for k in range(8, -1, -1)
    ]
    table = []
    for i in range(PI_LOWER + 1):
        i2 = i*i
        polynomial = coefficients[0]
        for coefficient in coefficients[1:]:
            polynomial = polynomial*i2 + coefficient
        table.append((-COS_SCALE*polynomial) // denominator)
    assert all(a <= b for a, b in zip(table, table[1:]))
    return table

def max_half_angle(cosines, s, left, right, radius=RADIUS):
    """Scaled upper bound on the half-angle of the arc hit by one disk."""
    a = s*s - radius*radius
    if a < 0 and left == 0:
        return PI_UPPER
    if right*right <= a:
        t = right
    elif left*left >= a:
        t = left
    else:
        scale = 10**8
        lower = (COS_SCALE*isqrt(a*scale*scale)) // (scale*s)
        return min(bisect_left(cosines, -lower), PI_UPPER)
    lower = (COS_SCALE*(a + t*t)) // (2*s*t)
    return min(bisect_left(cosines, -lower), PI_UPPER)

def certify_boundary_count():
    # 12 outer disks cannot cover the origin. If there are 11 outer
    # disks, the 12th covers the concentric disk of radius 1-2r alone.
    assert 3*RADIUS - GRID <= 84_000
    cosines = cosine_table()
    rings = sorted(set().union(*(row.keys() for row in WEIGHTS)))
    maxima = [0]*len(WEIGHTS)
    for lo in range(GRID-RADIUS, GRID, 100):
        hi = min(lo+100, GRID)
        arcs = {s: max_half_angle(cosines, s*10_000, lo, hi) for s in rings}
        for j, row in enumerate(WEIGHTS):
            maxima[j] = max(maxima[j], sum(w*arcs[s] for s, w in row.items()))

    margins = []
    for j, row in enumerate(WEIGHTS):
        lo, hi = 6000*j, 6000*(j+1)
        inside = sum(w*max_half_angle(cosines, s*10_000, lo, hi) for s, w in row.items())
        margin = PI_LOWER*sum(row.values()) - 11*maxima[j] - inside
        assert margin > 0
        margins.append(margin/sum(row.values())/ANGLE_GRID)
    print(f"11 boundary disks excluded. Minimum weighted angular margin {min(margins):.6f}")

if __name__ == "__main__":
    certify_boundary_count()

