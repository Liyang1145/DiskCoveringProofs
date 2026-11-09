"""Exact angular deficit upper bounds for exterior arcs with b>=15."""

import argparse
import json
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path

from rational_trig import pi_bounds
from verify_fan import c_bounds, fan_line, require
from verify_patch14 import ARC_CAP, RADIUS
from verify_seam import seam_upper


def verify(entries):
    pi0, pi1 = pi_bounds()
    groups = defaultdict(dict)
    for row in entries:
        n, b, m = row["n"], row["b"], row["m"]
        require(n in (25, 26) and 15 <= b <= n - 9 and 1 <= m < b, "Invalid arc group")
        half, lam, tau, a, d, c, e = map(Q, (
            row["half"], row["lambda"], row["tau"], *row["small"], *row["large"],
        ))
        require(0 <= tau < lam < Q(1, 2) and 0 < half < m*ARC_CAP/2 and d > e,
                "Invalid fan constants")
        lo, hi = c_bounds(lam)
        offset = (2*c_bounds(lam-tau)[1] + seam_upper(lam, tau, 2) - 4*lo) if tau else Q(0)
        fan_line(RADIUS, lam-tau, a, d, offset=offset)
        fan_line(RADIUS, lam-tau, c, e, offset=offset)
        p = 2*n*lam - 2*tau + e
        area = RADIUS**2 * (p*(pi0 if p <= 0 else pi1) + (6*n-6)*hi
                             + m*a + (b-m)*c + (d-e)*half)
        require(area < pi0, f"Window not excluded for n={n}, b={b}, m={m}")
        delta = m*ARC_CAP - 2*half
        previous = groups[n, b].get(m, delta)
        groups[n, b][m] = min(previous, delta)
    return groups


def model_windows(file, n, b):
    rows = json.loads(Path(file).read_text(encoding="utf-8"))
    selected = [row for row in rows if (row["n"],row["b"]) == (n,b)]
    return verify(selected).get((n,b),{})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    result = verify(json.loads(args.certificate.read_text(encoding="utf-8")))
    for (n, b), rows in sorted(result.items()):
        print(f"PASS n={n} b={b} angular deficit upper bounds "
              f"{[(m, float(x)) for m, x in sorted(rows.items())]}")


if __name__ == "__main__":
    main()
