"""C24: determine the exact relation between (rho, theta, R) at a sharp ring site
by direct construction instead of guessing.

Construction: choose theta (half-gap) and rho; put
    P = unit at -theta,  Q = unit at +theta   (so mid direction = 1, |M| = cos theta)
    c = rho * (cos sigma, sin sigma)
and solve the single condition  |c - P| = |c - Q|  (=> c lies on the bisector:
cos sigma = 1/(2 rho cos theta)); then R = |c - P|.
We tabulate rho vs theta vs R and test closed forms numerically.
"""
import math
import numpy as np
from pathlib import Path
import json

HERE = Path(__file__).parent
OUT = HERE / "out"


def solve_rho(theta, target_R):
    """for fixed theta find rho with |c-P| = |c-Q| and R = target_R."""
    cosT = math.cos(theta)
    R = target_R
    # |c-P|^2 = R^2 with the bisector constraint c·(P-Q)=0  <=>
    # |c|^2 - 2 c·P + 1 = R^2 ;  c·(P-Q)=0 gives c·n = cos(theta) with n=(1,0)
    # c = rho (cos s, sin s); rho cos s = cos(theta); c·P = cos(theta)cos(theta)/rho + sin(theta) sin s
    # and rho sin s = +-sqrt(rho^2 - cos^2 theta)
    # => |c-P|^2 = rho^2 - 2c·P + 1 = R^2
    # Solve by bisection on rho.
    def resid(rho):
        if rho < cosT:
            return None
        s = math.sqrt(rho * rho - cosT * cosT)
        cdotP = cosT * cosT / rho + math.sin(theta) * s / rho
        return rho * rho - 2 * cdotP + 1 - R * R

    lo, hi = cosT + 1e-12, 5.0
    flo = resid(lo)
    fhi = resid(hi)
    if flo is None or flo * fhi > 0:
        # try the other sign of s (site on the other side)
        def resid2(rho):
            if rho < cosT:
                return None
            s = math.sqrt(rho * rho - cosT * cosT)
            cdotP = cosT * cosT / rho - math.sin(theta) * s / rho
            return rho * rho - 2 * cdotP + 1 - R * R
        flo = resid2(lo); fhi = resid2(hi)
        if flo is None or flo * fhi > 0:
            return None
        for _ in range(200):
            mid = (lo + hi) / 2
            if resid2(mid) * flo <= 0:
                hi = mid
            else:
                lo = mid; flo = resid2(mid)
        return (lo + hi) / 2
    for _ in range(200):
        mid = (lo + hi) / 2
        if resid(mid) * flo <= 0:
            hi = mid
        else:
            lo = mid; flo = resid(mid)
    return (lo + hi) / 2


def main():
    R = 0.37998385311983884
    print("theta(deg)  rho        rho*cos      1-rho*cos    rho*sin      rho*cos+R*sin   R*?   cos^2?")
    rows = []
    for dth in (10, 16.08991, 19.52887, 21.31452, 21.94497, 22.24345, 25, 30):
        th = math.radians(dth)
        rho = solve_rho(th, R)
        if rho is None:
            print(f"  {dth:8.5f}   no solution")
            continue
        rows.append((dth, th, rho))
        print(f"  {dth:8.5f} {rho:.9f}  {rho*math.cos(th):.9f}  {1-rho*math.cos(th):.9f}"
              f"  {rho*math.sin(th):.9f}   {rho*math.cos(th)+R*math.sin(th):.9f}"
              f"   {R/math.sin(th):.6f}  {math.cos(th)**2:.6f}")
    print("\ncandidate values for comparison:")
    print("   site 7: theta=21.94497 rho=0.858810938")
    print("   site 1: theta=22.24345 rho=0.892521730")
    print("   site 6: theta=16.08991 rho=0.700870054")
    print("\nfitted relation rho vs theta with R fixed:")
    ths = np.array([r[1] for r in rows]); rhos = np.array([r[2] for r in rows])
    for name, f in (("cos", np.cos(ths)), ("1/cos", 1 / np.cos(ths)),
                    ("cos/(1-sin^2)", np.cos(ths) / (1 - np.sin(ths) ** 2)),
                    ("sqrt(1-2sin^4)", np.sqrt(1 - 2 * np.sin(ths) ** 4)),
                    ("cos+sin*tan", np.cos(ths) + np.sin(ths) * np.tan(ths)),
                    ("(1-sqrt(1-R^2/sin^2*0))/1", np.ones_like(ths))):
        if name == "(1-sqrt(1-R^2/sin^2*0))/1":
            continue
        ratio = rhos / f
        print(f"   rho/{name:16s}: min={ratio.min():.9f} max={ratio.max():.9f}")
    OUT.mkdir(exist_ok=True)
    (OUT / "c24_relation.json").write_text(json.dumps(
        [{"theta_deg": r[0], "rho": r[2]} for r in rows], indent=2))
    print("wrote", OUT / "c24_relation.json")


if __name__ == "__main__":
    main()
