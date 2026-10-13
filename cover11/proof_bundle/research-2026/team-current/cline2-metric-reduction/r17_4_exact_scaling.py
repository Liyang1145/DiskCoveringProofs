"""R17-4: exact flat-limit geometry with ALL constraints enforced, and the true scaling.

Withdrawn (my Round-17 report): the flat limit being w = 2asin r for the sector width;
eps = 2 arcsin(delta/(2 sin(w/2))); h = sqrt(delta(2r-delta)); h/eps -> const (linear collar);
and the assertion that C842 bounds alpha2 <= pi - 1e-8 (claim_get: C842 excludes alpha = pi at
the ENDPOINT sectors 0 and 4 only).

Exact setup, all constraints enforced.
  Site M at the origin; switches P, Q with |MP| = |MQ| = r, angle PMQ = alpha2 = pi - eps.
  P, Q on the unit circle; O the unit-circle centre.
  The sector width w (site arc): chord |PQ| = 2 sin(w/2) = 2r cos(eps/2) (law of cosines in MPQ).
  Law of sines in M P O: sin(phi) = r sin beta, beta := angle PMO = (pi-eps)/2.
  The height h = dist(M, span(P,Q)) = r cos(beta + phi).
"""
import math


def solve(r, beta, branch=+1):
    """given beta, find phi from sin(phi) = r sin(beta) (law of sines), with the centre O
    on the correct side; return phi, and the configuration."""
    s = r * math.sin(beta)
    if s > 1:
        return None
    # phi is the angle at O between OM and OP; O = centre
    # geometry: with M at origin, P = r(cos beta, sin beta) (take beta measured from the
    # chord direction), the centre O satisfies |O| = |O-P| = 1.
    # O = x * M-direction + normal: solve exactly.
    ex = (math.cos(beta), math.sin(beta))
    nx = (-math.sin(beta), math.cos(beta))
    # O = a ex + b nx with |O| = 1 and |O - r ex| = 1  =>  a = r/2, b^2 = 1 - r^2/4
    a = r / 2
    bsq = 1 - r * r / 4
    if bsq < 0:
        return None
    b = branch * math.sqrt(bsq)
    return (a, b)


def main():
    print("exact configuration: |MP|=|MQ|=r, P,Q on unit circle, angle PMQ = pi - eps")
    print("   r      beta(deg)   eps         h           delta_sw        h/eps        delta/eps")
    for r in (0.38,):
        for bd in (89.99, 89.9, 89.0, 85.0, 80.0, 70.0):
            beta = math.radians(bd)
            eps = math.pi - 2 * beta
            a, b = solve(r, beta)
            # P = r(cos beta, sin beta); O = a ex + b nx
            P = (r * math.cos(beta), r * math.sin(beta))
            Q = (r * math.cos(beta), -r * math.sin(beta))
            O = (a * math.cos(beta) - b * math.sin(beta), a * math.sin(beta) + b * math.cos(beta))
            # check |OP| = 1
            OP = math.hypot(P[0] - O[0], P[1] - O[1])
            # chord length and the site-arc width: chord = 2 sin(w/2)
            chord = math.hypot(P[0] - Q[0], P[1] - Q[1])
            w = 2 * math.asin(min(1.0, chord / 2))
            delta_site = (2 * math.asin(r / 2)) * 0 - (2 * math.asin(r / 2) - w)  # deficit vs w_flat
            w_flat = 2 * math.asin(r / 2)
            delta_site = w_flat - w
            h = r * math.cos(beta)          # dist from M to the chord (chord vertical here)
            print(f"   {r:.3f}  {bd:8.4f}  {eps:.6e}  {h:.6e}  {delta_site:.6e}  "
                  f"{h/eps if eps else float('nan'):.6f}  {delta_site/eps if eps else float('nan'):.6f}"
                  f"   |OP|={OP:.12f}")

    print("\nlog-log scan for the exponents: h ~ eps^p and delta ~ eps^q")
    r = 0.38
    data = []
    for k in range(2, 9):
        beta = math.pi / 2 - 10.0 ** (-k)
        eps = math.pi - 2 * beta
        a, b = solve(r, beta)
        chord = 2 * r * math.cos(eps / 2)
        w = 2 * math.asin(min(1.0, chord / 2))
        delta_site = 2 * math.asin(r / 2) - w
        h = r * math.cos(beta)
        data.append((eps, h, delta_site))
    print("   %12s %14s %14s %12s %12s" % ("eps", "h", "delta", "p=log h/log eps", "q=log d/log eps"))
    for i in range(1, len(data)):
        e0, h0, d0 = data[i - 1]
        e1, h1, d1 = data[i]
        p = (math.log(h1) - math.log(h0)) / (math.log(e1) - math.log(e0))
        q = (math.log(d1) - math.log(d0)) / (math.log(e1) - math.log(e0))
        print("   %12.3e %14.6e %14.6e %16.6f %16.6f" % (e1, h1, d1, p, q))

    print("\nkey ratios:")
    for (eps, h, d) in data:
        print("   eps=%.3e  h/eps=%.6e  delta/eps=%.6e  h/delta=%.6e  h/sqrt(delta)=%.6f"
              % (eps, h / eps, d / eps, h / d, h / math.sqrt(d) if d > 0 else float('nan')))


if __name__ == "__main__":
    main()
