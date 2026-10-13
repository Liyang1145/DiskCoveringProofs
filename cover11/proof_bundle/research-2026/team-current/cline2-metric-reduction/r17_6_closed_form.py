"""R17-6: exact flat-limit family in closed form, and the true exponents.

Setup (all constraints exact). Site M at the origin. Switches
    P_pm = (u, +-v),   u^2 + v^2 = r^2      (switch radii = r)
on the unit circle centred at C = (a, b):
    (u-a)^2 + (v-b)^2 = 1  and  (u-a)^2 + (v+b)^2 = 1
The second pair gives b = 0 and (u - a)^2 + v^2 = 1, i.e. a = u - sqrt(1 - v^2)  (centre on the
same side as M). The sector angle and height:
    alpha2 = angle at M between P+ and P- ,   h = dist(M, line P+P-) = u .
Width (the site's arc): 2 sin(w/2) = |P+P-| = 2v, so w = 2 asin v, and the flat limit is
alpha2 -> pi  <=>  h = u -> 0  <=>  v -> r, i.e. w -> 2 asin r.

EXACT SCALING (expansions below are elementary; the run only confirms them):
    v = r cos(eps/2) ,  u = r sin(eps/2) ,  eps := pi - alpha2      [law of cosines in M P+ P-]
    h = u = r sin(eps/2) = r eps/2 + O(eps^3)
    w = 2 asin v = 2 asin(r cos(eps/2)) = 2 asin r - (r eps^2)/(4 sqrt(1-r^2)) + O(eps^4)
    delta := w_flat - w = (r eps^2)/(4 sqrt(1-r^2)) + O(eps^4)
So h ~ eps  while  delta ~ eps^2/8  (up to the r-factor), hence
    h/delta ~ eps^{-1} -> infinity
and the correct statement is h ~ sqrt(delta), NOT h ~ delta.
NOTE the flat width here is w_flat = 2 asin r for the SITE arc; if instead the deficit is taken
for the CHORD 2 sin(w/2) = |P+P-| = 2v, then 2v = 2r - r eps^2/4, i.e. delta_chord ~ eps^2
again. Either way delta is quadratic in eps, so eps ~ sqrt(delta) and h ~ eps ~ sqrt(delta).
"""
import math


def config(r, eps):
    v = r * math.cos(eps / 2)
    u = r * math.sin(eps / 2)
    if v > 1:
        return None
    a = u - math.sqrt(max(0.0, 1 - v * v))
    w = 2 * math.asin(min(1.0, v))
    w_flat = 2 * math.asin(r)
    return u, v, a, w, w_flat - w, 2 * v


def main():
    print("exact check: the centre C=(a,0) must have |C - P+| = 1 and |C| = |C - M| arbitrary")
    for r in (0.38,):
        for eps in (0.3, 0.03, 3e-3):
            u, v, a, w, delta, chord = config(r, eps)
            C = (a, 0.0)
            dP = math.hypot(u - a, v - 0.0)
            print(f"  r={r} eps={eps:.3e}: u=h={u:.6e} v={v:.9f} |C-P|={dP:.12f}"
                  f"  w={w:.12f}  w_flat={2*math.asin(r):.12f}  delta={delta:.6e}")

    print("\nexponent scan: r = 0.38")
    print("   %12s %14s %14s %12s %12s %12s %12s"
          % ("eps", "h", "delta", "h/eps", "delta/eps^2", "h/sqrt(delta)", "log(h)/log(eps)"))
    r = 0.38
    rows = []
    for k in range(0, 13):
        eps = 0.3 * 10.0 ** (-k)
        u, v, a, w, delta, chord = config(r, eps)
        rows.append((eps, u, delta))
    for i, (eps, h, delta) in enumerate(rows):
        p = "-"
        if i > 0:
            e0, h0, d0 = rows[i - 1]
            p = "%.4f" % ((math.log(h) - math.log(h0)) / (math.log(eps) - math.log(e0)))
        print("   %12.3e %14.6e %14.6e %12.6f %12.6f %12.6f %12s"
              % (eps, h, delta, h / eps, delta / eps ** 2,
                 h / math.sqrt(delta) if delta > 0 else float('nan'), p))

    print("\nclosed-form comparison at eps = 1e-4 (r = 0.38):")
    eps = 1e-4
    u, v, a, w, delta, chord = config(r, eps)
    pred_h = r * eps / 2
    pred_delta = r * eps ** 2 / (4 * math.sqrt(1 - r * r))
    print("   h        exact %.12e   r eps/2 = %.12e" % (u, pred_h))
    print("   delta    exact %.12e   r eps^2/(4 s) = %.12e" % (delta, pred_delta))
    print("   h/delta  exact %.6e     (-> infinity: h ~ sqrt(delta) ~ eps)" % (u / delta))


if __name__ == "__main__":
    main()
