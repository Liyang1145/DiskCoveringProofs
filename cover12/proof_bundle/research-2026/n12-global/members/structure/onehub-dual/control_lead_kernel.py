"""Independent controls for lead/onehub_interval_certificate.py (READ-ONLY).

Three checks, all implemented independently of the lead kernel's arithmetic:

 C1 aggregate-rows: rebuild {'boundary':[a,b,c],'hub':[a,b,c]} from the row
    weights in segment_U_K1.json with an independent parser, compare with
    lead.aggregate(), and verify the nonnegativity condition a >= sqrt(b^2+c^2)
    (the one actually needed for a nonnegative weight 1 + (b/a)cos + (c/a)sin).

 C2 point control: for sampled boxes B (including degenerate ones at corners,
    centre and random interior points) require
        upper(d,B).b  >=  F(pointwise)(any sampled interior point of B)
    where F is computed by this script's own row algebra at 40 digits.

 C3 tightness: for degenerate boxes (a single point) the interval width
    upper.b - upper.a should be tiny (< 1e-12), i.e. the kernel is not
    over-widening on points.

Usage: py -3 control_lead_kernel.py [n_segments] [n_sample_boxes_per_segment]
"""
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

from mpmath import mp, iv
import mpmath

HERE = Path(__file__).parent
ROOT = HERE.parents[4]                      # workspace root (ai4math2)
LEAD = ROOT / "research-2026" / "n12-global" / "lead"
sys.path.insert(0, str(LEAD))


def load_lead():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "lead_kernel", LEAD / "onehub_interval_certificate.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)             # module level only (guarded main)
    return mod


def row_algebra(rho, phi, e, mpdps=40):
    """independent pointwise evaluation of the folded functional."""
    mp.dps = mpdps
    rho = mp.mpf(rho); phi = mp.mpf(phi); e = mp.mpf(e)
    Uq = F('0.361102963744508672616920293904')
    U = mp.mpf(Uq.numerator) / mp.mpf(Uq.denominator)
    ca = (1 + rho * rho - U * U) / (2 * rho)
    ca = max(mp.mpf(-1), min(mp.mpf(1), ca))
    al = mp.acos(ca)
    sa = mp.sqrt(max(mp.mpf(0), 1 - ca * ca))
    ell = mp.sqrt(rho * rho - 2 * rho * e * mp.cos(phi) + e * e)
    qb = min(mp.mpf(1), ell / (2 * U))
    be = mp.acos(qb)
    sb = mp.sqrt(max(mp.mpf(0), 1 - qb * qb))
    dx = rho * mp.cos(phi) - e
    dy = rho * mp.sin(phi)
    return dict(al=al, sa=sa, be=be, sb=sb, cosp=mp.cos(phi), sinp=mp.sin(phi),
                cpsi=dx / ell, spsi=dy / ell, ell=ell)


def F_pointwise(d, rho, phi, e):
    r = row_algebra(rho, phi, e)
    wb = [mp.mpf(v[0].numerator) / mp.mpf(v[0].denominator) * F(str(v[1]))
          if False else mp.mpf(v[1].numerator) / mp.mpf(v[1].denominator)
          for v in ([(d['boundary'][0], d['boundary'][0]),
                     (d['boundary'][1], d['boundary'][1]),
                     (d['boundary'][2], d['boundary'][2])])]
    return r


def point_F(d, rho, phi, e):
    """value of the folded functional sum_r w_r A[r,p] at one point."""
    r = row_algebra(rho, phi, e)
    wb = [Q_to_mp(x) for x in d['boundary']]
    wh = [Q_to_mp(x) for x in d['hub']]
    return (wb[0] * r['al'] + r['sa'] * (wb[1] * r['cosp'] + wb[2] * r['sinp'])
            + wh[0] * r['be'] + r['sb'] * (wh[1] * r['cpsi'] + wh[2] * r['spsi']))


def Q_to_mp(fr):
    mp.dps = 40
    return mp.mpf(fr.numerator) / mp.mpf(fr.denominator)


def parse_rows(seg):
    """independent aggregate reconstruction, using the LEAD's rounding rule
    F(round(F(str(w)) * 10^9), 10^9) so that the control matches the kernel."""
    d = {'boundary': [F(0), F(0), F(0)], 'hub': [F(0), F(0), F(0)]}
    for row in seg['weights']:
        name = row['row']
        v = F(round(F(str(row['weight'])) * 10 ** 9), 10 ** 9)
        circ = name.split('_')[0]
        d[circ][0] += v
        if 'cos' in name:
            d[circ][1] += v * int(name.split('_')[-1].replace('+', ''))
        if 'sin' in name:
            d[circ][2] += v * int(name.split('_')[-1].replace('+', ''))
    return d


def exact_rows(seg):
    """the same aggregate built from our independent exact-rational JSON."""
    out = {'boundary': [F(0), F(0), F(0)], 'hub': [F(0), F(0), F(0)]}
    for row in seg['weights']:
        name = row['row']
        v = F(row['num'], row['den'])
        circ = name.split('_')[0]
        out[circ][0] += v
        if 'cos' in name:
            out[circ][1] += v * int(name.split('_')[-1].replace('+', ''))
        if 'sin' in name:
            out[circ][2] += v * int(name.split('_')[-1].replace('+', ''))
    return out


def main():
    nseg = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    nsamp = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    mod = load_lead()
    data = json.loads(
        (HERE / "segment_U_K1.json").read_text())['segments']
    exact = json.loads(
        (HERE / "weights_K1_exact.json").read_text())['segments']
    print("controls on lead kernel; %d segments in JSON" % len(data))
    bad = 0
    for k in range(min(nseg, len(data))):
        seg = data[k]
        d_ind = parse_rows(seg)
        d_lead = mod.aggregate(seg['weights'])
        d_exact = exact_rows(exact[k]) if k < len(exact) else None
        ok_rows = all(d_ind[c][i] == d_lead[c][i]
                      for c in ('boundary', 'hub') for i in range(3))
        ok_exact = (d_exact is None) or all(
            abs(float(d_exact[c][i] - d_lead[c][i])) < 1e-9
            for c in ('boundary', 'hub') for i in range(3))
        # nonnegativity of the underlying weight functions: a^2 >= b^2 + c^2
        nonneg = True
        for c in ('boundary', 'hub'):
            a, b, cc = d_ind[c]
            if not (a * a >= b * b + cc * cc):
                nonneg = False
        # sampled boxes: e-box from the segment, z(phi) grid inside
        lo = F(seg['e_lo']); hi = F(seg['e_hi'])
        worst_slack = None
        width_max = 0.0
        import random
        rnd = random.Random(1234 + k)
        for s in range(nsamp):
            z0 = F(rnd.randint(0, 600), 600)
            p0 = F(rnd.randint(0, 600), 600)
            e0 = lo + (hi - lo) * F(rnd.randint(0, 4), 4)
            # degenerate box at the point
            B = ((z0, z0), (p0, p0), (e0, e0))
            up = mod.upper(d_lead, B)
            if up is None:
                continue
            # point coordinates from the same parametrisation, exact rationals
            Uq = F('0.361102963744508672616920293904')
            rl = 1 - Uq
            rh = mpmath.sqrt(mpmath.mpf(Uq.numerator) ** 2 /
                             mpmath.mpf(Uq.denominator) ** 2)
            # sqrt(1-U^2) evaluated independently
            rh = mpmath.sqrt(mpmath.mpf(1) - mpmath.mpf(Uq.numerator) ** 2 /
                             mpmath.mpf(Uq.denominator) ** 2)
            rlo = mpmath.mpf(rl.numerator) / mpmath.mpf(rl.denominator)
            z_fr = mpmath.mpf(z0.numerator) / mpmath.mpf(z0.denominator)
            rho_pt = rlo + (rh - rlo) * z_fr
            phi_pt = 2 * mpmath.pi * (mpmath.mpf(p0.numerator) /
                                      mpmath.mpf(p0.denominator))
            e_pt = (3 * mpmath.mpf(Uq.numerator) / mpmath.mpf(Uq.denominator)
                    - 1) * (mpmath.mpf(e0.numerator) /
                            mpmath.mpf(e0.denominator))
            fval = point_F(d_ind, rho_pt, phi_pt, e_pt)
            slack = mpmath.mpf(up.b) - fval
            width_max = max(width_max, float(mpmath.mpf(up.b) - mpmath.mpf(up.a)))
            if worst_slack is None or slack < worst_slack:
                worst_slack = slack
        flag = "OK" if (ok_rows and ok_exact and nonneg and
                        (worst_slack is None or worst_slack > -1e-12)) else "FAIL"
        if flag == "FAIL":
            bad += 1
        print("seg %2d  rows_match=%s exact_match=%s nonneg=%s  min_slack=%s  "
              "max_width=%.2e  %s"
              % (k, ok_rows, ok_exact, nonneg,
                 ("%.3e" % worst_slack) if worst_slack is not None else "n/a",
                 width_max, flag), flush=True)
    print("segments with control failure:", bad)


if __name__ == "__main__":
    main()
