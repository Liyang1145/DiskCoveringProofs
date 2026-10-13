"""Does the (invalid) clip at line 91 break the RETURNED interval?

Line 91 in the kernel clamps each partial to [-L, L] with L = R/sqrt(1-R^2) = 0.4108.
That bound is FALSE on the admissible set: max |dw/da| = 1.177 (a~0.1225, u=v=1, q~qmin).
This script builds the ring kernel with GENUINELY clipped intervals (as the kernel does),
then compares the returned interval's upper endpoint against a dense pointwise scan of the
same ring formula inside the box -- the property the branch-and-bound actually consumes.
"""
import io, math, os, sys
from contextlib import redirect_stdout
from pathlib import Path
from mpmath import iv

LEAD = Path(__file__).resolve().parents[1] / 'lead'
HERE = Path(__file__).resolve().parent
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']
SRC = (LEAD / 'certify_q0_closure.py').read_text().splitlines(keepends=True)
ns = {'__name__': 'iso', '__file__': str(LEAD / 'certify_q0_closure.py')}
with redirect_stdout(io.StringIO()):
    exec(compile(''.join(SRC[:108]), 'iso', 'exec'), ns)

interval, pos = ns['interval'], ns['pos']
pi = math.pi
qmin = 4 * math.sin(pi - 8 * math.asin(0.38)) ** 2 / 0.38 ** 2
z = [float(v.a) for v in ns['z']]


def asin(x):
    return iv.atan2(x, iv.sqrt(1 - x * x))


def ring_kernel(i, box, clip=True):
    """verbatim port of certify_q0_closure.py lines 79-107"""
    mu, d, e = [iv.mpf(x) for x in (z[i], z[32 + 2 * i], z[32 + 2 * i + 1])]
    C = iv.mpf(z[71] + (z[72] if i >= 3 else 0))
    dl, el = [iv.mpf(x) for x in (z[73 + 21 + 2 * i], z[73 + 21 + 2 * i + 1])]
    hl, hr = [iv.mpf(x) for x in (z[112 + i], z[112 + (i + 1) % 9])]
    a, u, v = box
    R = iv.mpf(19) / 50
    R2 = R * R
    q = (u - v) ** 2 + 4 * u * v * iv.sin(a / 2) ** 2
    q = interval(max(iv.mpf(0).a, q.a), min(iv.mpf(4).b, q.b))
    if float(q.b) < qmin:
        return None
    w = 2 * asin(R * iv.sqrt(q) / 2)
    wl, wh = iv.mpf(w.a), iv.mpf(w.b)
    h = interval(((C + iv.mpf('.5')) * wl - iv.sin(wl) / 2).a,
                 ((C + iv.mpf('.5')) * wh - iv.sin(wh) / 2).b)
    direct = R2 * u * v * iv.sin(a) / 2 + h - mu * a - d * u * u - e * v * v - dl * u - el * v
    L = R / iv.sqrt(1 - R2)
    den = iv.sqrt(1 - R2 * q / 4)
    if float(q.a) > 0:
        root = iv.sqrt(q)
        wa = R * u * v * iv.sin(a) / (root * den)
        wu = R * (u - v * iv.cos(a)) / (root * den)
        wv = R * (v - u * iv.cos(a)) / (root * den)
        if clip:
            wa = interval(max(-float(L.b), float(wa.a)), min(float(L.b), float(wa.b)))
            wu = interval(max(-float(L.b), float(wu.a)), min(float(L.b), float(wu.b)))
            wv = interval(max(-float(L.b), float(wv.a)), min(float(L.b), float(wv.b)))
    else:
        wa = interval(-float(L.b), float(L.b))
        wu = interval(-float(L.b), float(L.b))
        wv = interval(-float(L.b), float(L.b))
    H = C + (1 - iv.cos(w)) / 2
    grad = [R2 * u * v * iv.cos(a) / 2 + H * wa - mu,
            R2 * v * iv.sin(a) / 2 + H * wu - 2 * d * u - dl,
            R2 * u * iv.sin(a) / 2 + H * wv - 2 * e * v - el]
    mids = [iv.mpf((float(t.a) + float(t.b)) / 2) for t in box]
    am, um, vm = mids
    qm = (um - vm) ** 2 + 4 * um * vm * iv.sin(am / 2) ** 2
    wm = 2 * asin(R * iv.sqrt(qm) / 2)
    center = (R2 * um * vm * iv.sin(am) / 2 + (wm - iv.sin(wm)) / 2 + C * wm
              - mu * am - d * um * um - e * vm * vm - dl * um - el * vm)
    mean = center + sum(grad[k] * (box[k] - mids[k]) for k in range(3))
    bet = interval(0, float(iv.pi.b)) if float(q.a) <= 0 else iv.atan2(
        pos(v * iv.sin(a)), u - v * iv.cos(a))
    extra = (hl - hr) * bet - hr * a + hr * iv.pi + (hl + hr) * w / 2
    old = interval(max(float(direct.a), float(mean.a)), min(float(direct.b), float(mean.b)))
    direct2 = old + extra
    if float(q.a) <= 0 or float(a.a) < 0 or float(a.b) >= float(iv.pi.a):
        return {'final': direct2, 'direct_side': direct + extra, 'mean_side': mean + extra}
    ba = (u * v * iv.cos(a) - v * v) / q
    bu = -v * iv.sin(a) / q
    bv = u * iv.sin(a) / q
    gg = [grad[k] + (hl - hr) * (ba, bu, bv)[k] + (hl + hr) * (wa, wu, wv)[k] / 2
          - (hr if k == 0 else 0) for k in range(3)]
    betm = iv.atan2(vm * iv.sin(am), um - vm * iv.cos(am))
    center2 = center + (hl - hr) * betm - hr * am + hr * iv.pi + (hl + hr) * wm / 2
    mean2 = center2 + sum(gg[k] * (box[k] - mids[k]) for k in range(3))
    final = interval(max(float(direct2.a), float(mean2.a)), min(float(direct2.b), float(mean2.b)))
    return {'final': final, 'direct_side': direct2, 'mean_side': mean2}


def true_sup(i, box, N=24):
    a, u, v = box
    best = -1e9
    for ia in range(N + 1):
        aa = float(a.a) + (float(a.b) - float(a.a)) * ia / N
        for iu in range(N + 1):
            uu = float(u.a) + (float(u.b) - float(u.a)) * iu / N
            for ivv in range(N + 1):
                vv = float(v.a) + (float(v.b) - float(v.a)) * ivv / N
                q = uu * uu + vv * vv - 2 * uu * vv * math.cos(aa)
                if q <= 0:
                    continue
                w = 2 * math.asin(min(1.0, 0.38 * math.sqrt(q) / 2))
                C = z[71] + (z[72] if i >= 3 else 0)
                beta = math.atan2(vv * math.sin(aa), uu - vv * math.cos(aa))
                val = (0.38 ** 2 * uu * vv * math.sin(aa) / 2 + (w - math.sin(w)) / 2 + C * w
                       - z[i] * aa - z[32 + 2 * i] * uu * uu - z[32 + 2 * i + 1] * vv * vv
                       - z[73 + 21 + 2 * i] * uu - z[73 + 21 + 2 * i + 1] * vv
                       + (z[112 + i] - z[112 + (i + 1) % 9]) * beta
                       - z[112 + (i + 1) % 9] * aa + z[112 + (i + 1) % 9] * math.pi
                       + (z[112 + i] + z[112 + (i + 1) % 9]) * w / 2)
                best = max(best, val)
    return best


print('clipped-kernel final upper vs true pointwise sup inside the box:')
rows = []
for (i, ac, uc, vc, h) in [(1, 0.1225, 1.0, 1.0, 1e-3), (1, 0.1225, 1.0, 1.0, 1e-4),
                           (1, 0.1225, 0.98, 0.98, 1e-2), (1, 0.30, 1.0, 1.0, 1e-2),
                           (1, 0.60, 1.0, 1.0, 1e-2), (1, 0.90, 0.95, 0.95, 1e-2),
                           (1, 0.1225, 0.90, 0.90, 5e-2), (0, 0.1225, 1.0, 1.0, 1e-2),
                           (5, 0.1225, 1.0, 1.0, 1e-2)]:
    box = [iv.mpf([ac - h, ac + h]), iv.mpf([uc - h, uc + h]), iv.mpf([vc - h, vc + h])]
    out = ring_kernel(i, box, clip=True)
    if out is None:
        print(f'  i={i} a={ac} h={h}: qmin-rejected')
        continue
    tsup = true_sup(i, box)
    fin = float(out['final'].b)
    ok = fin >= tsup - 1e-12
    rows.append((i, ac, uc, vc, h, fin, tsup, ok))
    print(f'  i={i} a={ac:7.4f} u={uc:.2f} v={vc:.2f} h={h:g}: final_upper={fin:+.9f} '
          f'true_sup={tsup:+.9f}  {"OK" if ok else "*** VIOLATED ***"}')
nbad = sum(1 for r in rows if not r[7])
print(f'\nviolations: {nbad} of {len(rows)}')
