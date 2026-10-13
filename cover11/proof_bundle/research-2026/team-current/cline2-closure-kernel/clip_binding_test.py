"""Does the (provably invalid) clip at line 91 affect the code's RETURNED interval?

Method: reimplement the ring kernel verbatim (lines 79-107 style) with instrumentation that
reports the 3 candidate enclosures (direct, mean+extra=direct2, mean2) and the final answer,
then compare against a dense pointwise scan of the same formula inside the box.

Note the clip *can* be invalid: max|dw/da| over the admissible set is ~1.177 > L=0.411
(at a~0.1225, u=v=1, q~qmin). The question is whether `direct` (which does not use the clip)
keeps the returned interval sound.
"""
import io, math, os, sys
from contextlib import redirect_stdout
from pathlib import Path
from mpmath import iv

LEAD = Path(__file__).resolve().parents[1] / 'lead'
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']
SRC = (LEAD / 'certify_q0_closure.py').read_text().splitlines(keepends=True)
ns = {'__name__': 'iso', '__file__': str(LEAD / 'certify_q0_closure.py')}
with redirect_stdout(io.StringIO()):
    exec(compile(''.join(SRC[:108]), 'iso', 'exec'), ns)

iv.pi = iv.pi
interval, pos, asin_ = ns['interval'], ns['pos'], ns['asin']
R, R2, pi = ns['R'] if False else 0.38, 0.38 ** 2, math.pi
qmin = 4 * math.sin(pi - 8 * math.asin(0.38)) ** 2 / 0.38 ** 2
z = [float(v.a) for v in ns['z']]
Riv = iv.mpf(19) / 50
R2iv = Riv * Riv


def ring_verbose(i, box):
    mu, d, e = z[i], z[32 + 2 * i], z[32 + 2 * i + 1]
    C = z[71] + (z[72] if i >= 3 else 0)
    dl, el = z[73 + 21 + 2 * i], z[73 + 21 + 2 * i + 1]
    hl, hr = z[112 + i], z[112 + (i + 1) % 9]
    mu, d, e, C, dl, el, hl, hr = (iv.mpf(x) for x in (mu, d, e, C, dl, el, hl, hr))
    a, u, v = box
    q = (u - v) ** 2 + 4 * u * v * iv.sin(a / 2) ** 2
    q = interval(max(iv.mpf(0).a, q.a), min(iv.mpf(4).b, q.b))
    if float(q.b) < qmin:
        return None
    w = 2 * asin_(Riv * iv.sqrt(q) / 2)
    wl, wh = iv.mpf(w.a), iv.mpf(w.b)
    h = interval(((C + iv.mpf('.5')) * wl - iv.sin(wl) / 2).a,
                 ((C + iv.mpf('.5')) * wh - iv.sin(wh) / 2).b)
    direct = R2iv * u * v * iv.sin(a) / 2 + h - mu * a - d * u * u - e * v * v - dl * u - el * v
    L = Riv / iv.sqrt(1 - R2iv)
    den = iv.sqrt(1 - R2iv * q / 4)
    if float(q.a) > 0:
        root = iv.sqrt(q)
        wa = Riv * u * v * iv.sin(a) / (root * den)
        wu = Riv * (u - v * iv.cos(a)) / (root * den)
        wv = Riv * (v - u * iv.cos(a)) / (root * den)
        wa = interval(max(-float(L.b), float(wa.a)), min(float(L.b), float(wa.b)))
        wu = interval(max(-float(L.b), float(wu.a)), min(float(L.b), float(wu.b)))
        wv = interval(max(-float(L.b), float(wv.a)), min(float(L.b), float(wv.b)))
    else:
        wa = interval(-float(L.b), float(L.b))
        wu = interval(-float(L.b), float(L.b))
        wv = interval(-float(L.b), float(L.b))
    H = C + (1 - iv.cos(w)) / 2
    grad = [R2iv * u * v * iv.cos(a) / 2 + H * wa - mu,
            R2iv * v * iv.sin(a) / 2 + H * wu - 2 * d * u - dl,
            R2iv * u * iv.sin(a) / 2 + H * wv - 2 * e * v - el]
    mids = [iv.mpf((float(t.a) + float(t.b)) / 2) for t in box]
    am, um, vm = mids
    qm = (um - vm) ** 2 + 4 * um * vm * iv.sin(am / 2) ** 2
    wm = 2 * asin_(Riv * iv.sqrt(qm) / 2)
    center = (R2iv * um * vm * iv.sin(am) / 2 + (wm - iv.sin(wm)) / 2 + C * wm
              - mu * am - d * um * um - e * vm * vm - dl * um - el * vm)
    mean = center + sum(grad[k] * (box[k] - mids[k]) for k in range(3))
    bet = interval(0, float(iv.pi.b)) if float(q.a) <= 0 else iv.atan2(
        pos(v * iv.sin(a)), u - v * iv.cos(a))
    extra = (hl - hr) * bet - hr * a + hr * iv.pi + (hl + hr) * w / 2
    if float(q.a) <= 0 or float(a.a) < 0 or float(a.b) >= float(iv.pi.a):
        d2 = interval(max(float(direct.a), float(mean.a)), min(float(direct.b), float(mean.b)))
        return {'direct': direct, 'mean': mean, 'final': d2 + extra, 'uses_clip': False}
    ba = (u * v * iv.cos(a) - v * v) / q
    bu = -v * iv.sin(a) / q
    bv = u * iv.sin(a) / q
    db = [ba, bu, bv]
    dw = [wa, wu, wv]
    gg = [grad[k] + (hl - hr) * db[k] + (hl + hr) * dw[k] / 2 - (hr if k == 0 else 0)
          for k in range(3)]
    betm = iv.atan2(vm * iv.sin(am), um - vm * iv.cos(am))
    center2 = center + (hl - hr) * betm - hr * am + hr * iv.pi + (hl + hr) * wm / 2
    mean2 = center2 + sum(gg[k] * (box[k] - mids[k]) for k in range(3))
    old = interval(max(float(direct.a), float(mean.a)), min(float(direct.b), float(mean.b)))
    direct2 = old + extra
    final = interval(max(float(direct2.a), float(mean2.a)), min(float(direct2.b), float(mean2.b)))
    return {'direct': direct + extra, 'mean': mean + extra, 'mean2': mean2,
            'direct2': direct2, 'final': final, 'uses_clip': True}


def true_sup(i, box, N=20):
    """pointwise sup of the SAME formula over the box (exact per point, no clip)"""
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
                mu, d, e = z[i], z[32 + 2 * i], z[32 + 2 * i + 1]
                C = z[71] + (z[72] if i >= 3 else 0)
                dl, el = z[73 + 21 + 2 * i], z[73 + 21 + 2 * i + 1]
                hl, hr = z[112 + i], z[112 + (i + 1) % 9]
                beta = math.atan2(vv * math.sin(aa), uu - vv * math.cos(aa))
                val = (0.38 ** 2 * uu * vv * math.sin(aa) / 2 + (w - math.sin(w)) / 2 + C * w
                       - mu * aa - d * uu * uu - e * vv * vv - dl * uu - el * vv
                       + (hl - hr) * beta - hr * aa + hr * math.pi + (hl + hr) * w / 2)
                best = max(best, val)
    return best


print('box (i, a, u, v, halfwidth): final interval vs direct-only vs true sup')
cases = [(1, 0.1225, 1.0, 1.0, 1e-3), (1, 0.1225, 1.0, 1.0, 1e-4),
         (1, 0.30, 1.0, 1.0, 1e-3), (1, 0.60, 1.0, 1.0, 1e-3),
         (1, 0.90, 0.95, 0.95, 1e-3), (1, 2.00, 1.0, 0.6, 1e-2),
         (1, 0.1225, 0.98, 0.98, 1e-2)]
for (i, ac, uc, vc, h) in cases:
    box = [iv.mpf([ac - h, ac + h]), iv.mpf([uc - h, uc + h]), iv.mpf([vc - h, vc + h])]
    out = ring_verbose(i, box)
    if out is None:
        print(f'  i={i} box a={ac} u={uc} v={vc} h={h}: rejected by qmin filter')
        continue
    tsup = true_sup(i, box)
    fin = float(out['final'].b)
    dv = float(out['direct'].b)
    print(f'  i={i} a={ac} u={uc} v={vc} h={h}: final_upper={fin:+.9f} direct_upper={dv:+.9f} '
          f'true_sup={tsup:+.9f}  sound? {fin >= tsup - 1e-9}  '
          f'(mean2={float(out["mean2"].b):+.9f})' if 'mean2' in out else '')
    if 'mean2' in out:
        print(f'      mean2 binds? {float(out["mean2"].b) < dv}')

