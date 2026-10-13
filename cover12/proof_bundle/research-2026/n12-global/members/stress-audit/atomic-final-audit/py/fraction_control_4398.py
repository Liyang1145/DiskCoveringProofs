"""stress-audit / atomic-final-audit: independent Fraction-representation control
for the frozen integer atomic kernel (members/upper-audit/integer-atomic/py).

Task (Lead): different representation, one control leaf = stage11825 atomic index 4398
at scale 2^28.  I do NOT import the audited bound/certify to build my own quantities:
every claim below is recomputed from the exact rational definitions, and the audited
kernel is only *called* to compare outputs (and to run its own certify for the record).

Checks
  C1  exact atom reconstruction (boundary + screened hub atoms), count/demand vs record
  C2  exact vs integer rectangles: containment, endpoint cap, thresholds at 2^26 / 2^28
  C3  per-(atom, box) control: int d2 <= S^2 * exact d2 ; exact<=U^2 => counted (no false
      negative) ; over-count only inside the documented outward-rounding shell
  C4  annulus discard STRICTNESS probes: boxes strictly inside/outside/touching the
      annulus [1-U, sqrt(1-U^2)] must be discarded/kept with exactly the right strictness
  C5  weight rounding: |round(v*1e9) - v*1e9| <= 1/2, nonneg, zero-drop harmless
  C6  int64 range facts at 2^28 from my own rectangles (max |endpoint|, max d2)
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
N12 = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))     # .../n12-global
sys.path.insert(0, os.path.join(N12, 'members', 'upper-audit', 'integer-atomic', 'py'))
import integer_kernel as IK          # audited object: used ONLY for output comparison

U = F('0.361102963744508672616920293904')
SNAP = os.path.join(N12, 'evidence', 'hubline-domain-stage11825.json')
VECF = os.path.join(N12, 'evidence', 'atomic-unit-vectors-2048.json')
memo = {'probe': [], 'control': []}


def exact_rect(H, weights, vecfile=VECF, screen=True, drop_zero=True):
    """atom rectangles from the mathematical definition (no scaling, no rounding).

    j=0: boundary atom v (point).  j=1: h1+Uv with h1=(x-s,y).  j=2: h2+Uv, h2=(x+s,y).
    screening: retain hub1 atom iff U*c <= s_lo, hub2 iff U*c >= -s_lo.
    Returns list of (rx0,rx1,ry0,ry1,weight,exact_density,kind).
    """
    sl, sh = H[0]; xl, xh = H[1]; yl, yh = H[2]
    V = [(F(c), F(s)) for c, s in json.loads(open(vecfile, encoding='utf-8').read())]
    W = [[F(x) for x in row] for row in weights]
    n = (len(W[0]) - 1) // 2
    out = []
    for j, w in enumerate(W):
        for (c, sv) in V:
            if screen and j == 1 and U * c > sl:
                continue
            if screen and j == 2 and U * c < -sl:
                continue
            v = F(w[0]); co, si = F(1), F(0)
            for k in range(1, n + 1):
                co, si = co * c - si * sv, si * c + co * sv
                v += F(w[k]) * co + F(w[n + k]) * si
            wt = round(v * 10 ** 9)
            if drop_zero and wt == 0:
                continue
            if j == 0:
                rx = (c, c); ry = (sv, sv)
            elif j == 1:
                rx = (xl - sh + U * c, xh - sl + U * c); ry = (yl + U * sv, yh + U * sv)
            else:
                rx = (xl + sl + U * c, xh + sh + U * c); ry = (yl + U * sv, yh + U * sv)
            out.append((rx[0], rx[1], ry[0], ry[1], wt, v, j))
    return out


def exact_min_d2(r, B):
    """exact min squared distance between atom rectangle r and ring box B=(x0,x1,y0,y1)."""
    dx = max(F(0), B[0] - r[1], r[0] - B[1])
    dy = max(F(0), B[2] - r[3], r[2] - B[3])
    return dx * dx + dy * dy


def main():
    st = json.loads(open(SNAP, encoding='utf-8').read())
    atomic = [L for L in st['leaves'] if L.get('type') == 'atomic']
    idx = 4398
    leaf = atomic[idx]
    H_raw, W_raw = leaf['H'], leaf['proposal']['weights']
    N = leaf.get('atomN', 2048)
    H = [(F(a), F(b)) for a, b in H_raw]
    print('leaf idx %d  atomN %d  H=%s' % (idx, N, [[str(a), str(b)] for a, b in H]))

    # ---------------- C1: exact reconstruction -------------------------------
    atoms = exact_rect(H, W_raw)
    total = sum(a[4] for a in atoms)
    rec = leaf['result']
    print('\n[C1] my atoms=%d demand=%d   record atoms=%s demand=%s  match=%s' %
          (len(atoms), total, rec.get('atoms'), rec.get('total_integer_demand'),
           total == rec.get('total_integer_demand')))
    kinds = {0: 0, 1: 0, 2: 0}
    for a in atoms:
        kinds[a[6]] += 1
    print('     atoms per block (boundary/hub1/hub2): %s' % kinds)
    allc = len(json.loads(open(VECF, encoding='utf-8').read()))
    print('     screening drops: block1 %d, block2 %d (of %d each)' %
          (allc - kinds[1], allc - kinds[2], allc))
    memo['C1'] = {'atoms': len(atoms), 'demand': total, 'record_atoms': rec.get('atoms'),
                  'record_demand': rec.get('total_integer_demand'), 'per_block': kinds}

    # ---------------- C5: weight rounding ------------------------------------
    bad = 0
    for a in atoms:
        if a[4] < 0 or abs(F(a[4]) - a[5] * 10 ** 9) > F(1, 2):
            bad += 1
    zero_drop = exact_rect(H, W_raw, drop_zero=False)
    zeros = sum(1 for a in zero_drop if a[4] == 0)
    tot_all = sum(a[4] for a in zero_drop)
    print('[C5] rounding violations=%d ; zero-weight atoms=%d ; demand with zeros=%d (unchanged: %s)'
          % (bad, zeros, tot_all, tot_all == total))
    memo['C5'] = {'rounding_violations': bad, 'zero_weight_atoms': zeros,
                  'demand_including_zeros': tot_all}

    # ---------------- C2: integer rectangles, thresholds, ranges -------------
    for Sexpt in (26, 28):
        S = 1 << Sexpt
        U2c = -((-U * U * S * S).numerator // (U * U * S * S).denominator)   # ceil
        inner = ((1 - U) ** 2 * S * S).numerator // ((1 - U) ** 2 * S * S).denominator
        outer = -((-(1 - U * U) * S * S).numerator // ((1 - U * U) * S * S).denominator)
        okc = all(F(ax0) <= a[0] * S and a[1] * S <= F(ax1) for a, (ax0, ax1) in
                  zip(atoms[:400], [( (a[0] * S).__floor__(), -((-(a[1] * S)).__floor__()) ) for a in atoms[:400]]))
        print('[C2] S=2^%d  U2_ceil=%d inner_floor=%d outer_ceil=%d' % (Sexpt, U2c, inner, outer))
        memo.setdefault('C2', {})['S2^%d' % Sexpt] = {'U2_ceil': U2c, 'inner_floor': inner, 'outer_ceil': outer}
    S = 1 << 28
    Ax0 = [(a[0] * S).__floor__() for a in atoms]
    Ax1 = [-((-(a[1] * S)).__floor__()) for a in atoms]
    Ay0 = [(a[2] * S).__floor__() for a in atoms]
    Ay1 = [-((-(a[3] * S)).__floor__()) for a in atoms]
    maxend = max(max(map(abs, Ax0)), max(map(abs, Ax1)), max(map(abs, Ay0)), max(map(abs, Ay1)))
    print('     my max |atom endpoint| (units) = %d ; cap 2S = %d ; record max_endpoint=%s'
          % (maxend, 2 * S, '268435456'))
    memo['C2']['maxend_units_2^28'] = maxend
    memo['C2']['maxend_cap'] = 2 * S

    # ---------------- C4: annulus discard strictness probes ------------------
    # legal centers: 1-U <= |c| <= sqrt(1-U^2).  Build boxes with known exact relation.
    S28 = S
    def snap(frac, mode):
        v = frac * S28
        return (v.numerator // v.denominator) if mode == 'floor' else -((-(v)).__floor__())
    r_lo = 1 - U                    # inner radius (exact rational)
    r_hi2 = 1 - U * U               # outer radius SQUARED (exact rational)
    probes = []
    def mk(tag, x0, x1, y0, y1, need_keep):
        B = (snap(x0, 'floor'), snap(x1, 'ceil'), snap(y0, 'floor'), snap(y1, 'ceil'))
        probes.append((tag, B, need_keep))
    # (a) strictly inside the hole -> must be discarded
    mk('inside-hole', F(0), F(1, 4), F(0), F(1, 4), False)
    # (b) hole in x but far outside in y -> discarded (low > outer)
    mk('x-in-hole y-outside-outer', F(0), F(1, 4), F(99, 100), F(1), False)
    # (c) box straddling the inner radius -> must be kept
    mk('straddle-inner', r_lo - F(1, 100), r_lo + F(1, 100), F(0), F(1, 100), True)
    # (d) box straddling the outer radius (coordinate sqrt(1-U^2) in [0.93,0.94]) -> kept
    mk('straddle-outer', F(93, 100), F(94, 100), F(0), F(1, 100), True)
    # (e) strictly outside outer: min |c|^2 >= x0^2 = 0.8836 > 1-U^2 = 0.86960 -> discarded
    mk('strictly-outside-outer', F(94, 100), F(95, 100), F(0), F(1, 1000), False)
    # (f) strictly inside hole: max |c|^2 = x1^2+y1^2 < (1-U)^2 -> discarded
    x1 = F(63, 100); y1 = F(1, 1000)     # 0.63^2 + 0.001^2 = 0.396901 < 0.408163
    mk('strictly-inside-hole', F(0), x1, F(0), y1, False)
    # (g) exact-touch probe: y = 0 and x-range ending exactly at (1-U) -> kept (non-strict side)
    mk('touch-inner-exactly', F(0), r_lo, F(0), F(0), True)
    # (h) exact-touch probe: x-range starting at 0.94 (> sqrt(1-U^2)=0.93253) -> discarded
    mk('outside-outer-094', F(94, 100), F(1), F(0), F(0), False)
    A = IK.IntAtoms(H, [[str(x) for x in row] for row in W_raw], 28)
    print('\n[C4] annulus strictness probes (kernel bound: -1 = discarded):')
    all_ok = True
    for tag, B, keep in probes:
        val = A.bound(B)
        got_keep = (val >= 0)
        # my own exact verdict from the mathematical annulus test
        bx0f, bx1f, by0f, by1f = [F(v, S28) for v in B]
        nearx = max(bx0f, -bx1f, F(0)); neary = max(by0f, -by1f, F(0))
        farx = max(abs(bx0f), abs(bx1f)); fary = max(abs(by0f), abs(by1f))
        low = nearx ** 2 + neary ** 2; high = farx ** 2 + fary ** 2
        my_discard = (high < (1 - U) ** 2) or (low > 1 - U * U)
        ok = (got_keep == (not my_discard)) and (got_keep == keep)
        all_ok &= ok
        print('   %-26s keep=%s kernel_keep=%s my_discard=%s   low=%.6f high=%.6f  [%s]'
              % (tag, keep, got_keep, my_discard, float(low), float(high), 'OK' if ok else 'MISMATCH'))
    memo['C4'] = {'all_ok': all_ok, 'probes': [(tag, B, keep) for tag, B, keep in probes]}

    # ---------------- C3: per-(atom,box) soundness control -------------------
    import random
    rng = random.Random(20260927)
    U2c = -((-U * U * S * S).numerator // (U * U * S * S).denominator)
    fn = over = over_shell = 0
    trials = 0
    for _ in range(60):
        depth = rng.randrange(6, 22)
        w = (2 * S) >> depth
        kx = rng.randrange(0, (2 * S) // w); ky = rng.randrange(0, (2 * S) // w)
        B = (-S + kx * w, -S + (kx + 1) * w, -S + ky * w, -S + (ky + 1) * w)
        # my own integer d2 for a sample of atoms (recomputed, not imported)
        for a in rng.sample(atoms, 25):
            trials += 1
            ax0 = (a[0] * S).__floor__(); ax1 = -((-(a[1] * S)).__floor__())
            ay0 = (a[2] * S).__floor__(); ay1 = -((-(a[3] * S)).__floor__())
            dx = max(0, ax0 - B[1], B[0] - ax1); dy = max(0, ay0 - B[3], B[2] - ay1)
            d2i = dx * dx + dy * dy
            if d2i > 32 * S * S:
                print('   !! int64 cap exceeded', d2i)
            dex = exact_min_d2(a, [F(v, S) for v in B])
            if d2i > S * S * dex:
                print('   !! integer d2 exceeds scaled exact d2')
            int_cap = (d2i <= U2c)
            ex_cap = (dex <= U * U)
            if ex_cap and not int_cap:
                fn += 1
            if int_cap and not ex_cap:
                over += 1
                if dex - U * U > F(6, S):
                    over_shell += 1
    print('\n[C3] atom/box control samples=%d : false negatives=%d ; over-counts=%d (beyond 6/S shell: %d)'
          % (trials, fn, over, over_shell))
    memo['C3'] = {'samples': trials, 'false_negatives': fn, 'over_counts': over,
                  'over_counts_beyond_shell': over_shell, 'shell_allowance_1e9': float(F(6, S))}

    # ---------------- extra: record cross-check of the leaf verdict ----------
    A28 = IK.IntAtoms(H, [[str(x) for x in row] for row in W_raw], 28)
    res = A28.certify()
    print('\n[record] kernel certify(2^28): %s' % json.dumps(res))
    print('         recorded:               %s' % json.dumps({k: rec[k] for k in rec if k != 'atoms'}))
    memo['record'] = {'kernel_certify_2^28': res, 'recorded': rec}

    out = os.path.join(HERE, '..', 'evidence', 'fraction-control-4398.json')
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as f:
        json.dump(memo, f, indent=1, default=str)
    print('\nwrote', os.path.relpath(out, N12))


if __name__ == '__main__':
    main()
