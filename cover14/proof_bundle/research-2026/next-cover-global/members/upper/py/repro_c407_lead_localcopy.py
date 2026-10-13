# -*- coding: utf-8 -*-
"""verify_c407_lead.py -- lead 侧对 C407 的独立复核（不读外部评审代码、不读团队求值器）

口径行：
  图 = 单位闭盘 D 的覆盖（14 个等半径 R 闭盘，盘心任意，无归一化）；
  单位 = 无量纲；聚合 = 候选极值集完备枚举取 max；阈值 = 有理数 T / Tp / L（本文件明写）。
  算术 = 全程 fractions.Fraction（精确有理）；唯一非有理运算是 sqrt，用整数 isqrt 做
         **有向区间包**（10^-40 位），故所有比较的方向都是严格确定的。

完备性（本件自述，用于把"候选集上的 max"升级为"整盘上的 max"）：
  f(p) = min_i |p-c_i| 在紧集 D 上的最大值点 p* 必属下列之一：
    (a) p* ∈ int D：至少 3 个盘在 p* 处活跃且等距 ⇒ 三盘外心；
    (b) p* ∈ ∂D：至少 2 个盘活跃且等距 ⇒ 中垂线 ∩ ∂D；
    (c) p* ∈ ∂D：只有 1 个盘活跃 ⇒ 该盘心在 ∂D 上的最远点（对径点）；
    (d) p* = 原点（局部单盘覆盖退化情形）。
  故 {原点} ∪ {对径点} ∪ {中垂线∩∂D} ∪ {三盘外心∩D} 完备。

独立手段：外部评审用"二次根号精确符号 sign(a+b√q)"；本件用"有理数 + isqrt 有向区间包"，
并把阈值抬高到 Tp（仍 < L）留余量；另用 numpy 稠密网格 + 局部爬升做交叉检查。
"""
import hashlib, json, math, sys
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

try:                                   # 控制台可能是 GBK
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
except Exception:
    pass

# --- MODIFIED COPY (member upper, next-cover-global) -----------------------------
# Only this block differs from the read-only original (research-2026/lead/
# verify_c407_lead.py): the asset is re-pointed by absolute path and OUT is
# redirected into this member's logs/ (the original OUT dir is read-only to us).
# All arithmetic / enumeration / controls below are byte-identical.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
ORIG = ROOT / 'research-2026/lead/verify_c407_lead.py'
SRC = ROOT / 'research-2026/session2/type14/out/hprec_sol.json'
OUT = HERE.parent / 'logs' / 'c407_lead_result_localcopy.txt'

DIG = 40
SC = 10 ** DIG


def sqrt_iv(q):
    """Fraction q >= 0 -> (lo, hi) 有理区间，lo <= sqrt(q) <= hi"""
    assert q >= 0
    m = (q.numerator * SC ** 4) // q.denominator
    r = math.isqrt(m)
    return F(r, SC * SC), F(r + 1, SC * SC)


def iv_sqr(a):
    """区间平方 [a0,a1]^2（跨零时下界取 0，不做朴素四积）"""
    if a[0] <= 0 <= a[1]:
        return (F(0), max(a[0] * a[0], a[1] * a[1]))
    return (min(a[0] * a[0], a[1] * a[1]), max(a[0] * a[0], a[1] * a[1]))


def dist2_iv(box, c):
    """box = ((xlo,xhi),(ylo,yhi))；返回 [min, max] of |p-c|^2 over box（精确有理）"""
    dx = (box[0][0] - c[0], box[0][1] - c[0])
    dy = (box[1][0] - c[1], box[1][1] - c[1])
    sx, sy = iv_sqr(dx), iv_sqr(dy)
    return (sx[0] + sy[0], sx[1] + sy[1])


def mindist_iv(box, C):
    """[a,b] ⊇ {min_i |p-c_i| : p ∈ box}"""
    lo = min(dist2_iv(box, c)[0] for c in C)
    hi = min(dist2_iv(box, c)[1] for c in C)
    return sqrt_iv(lo)[0], sqrt_iv(hi)[1]


def pt(x, y):
    return ((x, x), (y, y))


def candidates(C):
    P = [('origin', pt(F(0), F(0)))]
    for i, c in enumerate(C):
        n2 = c[0] * c[0] + c[1] * c[1]
        if n2 == 0:
            P.append((f'stationary{i}(zero-center)', pt(F(1), F(0))))
            continue
        nlo, nhi = sqrt_iv(n2)
        for s in (-1, 1):
            xa, xb = (-s * c[0]) / nlo, (-s * c[0]) / nhi
            ya, yb = (-s * c[1]) / nlo, (-s * c[1]) / nhi
            P.append((f'stationary{i}/{s}',
                      ((min(xa, xb), max(xa, xb)), (min(ya, yb), max(ya, yb)))))
    for i, j in combinations(range(len(C)), 2):
        dx, dy = C[j][0] - C[i][0], C[j][1] - C[i][1]
        d2 = dx * dx + dy * dy
        if d2 == 0:
            continue
        h = (C[j][0] ** 2 + C[j][1] ** 2 - C[i][0] ** 2 - C[i][1] ** 2) / 2
        ux, uy = h * dx / d2, h * dy / d2
        q = 1 - (ux * ux + uy * uy)          # 交点在 ∂D 上：p = u ± sqrt(q) * w, |w| = 1
        if q < 0:
            continue
        sq_lo, sq_hi = sqrt_iv(q)
        nlo, nhi = sqrt_iv(d2)
        for s in (-1, 1):
            wx = (s * (-dy))
            wy = (s * dx)
            wxlo, wxhi = wx / nhi, wx / nlo
            wylo, wyhi = wy / nhi, wy / nlo
            xs = (ux + sq_lo * wxlo, ux + sq_lo * wxhi, ux + sq_hi * wxlo, ux + sq_hi * wxhi)
            ys = (uy + sq_lo * wylo, uy + sq_lo * wyhi, uy + sq_hi * wylo, uy + sq_hi * wyhi)
            P.append((f'bisector{i},{j}/{s}', ((min(xs), max(xs)), (min(ys), max(ys)))))
    for i, j, k in combinations(range(len(C)), 3):
        ax, ay = C[j][0] - C[i][0], C[j][1] - C[i][1]
        bx, by = C[k][0] - C[i][0], C[k][1] - C[i][1]
        D = ax * by - ay * bx
        if D == 0:
            continue
        e = (C[j][0] ** 2 + C[j][1] ** 2 - C[i][0] ** 2 - C[i][1] ** 2) / 2
        f = (C[k][0] ** 2 + C[k][1] ** 2 - C[i][0] ** 2 - C[i][1] ** 2) / 2
        ux, uy = (e * by - f * ay) / D, (ax * f - bx * e) / D
        if ux * ux + uy * uy <= 1:
            P.append((f'circum{i},{j},{k}', pt(ux, uy)))
    return P


def analyse(C, T, grid=True):
    P = candidates(C)
    lo_all, hi_all, arglo, arghi, fails = F(0), F(0), None, None, []
    for lab, box in P:
        a, b = mindist_iv(box, C)
        if a > lo_all:
            lo_all, arglo = a, lab
        if b > hi_all:
            hi_all, arghi = b, lab
        if not any(dist2_iv(box, c)[1] <= T * T for c in C):
            fails.append(lab)
    return dict(n=len(P), R_lo=lo_all, R_hi=hi_all, arglo=arglo, arghi=arghi,
                fails=fails, grid=grid_max(C) if grid else None)


def grid_max(C, N=1200):
    import numpy as np
    C = np.array([[float(a), float(b)] for a, b in C])
    xs = np.linspace(-1, 1, N + 1)
    best, bp = -1.0, (0.0, 0.0)
    for x in xs:
        hh = math.sqrt(max(0.0, 1 - x * x))
        M = max(2, int(N * hh))
        ys = np.linspace(-hh, hh, M + 1)
        d = np.sqrt(((xs[0] * 0 + x - C[:, 0])[:, None] ** 2 + (ys[None, :] - C[:, 1][:, None]) ** 2)).min(0)
        k = int(np.argmax(d))
        if d[k] > best:
            best, bp = float(d[k]), (x, float(ys[k]))
    x, y = bp
    step = 2.0 / N
    while step > 1e-15:
        moved = False
        for dxx, dyy in ((step, 0), (-step, 0), (0, step), (0, -step)):
            nx, ny = x + dxx, y + dyy
            if nx * nx + ny * ny > 1:
                continue
            d = min(math.hypot(nx - float(c[0]), ny - float(c[1])) for c in C)
            if d > best:
                best, x, y, moved = d, nx, ny, True
        if not moved:
            step *= 0.5
    return best


def main():
    LOG = []; say = lambda s: (print(s), LOG.append(s))

    # ---------- 层 0：已知真值自检 ----------
    say('provenance: original kernel sha256 = '
        + hashlib.sha256(ORIG.read_bytes()).hexdigest())
    say('provenance: input hprec_sol sha256 = '
        + hashlib.sha256(SRC.read_bytes()).hexdigest())
    say('== layer 0: ground-truth controls (known answers) ==')
    ctrl = []
    sq = [(F(s, 2), F(t, 2)) for s in (-1, 1) for t in (-1, 1)]
    r = analyse(sq, F(708, 1000), grid=False)
    ctrl.append(('square(±1/2,±1/2) T=0.708 -> covered', not r['fails']))
    ctrl.append(('square R enclosure ∋ sqrt(1/2) exactly',
                 r['R_lo'] <= sqrt_iv(F(1, 2))[0] and r['R_hi'] >= sqrt_iv(F(1, 2))[1]))
    r2 = analyse(sq, F(707, 1000), grid=False)
    ctrl.append(('square T=0.707 -> rejected (not covered)', bool(r2['fails'])))
    r3 = analyse([(F(0), F(0))], F(1), grid=False)
    ctrl.append(('single disk at 0, T=1 -> covered, R enclosure ∋ 1',
                 not r3['fails'] and r3['R_lo'] <= 1 <= r3['R_hi']))
    for n, ok in ctrl:
        say(f'  [{"PASS" if ok else "FAIL"}] {n}')
    assert all(o for _, o in ctrl), 'ground-truth control FAILED -> stop'

    # ---------- 层 1：候选构型 ----------
    js = json.loads(SRC.read_text(encoding='utf-8'))
    th = [F(s) for s in js['th']]
    C = []
    for j in (0, 2):
        for s in (-1, 1):
            for t in (-1, 1):
                C.append((s * th[j], t * th[j + 1]))
    for j in (4, 5):
        C.extend([(th[j], F(0)), (-th[j], F(0))])
    C.extend([(F(0), th[6]), (F(0), -th[6])])
    assert len(C) == 14
    UPPER = F('1.33173203427623416')
    say('')
    say('== layer 1: candidate from exact decimal literals ==')
    say(f'  centers = 14 ; spec = (2×4-orbit, 2×x-pair, 1×y-pair, no origin)')
    say(f'  all |coord| <= 1.3317 (base-domain box [0,1+L]^7 up to sign/swap): '
        f'{all(abs(v) <= UPPER for v in th)}')
    say(f'  canonical |coords| desc = {[round(float(abs(v)), 6) for v in sorted(th, key=lambda z: -abs(z))]}')

    # ---------- 层 2：覆盖判据 ----------
    T = F('0.33173203427623414')     # 外部评审阈值
    Tp = F('0.33173203427623415')    # 本件抬高后的阈值（仍 < L）
    Lb = F('0.33173203427623416')    # 团队内芯目标
    say('')
    say('== layer 2: exact covering test (Fraction + isqrt directed interval) ==')
    res = {}
    for tag, TT in (('T ', T), ('Tp', Tp)):
        rr = analyse(C, TT)
        res[tag] = rr
        say(f'  threshold {tag} = {float(TT):.20f}: candidates={rr["n"]} uncovered={len(rr["fails"])}'
            f' -> {"PASS (covered)" if not rr["fails"] else "FAIL " + str(rr["fails"][:4])}')
        say(f'     R(C) enclosure = [{float(rr["R_lo"]):.20f}, {float(rr["R_hi"]):.20f}]'
            f'  argmax(lo)={rr["arglo"]} argmax(hi)={rr["arghi"]}')
        say(f'     numpy grid+climb max (cross-check, float64) = {rr["grid"]:.16f}')
    R_lo, R_hi = res['Tp']['R_lo'], res['Tp']['R_hi']

    # ---------- 层 3：排序 ----------
    say('')
    say('== layer 3: exact orderings ==')
    for nm, v in (('R_hi', R_hi), ('T', T), ('Tp', Tp), ('L', Lb)):
        say(f'  {nm:5s} = {float(v):.20f}')
    say(f'  R_hi < T : {R_hi < T}')
    say(f'  R_hi < Tp: {R_hi < Tp}')
    say(f'  R_hi < L : {R_hi < Lb}    (L - R_hi = {float(Lb - R_hi):.3e})')
    say(f'  L - Tp = {Lb - Tp}   Tp - T = {Tp - T}')
    verdict = ('CONFIRMED (exact): R(C) <= T < L -> inner-core target "R>=L" is FALSE near theta0'
               if R_hi < T else
               ('PARTIAL: R(C) <= Tp < L (looser threshold suffices)' if R_hi < Tp else
                'NOT CONFIRMED: enclosure does not separate from L'))
    say('')
    say('== verdict ==')
    say('  ' + verdict)
    say('  scope: certifies the covering radius of THIS candidate only; NOT the family minimum,')
    say('         NOT the global optimum r_D(14).')
    OUT.write_text('\n'.join(LOG) + '\n', encoding='utf-8')
    print(f'\n[written] {OUT}')


if __name__ == '__main__':
    main()
