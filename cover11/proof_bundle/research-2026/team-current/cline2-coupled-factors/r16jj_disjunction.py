"""cline2-coupled-factors R16jj: bounded interval subdivision for the implication
        |G'| <= 0.02   =>   G'' > 0        (wider exploratory form)
and for the disjunction
        G' != 0   OR   G'' > 0             (the obligation)

Legal set: for each face arc (H = 2r sin(2b1-delta) on face 1, H = 2r sin(2b2+delta) on
face 2) the point must satisfy the three feasibility filters
    (F1) H <= 2 r sin(2 b1 - delta)          [inside the face-1 cap]
    (F2) H <= 2 r sin(2 b2 + delta)          [inside the face-2 cap]
    (N)  H^2 - 2 s cos(delta) H + 2 r (1-r) <= 0    [inside the norm circle]
with s = sqrt(1-r^2), H > 0, and delta in [-b2, b1].  (Note: on the face-1 arc (F1) is an
identity; on the face-2 arc (F2) is.)

Method (bounded, no unbounded depth):
  * interval enclosures G'_box, G''_box at 30 dps with the exact 9-decimal coefficients;
  * for each box: if 0 not in G'_box -> certified (G' != 0 on the box);
    else if G''_box > 0 -> certified (G'' > 0 on the box, so no stationary maximum);
    else split the widest scaled dimension (round-robin) and push both halves.
  * the run stops at the box budget; unresolved boxes are returned as live boxes with
    their loose intervals.  No theorem is claimed if the budget runs out.
"""
import math, json, sys, time, heapq
from pathlib import Path
from mpmath import iv

iv.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
C0 = iv.mpf(f'{zJ[3]-zJ[1]:.9f}')
XX1 = iv.mpf(f'{zJ[1]-zJ[9]:.9f}'); XX2 = iv.mpf(f'{zJ[3]-zJ[9]:.9f}')
BE1 = iv.mpf(f'{-zJ[16]:.9f}'); GA1 = iv.mpf(f'{-zJ[78]:.9f}')
BE2 = iv.mpf(f'{zJ[20]:.9f}');  GA2 = iv.mpf(f'{zJ[82]:.9f}')
RR = iv.mpf(19)/50
TWO = iv.mpf(2); ZERO = iv.mpf(0)


def deriv_box(r, b1, b2, dl, face):
    """interval enclosure of (G, G', G'', R1, R2, N) with
    R1 = cap1 - H, R2 = cap2 - H, N = -(H^2 - 2 s cos dl H + 2r(1-r))  (all >= 0 legal)"""
    r = iv.mpf(r); b1 = iv.mpf(b1); b2 = iv.mpf(b2); dl = iv.mpf(dl)
    A = b1-dl; B = b2+dl
    s = iv.sqrt(1-r*r)
    c1 = TWO*r*iv.sin(TWO*b1-dl)
    c2 = TWO*r*iv.sin(TWO*b2+dl)
    if face == 1:
        H = c1; Hp = -TWO*r*iv.cos(TWO*b1-dl); Hpp = -H
    else:
        H = c2; Hp = TWO*r*iv.cos(TWO*b2+dl); Hpp = -H
    R1 = c1-H; R2 = c2-H
    Nc = -(H*H-TWO*s*iv.cos(dl)*H+TWO*r*(1-r))
    kb1 = iv.sin(b1); kb2 = iv.sin(b2)
    k = r*(kb1*iv.sin(A)+kb2*iv.sin(B))
    kp = r*(-kb1*iv.cos(A)+kb2*iv.cos(B))
    kpp = -r*(kb1*iv.sin(A)+kb2*iv.sin(B))
    G = C0*dl+H*k
    Gp = C0+Hp*k+H*kp
    Gpp = Hpp*k+TWO*Hp*kp+H*kpp
    for i, (b, ang, dang, xx, bb, gg) in enumerate(
            [(b1, A, iv.mpf(-1), XX1, BE1, GA1), (b2, B, iv.mpf(1), XX2, BE2, GA2)]):
        on_this = (face == 1 and i == 0) or (face == 2 and i == 1)
        if on_this:
            e = r*iv.sin(ang)/RR
            ep = r*iv.cos(ang)*dang/RR
            epp = -r*iv.sin(ang)/RR
            phi = b; phip = iv.mpf(0); phipp = iv.mpf(0)
        else:
            Y = TWO*r*iv.sin(b)*iv.sin(ang)
            X = H-TWO*r*iv.sin(b)*iv.cos(ang)
            Yp = TWO*r*iv.sin(b)*iv.cos(ang)*dang
            Xp = Hp-TWO*r*iv.sin(b)*(-iv.sin(ang))*dang
            Ypp = -TWO*r*iv.sin(b)*iv.sin(ang)*dang*dang
            Xpp = Hpp-TWO*r*iv.sin(b)*(-iv.cos(ang))*dang*dang
            Q = X*X+Y*Y
            if Q.b < iv.mpf(1)/(50000**2) or Q.a < 0:
                return None
            try:
                sq = iv.sqrt(Q)
            except Exception:
                return None
            Qp = TWO*(X*Xp+Y*Yp)
            Qpp = TWO*(Xp*Xp+X*Xpp+Yp*Yp+Y*Ypp)
            e = sq/(TWO*RR); ep = Qp/(TWO*sq)/(TWO*RR)
            epp = Qpp/(TWO*sq)/(TWO*RR)-Qp*Qp/(4*sq**3)/(TWO*RR)
            num = X*Yp-Y*Xp
            nump = Xp*Yp+X*Ypp-Yp*Xp-Y*Xpp
            phi = iv.atan2(Y, X)
            phip = num/Q
            phipp = (nump*Q-num*Qp)/(Q*Q)
        G += xx*phi+bb*e*e+gg*e
        Gp += xx*phip+(TWO*bb*e+gg)*ep
        Gpp += xx*phipp+(TWO*bb*e+gg)*epp+TWO*bb*ep*ep
    return G, Gp, Gpp, R1, R2, Nc


def partials(r, b1, b2, dl, face, h):
    """central-difference partials of G' wrt the four coordinates, interval-safe"""
    out = []
    for k in range(4):
        xp = [r, b1, b2, dl]; xm = [r, b1, b2, dl]
        if isinstance(xp[k], float):
            xp[k] += h; xm[k] -= h
        else:
            xp[k] = iv.mpf(xp[k])+h; xm[k] = iv.mpf(xm[k])-h
        ap = deriv_box(*xp, face=face); am = deriv_box(*xm, face=face)
        if ap is None or am is None:
            out.append(None); continue
        out.append((ap[1]-am[1])/(2*h))
    return out


def certify(budget=20000, thr=0.02, face_list=(1, 2), rlo=.375, rhi=.38,
            blo=1.0, bhi=None, nexp=6):
    """bounded subdivision; returns stats and the live-box list"""
    if bhi is None:
        bhi = math.acos(rlo)
    # initial cover: split b1,b2 into nexp parts, delta into 2*nexp
    heap = []; cnt = [0]

    def push(bx, prio):
        heapq.heappush(heap, (prio, cnt[0], bx)); cnt[0] += 1
    def rng(lo, hi, n):
        return [(lo+(hi-lo)*i/n, lo+(hi-lo)*(i+1)/n) for i in range(n)]
    dlo, dhi = -bhi, bhi
    for face in face_list:
        for r0, r1 in rng(rlo, rhi, nexp):
            for a0, a1 in rng(blo, bhi, nexp):
                for b0, b1_ in rng(blo, bhi, nexp):
                    for d0, d1 in rng(dlo, dhi, 2*nexp):
                        push((face, r0, r1, a0, a1, b0, b1_, d0, d1), 0.0)
    stats = dict(processed=0, certified=0, infeasible=0, live=0, noQ=0)
    live = []
    t0 = time.time()
    while heap and stats['processed'] < budget:
        _, _, bx = heapq.heappop(heap)
        stats['processed'] += 1
        face, r0, r1, a0, a1, b0, b1_, d0, d1 = bx
        res = deriv_box((r0, r1), (a0, a1), (b0, b1_), (d0, d1), face)
        if res is None:
            stats['noQ'] += 1
            continue
        G, Gp, Gpp, R1, R2, Nc = res
        # feasibility: a box with any residual entirely negative is entirely illegal
        if R1.b < 0 or R2.b < 0 or Nc.b < 0:
            stats['infeasible'] += 1
            continue
        # is the box certainly legal?
        legal_box = (R1.a >= 0 and R2.a >= 0 and Nc.a >= 0)
        if Gp.a > 0 or Gp.b < 0:
            stats['certified'] += 1
            continue
        if Gpp.a > 0:
            stats['certified'] += 1
            continue
        if legal_box:
            stats['live'] += 1
            live.append(dict(face=face, r=(r0, r1), b1=(a0, a1), b2=(b0, b1_),
                             d=(d0, d1), Gp=(float(Gp.a), float(Gp.b)),
                             Gpp=(float(Gpp.a), float(Gpp.b))))
        else:
            stats['live'] += 1
            live.append(dict(face=face, r=(r0, r1), b1=(a0, a1), b2=(b0, b1_),
                             d=(d0, d1), Gp=(float(Gp.a), float(Gp.b)),
                             Gpp=(float(Gpp.a), float(Gpp.b)), partial=True))
        # split widest scaled dimension
        spans = [r1-r0, a1-a0, b1_-b0, d1-d0]
        scales = [rhi-rlo, bhi-blo, bhi-blo, 2*bhi]
        k = max(range(4), key=lambda i: spans[i]/scales[i])
        l, h_ = [(r0, r1), (a0, a1), (b0, b1_), (d0, d1)][k]
        m = 0.5*(l+h_)
        for seg in ((l, m), (m, h_)):
            nb = list(bx)
            if k == 0:
                nb[1], nb[2] = seg
            elif k == 1:
                nb[3], nb[4] = seg
            elif k == 2:
                nb[5], nb[6] = seg
            else:
                nb[7], nb[8] = seg
            push(tuple(nb), -(seg[1]-seg[0]))
    return stats, live, time.time()-t0, len(heap)


if __name__ == '__main__':
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    nexp = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    print(f'bounded interval subdivision: budget {budget} boxes, initial {nexp}x{nexp}x{nexp}x{2*nexp} per face')
    stats, live, dt, left = certify(budget=budget, nexp=nexp)
    print(f'processed {stats["processed"]} in {dt:.1f}s; queue left {left}')
    print(f'  certified   : {stats["certified"]}')
    print(f'  infeasible  : {stats["infeasible"]}')
    print(f'  live (unres): {stats["live"]}')
    print(f'  Q-guard skip: {stats["noQ"]}')
    # gap summary
    if live:
        gp = [b['Gp'] for b in live]
        gpp = [b['Gpp'] for b in live]
        print(f'\nLIVE BOXES: {len(live)}')
        print(f'   G\'  interval bounds across live boxes: '
              f'[{min(v[0] for v in gp):+.6f}, {max(v[1] for v in gp):+.6f}]')
        print(f'   G\'\' interval bounds across live boxes: '
              f'[{min(v[0] for v in gpp):+.6f}, {max(v[1] for v in gpp):+.6f}]')
        # the sharpest live boxes (smallest G'' upper bound)
        worst = sorted(live, key=lambda b: b['Gpp'][1])[:6]
        print('\n   live boxes with the smallest G\'\' upper bound (the actual gap):')
        for b in worst:
            print(f'      face {b["face"]} r={b["r"][0]:.5f}-{b["r"][1]:.5f} '
                  f'b1={b["b1"][0]:.5f}-{b["b1"][1]:.5f} b2={b["b2"][0]:.5f}-{b["b2"][1]:.5f} '
                  f'd={b["d"][0]:.5f}-{b["d"][1]:.5f}  G\'={b["Gp"]}  G\'\'={b["Gpp"]}')
        json.dump(live, open(OUT/'r16jj_live.json', 'w'), indent=1)
        print('\n   saved out/r16jj_live.json')
    print('\nVERDICT:',
          'DISJUNCTION CERTIFIED over the covered region' if stats['live'] == 0
          else 'NOT CLOSED -- live boxes returned; no theorem claimed')
