"""cline2-coupled-factors R16pp: bounded run, delta-first refinement (final structure).

Rationale from the failed runs: the legal set is bounded by the norm-circle residual
    Nc = -(H^2 - 2 s cos(delta) H + 2r(1-r))
which is monotone in delta on each arc; a box can be certified legal only if its delta
width is small compared to its distance from the Nc = 0 boundary.  Likewise G' != 0 can
only be certified on boxes narrow in delta (G'' sets the rate).  Hence delta must be the
first coordinate to refine, with (r, b1, b2) refined only when the interval stays open.

Budget: 20000 box evaluations (hard stop), live boxes returned with their loose intervals.
Filters: own-cap (>= 0), norm circle (>= 0); the opposite cap is implied on this box as
shown in r16nn.  Coefficients exact 9-decimal.
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
TWO = iv.mpf(2)
BHI = math.acos(0.375)


def deriv_box(rr, b1, b2, dl, face):
    r = iv.mpf(rr); b1 = iv.mpf(b1); b2 = iv.mpf(b2); dl = iv.mpf(dl)
    A = b1-dl; B = b2+dl
    s = iv.sqrt(1-r*r)
    c1 = TWO*r*iv.sin(TWO*b1-dl); c2 = TWO*r*iv.sin(TWO*b2+dl)
    H = c1 if face == 1 else c2
    Hp = (-TWO*r*iv.cos(TWO*b1-dl)) if face == 1 else (TWO*r*iv.cos(TWO*b2+dl))
    Hpp = -H
    own = (c1-H) if face == 1 else (c2-H)
    Nc = -(H*H-TWO*s*iv.cos(dl)*H+TWO*r*(1-r))
    k = r*(iv.sin(b1)*iv.sin(A)+iv.sin(b2)*iv.sin(B))
    kp = r*(-iv.sin(b1)*iv.cos(A)+iv.sin(b2)*iv.cos(B))
    kpp = -k
    G = C0*dl+H*k
    Gp = C0+Hp*k+H*kp
    Gpp = Hpp*k+TWO*Hp*kp+H*kpp
    for i, (b, ang, dang, xx, bb, gg) in enumerate(
            [(b1, A, iv.mpf(-1), XX1, BE1, GA1), (b2, B, iv.mpf(1), XX2, BE2, GA2)]):
        on_this = (face == 1 and i == 0) or (face == 2 and i == 1)
        if on_this:
            e = r*iv.sin(ang)/RR; ep = r*iv.cos(ang)*dang/RR; epp = -e
            phi = b; phip = iv.mpf(0); phipp = iv.mpf(0)
        else:
            Y = TWO*r*iv.sin(b)*iv.sin(ang)
            X = H-TWO*r*iv.sin(b)*iv.cos(ang)
            Yp = TWO*r*iv.sin(b)*iv.cos(ang)*dang
            Xp = Hp+TWO*r*iv.sin(b)*iv.sin(ang)*dang
            Ypp = -TWO*r*iv.sin(b)*iv.sin(ang)
            Xpp = Hpp+TWO*r*iv.sin(b)*iv.cos(ang)
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
    return G, Gp, Gpp, own, Nc


def run(budget=20000, ncell=4, nd=8):
    heap = []; cnt = [0]

    def push(bx):
        heapq.heappush(heap, (0.0, cnt[0], bx)); cnt[0] += 1

    def rng(lo, hi, n):
        return [(lo+(hi-lo)*i/n, lo+(hi-lo)*(i+1)/n) for i in range(n)]
    for face in (1, 2):
        for r0, r1 in rng(.375, .38, ncell):
            for a0, a1 in rng(1.0, BHI, ncell):
                for b0, b1_ in rng(1.0, BHI, ncell):
                    for d0, d1 in rng(-BHI, 0.0, nd*ncell):
                        push((face, r0, r1, a0, a1, b0, b1_, d0, d1))
    st = dict(cert0=0, certGpp=0, illegal=0, live=0, legal_live=0, legal_seen=0,
              processed=0, noQ=0)
    live = []
    t0 = time.time()
    while heap and st['processed'] < budget:
        _, _, bx = heapq.heappop(heap)
        st['processed'] += 1
        face, r0, r1, a0, a1, b0, b1_, d0, d1 = bx
        res = deriv_box((r0, r1), (a0, a1), (b0, b1_), (d0, d1), face)
        if res is None:
            st['noQ'] += 1; continue
        G, Gp, Gpp, own, Nc = res
        if own.b < 0 or Nc.b < 0:
            st['illegal'] += 1; continue
        if own.a >= 0 and Nc.a >= 0:
            st['legal_seen'] += 1
            if Gp.b < 0 or Gp.a > 0:
                st['cert0'] += 1; continue
            if Gpp.a > 0:
                st['certGpp'] += 1; continue
            st['live'] += 1; st['legal_live'] += 1
            live.append(dict(face=face, r=(r0, r1), b1=(a0, a1), b2=(b0, b1_),
                             d=(d0, d1), Gp=[float(Gp.a), float(Gp.b)],
                             Gpp=[float(Gpp.a), float(Gpp.b)], legal=True))
        else:
            st['live'] += 1
            if len(live) < 100000:
                live.append(dict(face=face, r=(r0, r1), b1=(a0, a1), b2=(b0, b1_),
                                 d=(d0, d1), Gp=[float(Gp.a), float(Gp.b)],
                                 Gpp=[float(Gpp.a), float(Gpp.b)], legal=False,
                                 Nc=[float(Nc.a), float(Nc.b)]))
        # delta-first split
        dspan = d1-d0
        if dspan > 1e-9 and (Nc.b < 0 < Nc.a or (Gp.a <= 0 <= Gp.b) or dspan > 0.004):
            k = 3
        else:
            spans = [r1-r0, a1-a0, b1_-b0, dspan]
            scales = [.005, BHI-1.0, BHI-1.0, BHI]
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
            push(tuple(nb))
    return st, live, time.time()-t0, len(heap)


if __name__ == '__main__':
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    ncell = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    nd = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    st, live, dt, left = run(budget=budget, ncell=ncell, nd=nd)
    print(f'delta-first run: budget={budget}, cells={ncell}, d-splits={nd}')
    print(f'processed {st["processed"]} in {dt:.1f}s; queue {left}')
    print(f'  certified by G\'!=0 : {st["cert0"]}')
    print(f'  certified by G\'\'>0 : {st["certGpp"]}')
    print(f'  illegal            : {st["illegal"]}')
    print(f'  LEGAL boxes seen   : {st["legal_seen"]}')
    print(f'  legal live         : {st["legal_live"]}')
    ll = [b for b in live if b.get('legal')]
    if ll:
        w = sorted(ll, key=lambda b: b['Gpp'][1])[:5]
        print('  legal live boxes with smallest G\'\' upper bound:')
        for b in w:
            print(f'     face {b["face"]} r={b["r"][0]:.6f}-{b["r"][1]:.6f} '
                  f'b1={b["b1"][0]:.5f}-{b["b1"][1]:.5f} b2={b["b2"][0]:.5f}-{b["b2"][1]:.5f}'
                  f' d={b["d"][0]:.6f}-{b["d"][1]:.6f}  G\'={b["Gp"]}  G\'\'={b["Gpp"]}')
    # the tightest Nc-straddling boxes tell us the actual gap
    nn = [b for b in live if not b.get('legal') and 'Nc' in b][:5]
    if nn:
        print('  sample partially-legal live boxes (Nc straddles 0):')
        for b in nn:
            print(f'     face {b["face"]} r={b["r"][0]:.7f}-{b["r"][1]:.7f} '
                  f'b1={b["b1"][0]:.6f}-{b["b1"][1]:.6f} b2={b["b2"][0]:.6f}-{b["b2"][1]:.6f}'
                  f' d={b["d"][0]:.7f}-{b["d"][1]:.7f}')
            print(f'        Nc={b["Nc"]}  G\'={b["Gp"]}  G\'\'={b["Gpp"]}')
    json.dump(live[:20000], open(OUT/'r16pp_live.json', 'w'), indent=1)
    print('  saved live boxes to out/r16pp_live.json')
    print('VERDICT:', 'CERTIFIED (no live boxes)' if st['live'] == 0 else
          'NOT CLOSED -- live boxes returned; no theorem claimed')
