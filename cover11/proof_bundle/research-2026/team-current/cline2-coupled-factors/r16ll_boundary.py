"""cline2-coupled-factors R16ll: bounded interval subdivision with explicit boundary handling.

Diagnosis from r16kk: the live boxes are PARTIALLY legal -- the norm-circle residual
    Nc = -(H^2 - 2 s cos(delta) H + 2r(1-r))          [H on the arc]
which depends only on (r, delta), changes sign inside those boxes.  The residual is
monotone in H, and on the face-1 arc H = 2r sin(2b1-delta) is monotone in delta, so
Nc = 0 has at most one root in delta per (r,b1,b2) -- a smooth curve, not a thick set.

Algorithm:
  * maintain boxes over (face, r, b1, b2, delta);
  * test the three residuals (R1, R2, Nc) as intervals:
      - any residual with upper bound < 0  -> box entirely ILLEGAL, discard;
      - all residuals with lower bound >= 0 -> box entirely LEGAL, certify by
          (G' != 0)  or  (G'' > 0);
      - otherwise SPLIT, preferring delta (where the boundary lives) and preferring
        the dimension with the largest relative span;
  * budget-bounded: stops at the box count and returns live boxes with their loose
    intervals.  No theorem is claimed if the budget runs out.

Implication tested: |G'| <= 0.02 => G'' > 0  (and the disjunction G' != 0 or G'' > 0).
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


def deriv_box(rr, b1, b2, dl, face):
    r = iv.mpf(rr); b1 = iv.mpf(b1); b2 = iv.mpf(b2); dl = iv.mpf(dl)
    A = b1-dl; B = b2+dl
    s = iv.sqrt(1-r*r)
    c1 = TWO*r*iv.sin(TWO*b1-dl); c2 = TWO*r*iv.sin(TWO*b2+dl)
    H = c1 if face == 1 else c2
    Hp = (-TWO*r*iv.cos(TWO*b1-dl)) if face == 1 else (TWO*r*iv.cos(TWO*b2+dl))
    Hpp = -H
    R1 = c1-H; R2 = c2-H
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
    return G, Gp, Gpp, R1, R2, Nc


def run(budget=20000, nexp=8, thr=0.02):
    bhi = math.acos(0.375)
    heap = []; cnt = [0]

    def push(bx, prio):
        heapq.heappush(heap, (prio, cnt[0], bx)); cnt[0] += 1

    def rng(lo, hi, n):
        return [(lo+(hi-lo)*i/n, lo+(hi-lo)*(i+1)/n) for i in range(n)]
    for face in (1, 2):
        for r0, r1 in rng(.375, .38, nexp):
            for a0, a1 in rng(1.0, bhi, nexp):
                for b0, b1_ in rng(1.0, bhi, nexp):
                    for d0, d1 in rng(-bhi, bhi, 2*nexp):
                        push((face, r0, r1, a0, a1, b0, b1_, d0, d1), 0.0)
    st = dict(cert0=0, certGpp=0, illegal=0, live=0, processed=0, noQ=0)
    live = []
    t0 = time.time()
    while heap and st['processed'] < budget:
        _, _, bx = heapq.heappop(heap)
        st['processed'] += 1
        face, r0, r1, a0, a1, b0, b1_, d0, d1 = bx
        res = deriv_box((r0, r1), (a0, a1), (b0, b1_), (d0, d1), face)
        if res is None:
            st['noQ'] += 1
            continue
        G, Gp, Gpp, R1, R2, Nc = res
        if R1.b < 0 or R2.b < 0 or Nc.b < 0:
            st['illegal'] += 1
            continue
        full_legal = (R1.a >= 0 and R2.a >= 0 and Nc.a >= 0)
        if full_legal and (Gp.b < 0 or Gp.a > 0):
            st['cert0'] += 1
            continue
        if full_legal and Gpp.a > 0:
            st['certGpp'] += 1
            continue
        if full_legal:
            st['live'] += 1
            live.append(dict(face=face, r=(r0, r1), b1=(a0, a1), b2=(b0, b1_),
                             d=(d0, d1), Gp=(float(Gp.a), float(Gp.b)),
                             Gpp=(float(Gpp.a), float(Gpp.b)), legal=True))
        else:
            st['live'] += 1
            live.append(dict(face=face, r=(r0, r1), b1=(a0, a1), b2=(b0, b1_),
                             d=(d0, d1), Gp=(float(Gp.a), float(Gp.b)),
                             Gpp=(float(Gpp.a), float(Gpp.b)), legal=False))
        # split: prefer delta when the box straddles the norm boundary, else widest scaled
        spans = [r1-r0, a1-a0, b1_-b0, d1-d0]
        scales = [.38-.375, bhi-1.0, bhi-1.0, 2*bhi]
        if Nc.b < 0 < Nc.a or (R2.b < 0 < R2.a):
            k = 3 if spans[3] > 1e-9 else max(range(4), key=lambda i: spans[i]/scales[i])
        else:
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
    return st, live, time.time()-t0, len(heap)


if __name__ == '__main__':
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    nexp = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    print(f'boundary-aware subdivision: budget={budget}, initial {nexp} grid, thr={0.02}')
    st, live, dt, left = run(budget=budget, nexp=nexp)
    print(f'processed {st["processed"]} in {dt:.1f}s; queue {left}')
    print(f'  certified by G\'!=0 : {st["cert0"]}')
    print(f'  certified by G\'\'>0 : {st["certGpp"]}')
    print(f'  illegal            : {st["illegal"]}')
    print(f'  live               : {st["live"]}')
    print(f'  Q-guard            : {st["noQ"]}')
    legal_live = [b for b in live if b['legal']]
    print(f'\n  live boxes that are FULLY LEGAL: {len(legal_live)}')
    if legal_live:
        gp = [b['Gp'] for b in legal_live]; gpp = [b['Gpp'] for b in legal_live]
        print(f'     G\'  bounds: [{min(v[0] for v in gp):+.6f}, {max(v[1] for v in gp):+.6f}]')
        print(f'     G\'\' bounds: [{min(v[0] for v in gpp):+.6f}, {max(v[1] for v in gpp):+.6f}]')
        w = sorted(legal_live, key=lambda b: b['Gpp'][1])[:5]
        print('     legal live boxes with the smallest G\'\' upper bound:')
        for b in w:
            print(f'        face {b["face"]} r={b["r"][0]:.6f}-{b["r"][1]:.6f} '
                  f'b1={b["b1"][0]:.5f}-{b["b1"][1]:.5f} b2={b["b2"][0]:.5f}-{b["b2"][1]:.5f}'
                  f' d={b["d"][0]:.6f}-{b["d"][1]:.6f}')
            print(f'           G\'={b["Gp"]}  G\'\'={b["Gpp"]}')
    print(f'\n  live boxes only PARTIALLY legal: {len(live)-len(legal_live)} '
          f'(their legal part is not resolved)')
    json.dump(live, open(OUT/'r16ll_live.json', 'w'), indent=1)
    print('\n  saved out/r16ll_live.json')
    print('VERDICT:', 'CERTIFIED over the resolved part' if not live else
          'NOT CLOSED -- live boxes returned; no theorem claimed')
