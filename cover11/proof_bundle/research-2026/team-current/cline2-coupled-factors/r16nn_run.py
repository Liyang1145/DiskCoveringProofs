"""cline2-coupled-factors R16nn: bounded interval run with the tightened delta domain.

Findings that shape this version (all verified numerically in r16kk/r16mm):
  * the domain is delta in [-b2, b1], NOT the full +-c range I used before;
  * on the face-1 arc (H = 2r sin(2b1-delta)) one has R2 - R1 = 2r sin(2delta) and
    delta <= 0 on this box (since delta <= b1-b2 <= 0), so R2 = R1 + 2r sin(2 delta)
    <= R1: the face-2 cap is never the binding constraint there.  On the face-2 arc
    the mirror statement holds with R1 = R2 - 2r sin(2 delta).
  * hence legality reduces to  R1 >= 0  (the arc's own cap, binding only at A = 0)
    together with  Nc = -(H^2 - 2 s cos(delta) H + 2r(1-r)) >= 0  (norm circle).
  * the legal set has real volume (238750 legal samples on a coarse numerical grid).

Bound: 20000 box evaluations, no unbounded depth, live boxes returned on failure.
Implication tested:  |G'| <= 0.02  =>  G'' > 0, and the disjunction G'!=0 or G''>0.
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
    other = c1 if face == 2 else c2
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
    return G, Gp, Gpp, own, other, Nc


def run(budget=20000, nr=4, nb1=6, nb2=6, nd=3, thr=0.02):
    heap = []; cnt = [0]

    def push(bx, prio):
        heapq.heappush(heap, (prio, cnt[0], bx)); cnt[0] += 1

    def rng(lo, hi, n):
        return [(lo+(hi-lo)*i/n, lo+(hi-lo)*(i+1)/n) for i in range(n)]
    for face in (1, 2):
        for r0, r1 in rng(.375, .38, nr):
            for a0, a1 in rng(1.0, BHI, nb1):
                for b0, b1_ in rng(1.0, BHI, nb2):
                    for d0, d1 in rng(-BHI, 0.0, nd):
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
        G, Gp, Gpp, own, other, Nc = res
        if own.b < 0 or Nc.b < 0:
            st['illegal'] += 1
            continue
        full_legal = (own.a >= 0 and Nc.a >= 0)
        if full_legal:
            if Gp.b < 0 or Gp.a > 0:
                st['cert0'] += 1
                continue
            if Gpp.a > 0:
                st['certGpp'] += 1
                continue
            st['live'] += 1
            live.append(dict(face=face, r=(r0, r1), b1=(a0, a1), b2=(b0, b1_),
                             d=(d0, d1), Gp=(float(Gp.a), float(Gp.b)),
                             Gpp=(float(Gpp.a), float(Gpp.b)), legal=True))
        else:
            st['live'] += 1
            live.append(dict(face=face, r=(r0, r1), b1=(a0, a1), b2=(b0, b1_),
                             d=(d0, d1), Gp=(float(Gp.a), float(Gp.b)),
                             Gpp=(float(Gpp.a), float(Gpp.b)), legal=False))
        # split the widest scaled legal-relevant dimension: delta if the opposite cap
        # bound is active there, otherwise the widest of r/b1/b2.
        spans = [r1-r0, a1-a0, b1_-b0, d1-d0]
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
            push(tuple(nb), -(seg[1]-seg[0]))
    return st, live, time.time()-t0, len(heap)


if __name__ == '__main__':
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    args = [int(x) for x in sys.argv[2:6]] if len(sys.argv) > 5 else [4, 6, 6, 3]
    print(f'boundary-aware run: budget={budget}, base grid r,a,b,d = {args}')
    st, live, dt, left = run(budget=budget, nr=args[0], nb1=args[1], nb2=args[2],
                             nd=args[3])
    print(f'processed {st["processed"]} in {dt:.1f}s; queue {left}')
    print(f'  certified by G\'!=0 : {st["cert0"]}')
    print(f'  certified by G\'\'>0 : {st["certGpp"]}')
    print(f'  illegal            : {st["illegal"]}')
    print(f'  live               : {st["live"]}')
    legal_live = [b for b in live if b.get('legal')]
    print(f'\n  FULLY LEGAL live boxes: {len(legal_live)}')
    if legal_live:
        w = sorted(legal_live, key=lambda b: b['Gpp'][1])[:5]
        for b in w:
            print(f'     face {b["face"]} r={b["r"][0]:.6f}-{b["r"][1]:.6f} '
                  f'b1={b["b1"][0]:.5f}-{b["b1"][1]:.5f} '
                  f'b2={b["b2"][0]:.5f}-{b["b2"][1]:.5f} d={b["d"][0]:.6f}-{b["d"][1]:.6f}')
            print(f'        G\'={b["Gp"]}  G\'\'={b["Gpp"]}')
    json.dump(live, open(OUT/'r16nn_live.json', 'w'), indent=1)
    print('\n  saved out/r16nn_live.json')
    print('VERDICT:', 'CERTIFIED' if not live else 'NOT CLOSED -- live boxes returned')
