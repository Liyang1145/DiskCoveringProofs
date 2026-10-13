"""cline2-coupled-factors R16rr: bounded run with the cap residuals as exact trig forms.

Symbolic simplification (the reason earlier runs produced zero legal boxes): on the face-1
arc  H = 2r sin(2b1-delta)  identically, hence
    R1 = cap1 - H = 0                                  (exactly)
    R2 = cap2 - H = 2r [ sin(2b2+delta) - sin(2b1-delta) ]
                  = 4r cos(b1+b2) sin(2delta)            (with 2delta = 2b2+delta-(2b1-delta))
Interval arithmetic on two separately-computed sines inflates these to +-0.045, which is
why every box looked partially legal; the factored form removes the spurious width.
On the face-2 arc the mirror statements hold with b1 <-> b2.

Legality therefore reduces to
    (i)  delta <= 0  (so R2 >= 0;  note cos(b1+b2) < 0 on the box, both b in [1,1.187])
    (ii) Nc = -(H^2 - 2 s cos(delta) H + 2r(1-r)) >= 0     (norm circle)
and the only genuine (nontrivial) boundary is the norm circle in (r, delta).

Budget 20000 boxes; live boxes returned, no theorem claimed.
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
    # exact residual: own cap is zero by construction; opposite cap via the trig identity
    R2 = (TWO*TWO)*r*iv.cos(b1+b2)*iv.sin(dl+dl)
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
    return G, Gp, Gpp, R2, Nc


def run(budget=20000, ncells=3, nd0=12):
    heap = []; cnt = [0]

    def push(bx):
        heapq.heappush(heap, (0.0, cnt[0], bx)); cnt[0] += 1

    def rng(lo, hi, n):
        return [(lo+(hi-lo)*i/n, lo+(hi-lo)*(i+1)/n) for i in range(n)]
    for face in (1, 2):
        for r0, r1 in rng(.375, .38, ncells):
            for a0, a1 in rng(1.0, BHI, ncells):
                for b0, b1_ in rng(1.0, BHI, ncells):
                    for d0, d1 in rng(-BHI, 0.0, nd0*ncells):
                        push((face, r0, r1, a0, a1, b0, b1_, d0, d1))
    st = dict(cert0=0, certGpp=0, illegal=0, legal_seen=0, legal_live=0,
              partial_live=0, processed=0, noQ=0, certR2=0)
    legal_live = []; partial_live = []
    t0 = time.time()
    while heap and st['processed'] < budget:
        _, _, bx = heapq.heappop(heap)
        st['processed'] += 1
        face, r0, r1, a0, a1, b0, b1_, d0, d1 = bx
        res = deriv_box((r0, r1), (a0, a1), (b0, b1_), (d0, d1), face)
        if res is None:
            st['noQ'] += 1; continue
        G, Gp, Gpp, R2, Nc = res
        if R2.b < 0 or Nc.b < 0:
            st['illegal'] += 1; continue
        if R2.a >= 0 and Nc.a >= 0:
            st['legal_seen'] += 1
            if Gp.b < 0 or Gp.a > 0:
                st['cert0'] += 1; continue
            if Gpp.a > 0:
                st['certGpp'] += 1; continue
            st['legal_live'] += 1
            legal_live.append(dict(face=face, r=[r0, r1], b1=[a0, a1], b2=[b0, b1_],
                                   d=[d0, d1], Gp=[float(Gp.a), float(Gp.b)],
                                   Gpp=[float(Gpp.a), float(Gpp.b)]))
        else:
            st['partial_live'] += 1
            if len(partial_live) < 200000:
                partial_live.append(dict(face=face, r=[r0, r1], b1=[a0, a1],
                                         b2=[b0, b1_], d=[d0, d1],
                                         R2=[float(R2.a), float(R2.b)],
                                         Nc=[float(Nc.a), float(Nc.b)],
                                         Gp=[float(Gp.a), float(Gp.b)],
                                         Gpp=[float(Gpp.a), float(Gpp.b)]))
        if Nc.b < 0 < Nc.a:
            k = 3
        else:
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
            push(tuple(nb))
    return st, legal_live, partial_live, time.time()-t0, len(heap)


if __name__ == '__main__':
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    ncells = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    nd0 = int(sys.argv[3]) if len(sys.argv) > 3 else 12
    st, ll, pl, dt, left = run(budget=budget, ncells=ncells, nd0=nd0)
    print(f'factored-residual run: budget={budget} cells={ncells} d0={nd0}')
    print(f'processed {st["processed"]} in {dt:.1f}s; queue {left}')
    print(f'  certified by G\'!=0 : {st["cert0"]}')
    print(f'  certified by G\'\'>0 : {st["certGpp"]}')
    print(f'  illegal            : {st["illegal"]}')
    print(f'  fully-legal boxes  : {st["legal_seen"]} (unresolved {st["legal_live"]})')
    print(f'  partially-legal    : {st["partial_live"]}')
    if ll:
        print('\n  UNRESOLVED FULLY-LEGAL BOXES (the real gap):')
        for b in sorted(ll, key=lambda t: t['Gpp'][1])[:6]:
            print(f'     face {b["face"]} r={b["r"][0]:.6f}-{b["r"][1]:.6f} '
                  f'b1={b["b1"][0]:.6f}-{b["b1"][1]:.6f} b2={b["b2"][0]:.6f}-{b["b2"][1]:.6f}'
                  f' d={b["d"][0]:.7f}-{b["d"][1]:.7f}')
            print(f'        G\'={b["Gp"]}  G\'\'={b["Gpp"]}')
    if pl:
        pos = sum(1 for b in pl if b['Gp'][0] > 0)
        neg = sum(1 for b in pl if b['Gp'][1] < 0)
        both = sum(1 for b in pl if b['Gp'][0] <= 0 <= b['Gp'][1])
        posg = sum(1 for b in pl if b['Gpp'][0] > 0)
        print(f'\n  of {len(pl)} partial boxes: G\'>0 certain {pos}, G\'<0 certain {neg}, '
              f'straddling {both}; G\'\'>0 certain {posg}')
        nn = sorted(pl, key=lambda t: abs(t['Nc'][0]))[:4]
        print('  tightest partial boxes (Nc near 0):')
        for b in nn:
            print(f'     face {b["face"]} r={b["r"][0]:.7f}-{b["r"][1]:.7f} '
                  f'd={b["d"][0]:.7f}-{b["d"][1]:.7f} Nc={b["Nc"]} G\'={b["Gp"]}')
    json.dump({'legal_live': ll[:20000], 'partial': pl[:20000]},
              open(OUT/'r16rr_live.json', 'w'), indent=1)
    print('\n  saved out/r16rr_live.json')
    print('VERDICT:', 'CERTIFIED' if (not ll and st['partial_live'] == 0) else
          'NOT CLOSED -- live boxes returned; no theorem claimed')
