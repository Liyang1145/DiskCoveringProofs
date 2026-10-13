"""cline2-coupled-factors R16L: dependency-safe interval certificate for the j=0 branch.

Method.  On the face-1 branch, H = 2r sin(2b1-delta) is EXPLICIT, and the exact derivative
    G = dV/ddelta = C0 + H k' + H' k  +  [on-face-1]  +  [off-face-2]
has the following structure, each piece depending on (r,b1,b2,delta) through elementary
functions only.  We bound G on a box B centred at x0 by the RIGOROUS mean-value form

    G(B) subset G(x0) +- sum_i |partial_i G|(B) * h_i ,

where the partials are bounded by interval enclosures of EXPLICIT second-derivative
expressions (the recursion is written out below, term by term, using
  d/ddelta A = -1, d/ddelta B = +1, d/db1 A = 1, d/db2 B = 1, d/dr H = 2 sin(2b1-delta)
and, for the off-face quantities, closing the chain with the exact identities
  X = H-2r sin b2 cos B,  Y = 2r sin b2 sin B,
  X' = H'+2r sin b2 sin B, Y' = 2r sin b2 cos B,
  X'' = H''+2r sin b2 cos B, Y'' = -2r sin b2 sin B
plus the second-order chain rules for e2=sqrt(Q)/2R, phi2=atan2(Y,X),
phi2'=(X Y'-Y X')/Q, (1/(2 sqrt Q))' = -Q'/(4 Q^{3/2}).

This is a proof method (interval + mean value), not sampling.
Claim attempted: G >= 0.15 on the admissible set of the j=0 branch.
"""
import math, json, sys, time, heapq
from pathlib import Path
from mpmath import iv

iv.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
C0 = iv.mpf(f'{zJ[3]-zJ[1]:.9f}')
BE1 = iv.mpf(f'{-zJ[16]:.9f}')
GA1 = iv.mpf(f'{-zJ[78]:.9f}')
XX2 = iv.mpf(f'{zJ[3]-zJ[9]:.9f}')
BE2 = iv.mpf(f'{zJ[20]:.9f}')
GA2 = iv.mpf(f'{zJ[82]:.9f}')
RR = iv.mpf(19)/50
THRESH = 0.15
TWO = iv.mpf(2)


def parts(r, b1, b2, dl):
    """all quantities needed, as intervals; returns None if Q leaves the admissible range"""
    s = iv.sqrt(1-r*r)
    A = b1-dl; B = b2+dl
    sinA = iv.sin(A); cosA = iv.cos(A)
    sinB = iv.sin(B); cosB = iv.cos(B)
    sb1 = iv.sin(b1); cb1 = iv.cos(b1)
    sb2 = iv.sin(b2); cb2 = iv.cos(b2)
    H = TWO*r*iv.sin(2*b1-dl)
    H1 = -TWO*r*iv.cos(2*b1-dl)          # dH/ddelta
    H2 = -H                               # d2H/ddelta2 = -H
    Hr = TWO*iv.sin(2*b1-dl)              # dH/dr
    H1r = -TWO*iv.cos(2*b1-dl)            # d2H/ddelta dr
    H1b1 = -4*r*iv.sin(2*b1-dl)           # d2H/ddelta db1
    Hb1 = 4*r*iv.cos(2*b1-dl)             # dH/db1
    H1b2 = iv.mpf(0); Hb2 = iv.mpf(0)
    Hrb1 = TWO*iv.cos(2*b1-dl)            # d2H/dr db1
    H1dl_r = H1r
    # k = r(sin b1 sinA + sin b2 sinB);  k' = r(-sin b1 cosA + sin b2 cosB)
    k = r*(sb1*sinA+sb2*sinB)
    kp = r*(-sb1*cosA+sb2*cosB)
    # dk/ddelta = kp ; dk'/ddelta = -r(sin b1 sinA + sin b2 sinB)
    kp1 = -r*(sb1*sinA+sb2*sinB)
    kr = sb1*sinA+sb2*sinB
    kb1 = r*(cb1*sinA+sb1*cosA)
    kb2 = r*(cb2*sinB+sb2*cosB)
    kpr = -sb1*cosA+sb2*cosB
    kpb1 = r*(-cb1*cosA-sb1*sinA)
    kpb2 = r*(-cb2*cosB+sb2*sinB)
    # ON-face 1
    e1 = r*sinA/RR
    e1p = -r*cosA/RR
    e1pp = -r*sinA/RR
    e1r = sinA/RR; e1rp = -cosA/RR; e1b1 = -r*cosA/RR; e1b1p = r*sinA/RR
    # OFF-face 2
    Y = TWO*r*sb2*sinB
    X = H-TWO*r*sb2*cosB
    Q = X*X+Y*Y
    if Q.b < iv.mpf(1)/(50000**2):
        return None
    sq = iv.sqrt(Q)
    phi = iv.atan2(Y, X)
    Y1 = TWO*r*sb2*cosB
    X1 = H1+TWO*r*sb2*sinB
    Y2 = -TWO*r*sb2*sinB
    X2 = H2+TWO*r*sb2*cosB
    Q1 = TWO*(X*X1+Y*Y1)
    Q2 = TWO*(X1*X1+X*X2+Y1*Y1+Y*Y2)
    e2 = sq/(TWO*RR)
    e2p = Q1/(TWO*sq)/(TWO*RR)
    e2pp = Q2/(TWO*sq)/(TWO*RR)-Q1*Q1/(4*sq**3)/(TWO*RR)
    phip = (X*Y1-Y*X1)/Q
    phipp = ((X*Y2-Y*X2)*Q-(X*Y1-Y*X1)*Q1)/(Q*Q)
    # partials wrt r, b1, b2 of the off-face quantities
    Yr = TWO*sb2*sinB; Xr = Hr-TWO*sb2*cosB
    Yb2 = TWO*r*cb2*sinB+TWO*r*sb2*cosB; Xb2 = Hb2-TWO*r*cb2*cosB+TWO*r*sb2*sinB
    Yb1 = iv.mpf(0); Xb1 = Hb1
    Qr = TWO*(X*Xr+Y*Yr); Qb1 = TWO*(X*Xb1+Y*Yb1); Qb2 = TWO*(X*Xb2+Y*Yb2)
    e2r = Qr/(TWO*sq)/(TWO*RR); e2b1 = Qb1/(TWO*sq)/(TWO*RR); e2b2 = Qb2/(TWO*sq)/(TWO*RR)
    phir = (X*Yr-Y*Xr)/Q
    phib1 = (X*Yb1-Y*Xb1)/Q
    phib2 = (X*Yb2-Y*Xb2)/Q
    return dict(s=s, A=A, B=B, sinA=sinA, cosA=cosA, sinB=sinB, cosB=cosB,
                H=H, H1=H1, H2=H2, Hr=Hr, H1r=H1r, H1b1=H1b1, Hb1=Hb1, Hrb1=Hrb1,
                k=k, kp=kp, kp1=kp1, kr=kr, kb1=kb1, kb2=kb2, kpr=kpr, kpb1=kpb1,
                kpb2=kpb2, e1=e1, e1p=e1p, e1pp=e1pp, e1r=e1r, e1rp=e1rp,
                e1b1=e1b1, e1b1p=e1b1p,
                e2=e2, e2p=e2p, e2pp=e2pp, e2r=e2r, e2b1=e2b1, e2b2=e2b2,
                phip=phip, phipp=phipp, phir=phir, phib1=phib1, phib2=phib2,
                X=X, Y=Y, Q=Q)


def G_and_grad(r, b1, b2, dl):
    p = parts(r, b1, b2, dl)
    if p is None:
        return None
    H = p['H']; H1 = p['H1']; H2 = p['H2']
    k = p['k']; kp = p['kp']; kp1 = p['kp1']
    ea = p['e1']; eap = p['e1p']; eapp = p['e1pp']
    e2 = p['e2']; e2p = p['e2p']; e2pp = p['e2pp']
    phip = p['phip']; phipp = p['phipp']
    # G
    G = C0+H*kp+H1*k+BE1*TWO*ea*eap+GA1*eap+XX2*phip+BE2*TWO*e2*e2p+GA2*e2p
    # dG/ddelta
    Gd = (H1*kp+H*kp1+H2*k+H1*kp) + (BE1*TWO*(eap*eap+ea*eapp)+GA1*eapp) \
        + XX2*phipp + (BE2*TWO*(e2p*e2p+e2*e2pp)+GA2*e2pp)
    # dG/dr  (H', k, k', e1, e1', e2, e2', phi' all depend on r)
    Gr = (p['Hr']*kp+H*p['kpr']+p['H1r']*k+H1*p['kr']) \
        + (BE1*TWO*(p['e1r']*eap+ea*p['e1rp'])+GA1*p['e1rp']) \
        + XX2*p['phir'] + BE2*TWO*p['e2r']*e2p+GA2*p['e2r']
    # dG/db1
    Gb1 = (p['Hb1']*kp+H*p['kpb1']+p['H1b1']*k+H1*p['kb1']) \
        + (BE1*TWO*(p['e1b1']*eap+ea*p['e1b1p'])+GA1*p['e1b1p']) \
        + XX2*p['phib1'] + BE2*TWO*p['e2b1']*e2p+GA2*p['e2b1']
    # dG/db2
    Gb2 = (H*p['kpb2']+H1*p['kb2']) \
        + XX2*p['phib2'] + BE2*TWO*p['e2b2']*e2p+GA2*p['e2b2']
    return G, Gr, Gb1, Gb2, Gd


def certify(budget=200000, rlo=.375, rhi=.38, blo=1.0, sub=4):
    bhi = math.acos(rlo)
    def rng(lo, hi, n):
        return [(lo+(hi-lo)*i/n, lo+(hi-lo)*(i+1)/n) for i in range(n)]
    heap = []
    seq = [0]
    def push(bx):
        heapq.heappush(heap, (0.0, seq[0], bx)); seq[0] += 1
    for r0, r1 in rng(rlo, rhi, sub):
        for b10, b11 in rng(blo, bhi, sub):
            for b20, b21 in rng(blo, bhi, sub):
                for d0, d1 in rng(-bhi, bhi, 2*sub):
                    push((r0, r1, b10, b11, b20, b21, d0, d1))
    st = dict(certified=0, infeasible=0, split=0, processed=0)
    worst = None
    t0 = time.time()
    while heap and st['processed'] < budget:
        _, _, bx = heapq.heappop(heap)
        st['processed'] += 1
        r0, r1, b10, b11, b20, b21, d0, d1 = bx
        rc = iv.mpf(0.5*(r0+r1)); b1c = iv.mpf(0.5*(b10+b11))
        b2c = iv.mpf(0.5*(b20+b21)); dc = iv.mpf(0.5*(d0+d1))
        # admissibility at the centre
        pp = parts(rc, b1c, b2c, dc)
        if pp is None:
            st['infeasible'] += 1; continue
        Hc = pp['H']
        cap2 = TWO*rc*iv.sin(TWO*b2c+dc)
        beta = Hc*Hc-TWO*pp['s']*iv.cos(dc)*Hc+TWO*rc*(1-rc)
        if float(cap2.b) < float(Hc.a) or float(beta.a) > 0:
            st['infeasible'] += 1; continue
        bnd = G_and_grad(iv.mpf([r0, r1]), iv.mpf([b10, b11]), iv.mpf([b20, b21]),
                         iv.mpf([d0, d1]))
        if bnd is None:
            st['infeasible'] += 1; continue
        pt = G_and_grad(rc, b1c, b2c, dc)
        if pt is None:
            st['infeasible'] += 1; continue
        G, Gr, Gb1, Gb2, Gd = bnd
        G0 = pt[0]
        hr = 0.5*(r1-r0); h1 = 0.5*(b11-b10); h2 = 0.5*(b21-b20); hd = 0.5*(d1-d0)
        L = abs(Gr)*hr+abs(Gb1)*h1+abs(Gb2)*h2+abs(Gd)*hd
        lo = float(G0.a)-float(L.b)
        if lo >= THRESH:
            st['certified'] += 1
            if worst is None or lo < worst[0]:
                worst = (lo, bx)
            continue
        st['split'] += 1
        if worst is None or lo < worst[0]:
            worst = (lo, bx)
        scales = [rhi-rlo, bhi-blo, bhi-blo, 2*bhi]
        hw = [hr, h1, h2, hd]
        kq = max(range(4), key=lambda i: hw[i]/scales[i])
        lo_, hi_ = [(r0, r1), (b10, b11), (b20, b21), (d0, d1)][kq]
        m = 0.5*(lo_+hi_)
        for seg in ((lo_, m), (m, hi_)):
            nb = list(bx); nb[2*kq] = seg[0]; nb[2*kq+1] = seg[1]
            push(tuple(nb))
    return st, worst, time.time()-t0, len(heap)


if __name__ == '__main__':
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    sub = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    print(f'j=0 mean-value certificate: budget={budget}, initial grid {sub}x{sub}x{sub}x{2*sub}')
    st, worst, dt, left = certify(budget=budget, sub=sub)
    print(f'processed {st["processed"]} boxes in {dt:.1f}s; queue left {left}')
    print(f'  certified={st["certified"]} infeasible={st["infeasible"]} split={st["split"]}')
    if worst:
        print(f'worst lower bound = {worst[0]:.6f}')
        bx = worst[1]
        print('   r=[%.6f,%.6f] b1=[%.6f,%.6f] b2=[%.6f,%.6f] d=[%.6f,%.6f]'
              % (bx[0], bx[1], bx[2], bx[3], bx[4], bx[5], bx[6], bx[7]))
    print('verdict:', 'CLOSED' if st['split'] == 0 and left == 0 else 'NOT CLOSED')
