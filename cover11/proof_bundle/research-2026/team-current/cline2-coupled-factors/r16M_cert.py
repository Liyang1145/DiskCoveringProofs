"""cline2-coupled-factors R16M: interval certificate for the j=0 branch, systematic Jacobian.

Instead of hand-assembling the second derivatives (error-prone), we propagate an explicit
Jacobian table and close the chain rule exactly.

Base quantities and their partial derivatives wrt x = (r, b1, b2, delta):

  A = b1-delta                 dA = ( 0, 1, 0, -1)
  B = b2+delta                 dB = ( 0, 0, 1,  1)
  H = 2r sin(2b1-delta)        dH = ( 2 sin(2b1-dl), 4r cos(2b1-dl), 0, -2r cos(2b1-dl) )
  s = sqrt(1-r^2)              ds = ( -r/s, 0, 0, 0 )
  k  = r( sin b1 sinA + sin b2 sinB )        dk = (dk/dr, dk/db1, dk/db2, dk/ddl)
  k' = r(-sin b1 cosA + sin b2 cosB )        dk' analogously
  ON face-1 : e1 = r sinA/R,   phi1 = b1
  OFF face-2: Y = 2r sin b2 sinB,  X = H - 2r sin b2 cosB

For the off-face quantities we need X' = dX/ddelta and Y' = dY/ddelta; then
  Q  = X^2+Y^2,          dQ/dx   = 2X dX/dx + 2Y dY/dx
  e2 = sqrt(Q)/(2R),      de2/dx  = dQ/dx / (4 R sqrt(Q))
  phi2 = atan2(Y,X),      dphi2/dx = (X dY/dx - Y dX/dx)/Q
  dphi2/ddelta (= phi2')  = (X Y' - Y X')/Q, and its full partial derivative wrt x is
        d/dx [ (X Y'-Y X')/Q ] = [ (dX/dx Y' + X dY'/dx - dY/dx X' - Y dX'/dx) Q
                                   - (X Y'-Y X') dQ/dx ] / Q^2
  de2/ddelta (= e2') = (X X'+Y Y')/(2 R sqrt(Q)), and its partial wrt x likewise with the
  second-order product rule.

Everything below is generated from these identities with interval arithmetic, so each
partial is an enclosure over the box.  G = C0 + H k' + H' k + [on-face] + [off-face].
"""
import math, json, sys, time, heapq
from pathlib import Path
from mpmath import iv

iv.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
C0 = iv.mpf(f'{zJ[3]-zJ[1]:.9f}')
BE1 = iv.mpf(f'{-zJ[16]:.9f}'); GA1 = iv.mpf(f'{-zJ[78]:.9f}')
XX2 = iv.mpf(f'{zJ[3]-zJ[9]:.9f}')
BE2 = iv.mpf(f'{zJ[20]:.9f}'); GA2 = iv.mpf(f'{zJ[82]:.9f}')
RR = iv.mpf(19)/50
TWO = iv.mpf(2); ZERO = iv.mpf(0); ONE = iv.mpf(1)
THRESH = 0.15


def J(*xs):
    return list(xs)


def build(r, b1, b2, dl):
    """returns dict of quantities and their derivative vectors, or None if Q too small"""
    s = iv.sqrt(1-r*r)
    A = b1-dl; B = b2+dl
    sinA, cosA = iv.sin(A), iv.cos(A)
    sinB, cosB = iv.sin(B), iv.cos(B)
    sb1, cb1 = iv.sin(b1), iv.cos(b1)
    sb2, cb2 = iv.sin(b2), iv.cos(b2)
    H = TWO*r*iv.sin(2*b1-dl)
    dH = J(TWO*iv.sin(2*b1-dl), 4*r*iv.cos(2*b1-dl), ZERO, -TWO*r*iv.cos(2*b1-dl))
    k = r*(sb1*sinA+sb2*sinB)
    dk = J(sb1*sinA+sb2*sinB,
           r*(cb1*sinA+sb1*cosA),
           r*(cb2*sinB+sb2*cosB),
           r*(-sb1*cosA+sb2*cosB))
    kp = r*(-sb1*cosA+sb2*cosB)
    dkp = J(-sb1*cosA+sb2*cosB,
            r*(-cb1*cosA-sb1*sinA),
            r*(-cb2*cosB+sb2*sinB),
            r*(sb1*sinA+sb2*sinB))
    # ON face 1
    e1 = r*sinA/RR
    de1 = J(sinA/RR, -r*cosA/RR, ZERO, -r*cosA/RR)
    # OFF face 2
    Y = TWO*r*sb2*sinB
    X = H-TWO*r*sb2*cosB
    dY = J(TWO*sb2*sinB, ZERO,
           TWO*r*cb2*sinB+TWO*r*sb2*cosB,
           TWO*r*sb2*cosB)
    dX = J(dH[0]-TWO*sb2*cosB, dH[1],
           dH[2]-TWO*r*cb2*cosB+TWO*r*sb2*sinB,
           dH[3]+TWO*r*sb2*sinB)
    Q = X*X+Y*Y
    if Q.b < iv.mpf(1)/(50000**2):
        return None
    sq = iv.sqrt(Q)
    dQ = [TWO*X*dX[j]+TWO*Y*dY[j] for j in range(4)]
    e2 = sq/(TWO*RR)
    de2 = [dQ[j]/(TWO*sq)/(TWO*RR) for j in range(4)]
    phi = iv.atan2(Y, X)
    dphi = [(X*dY[j]-Y*dX[j])/Q for j in range(4)]
    return dict(s=s, A=A, B=B, sinA=sinA, cosA=cosA, sinB=sinB, cosB=cosB,
                H=H, dH=dH, k=k, dk=dk, kp=kp, dkp=dkp,
                e1=e1, de1=de1, e2=e2, de2=de2, phi=phi, dphi=dphi,
                X=X, Y=Y, dX=dX, dY=dY, Q=Q, dQ=dQ, sq=sq)


def G_and_grad(r, b1, b2, dl):
    """G and its exact four partial derivatives, as interval enclosures."""
    q = build(r, b1, b2, dl)
    if q is None:
        return None
    H, dH = q['H'], q['dH']
    k, dk = q['k'], q['dk']
    kp, dkp = q['kp'], q['dkp']
    e1, de1 = q['e1'], q['de1']
    e2, de2 = q['e2'], q['de2']
    phi, dphi = q['phi'], q['dphi']
    X, Y, dX, dY, Q, dQ, sq = q['X'], q['Y'], q['dX'], q['dY'], q['Q'], q['dQ'], q['sq']
    # G = C0 + H kp + H' k + BE1 e1^2 + GA1 e1  +  XX2 phi  +  BE2 e2^2 + GA2 e2
    # with H' = dH[3] (the delta-derivative of H) and k' = kp
    Hp = dH[3]
    G = C0+H*kp+Hp*k+BE1*e1*e1+GA1*e1+XX2*phi+BE2*e2*e2+GA2*e2
    # partials of G:  product rule on each term
    #   d(H kp)/dx = dH/dx * kp + H * dkp/dx
    #   d(Hp k)/dx = d(Hp)/dx * k + Hp * dk/dx     with d(Hp)/dx = d/dx dH[3]
    # d/dx (dH[3]) : H = 2r sin(2b1-dl) -> Hp = -2r cos(2b1-dl)
    Hpp = J(-TWO*iv.cos(2*b1-dl),          # d/dr
            -4*r*iv.sin(2*b1-dl),          # d/db1
            ZERO,                          # d/db2
            -TWO*r*iv.sin(2*b1-dl))        # d/ddelta
    out = []
    for j in range(4):
        t = (dH[j]*kp+H*dkp[j]) + (Hpp[j]*k+Hp*dk[j]) \
            + (BE1*TWO*e1*de1[j]+GA1*de1[j]) \
            + (XX2*dphi[j]) \
            + (BE2*TWO*e2*de2[j]+GA2*de2[j])
        out.append(t)
    return G, out[0], out[1], out[2], out[3]


def certify(budget=200000, rlo=.375, rhi=.38, blo=1.0, sub=4, thresh=THRESH):
    bhi = math.acos(rlo)
    def rng(lo, hi, n):
        return [(lo+(hi-lo)*i/n, lo+(hi-lo)*(i+1)/n) for i in range(n)]
    heap = []; seq = [0]
    def push(bx):
        heapq.heappush(heap, (0.0, seq[0], bx)); seq[0] += 1
    for r0, r1 in rng(rlo, rhi, sub):
        for b10, b11 in rng(blo, bhi, sub):
            for b20, b21 in rng(blo, bhi, sub):
                for d0, d1 in rng(-bhi, bhi, 2*sub):
                    push((r0, r1, b10, b11, b20, b21, d0, d1))
    st = dict(certified=0, infeasible=0, split=0, processed=0)
    worst = None; t0 = time.time()
    while heap and st['processed'] < budget:
        _, _, bx = heapq.heappop(heap)
        st['processed'] += 1
        r0, r1, b10, b11, b20, b21, d0, d1 = bx
        rc = iv.mpf(0.5*(r0+r1)); b1c = iv.mpf(0.5*(b10+b11))
        b2c = iv.mpf(0.5*(b20+b21)); dc = iv.mpf(0.5*(d0+d1))
        qc = build(rc, b1c, b2c, dc)
        if qc is None:
            st['infeasible'] += 1; continue
        Hc = qc['H']
        cap2 = TWO*rc*iv.sin(TWO*b2c+dc)
        beta = Hc*Hc-TWO*qc['s']*iv.cos(dc)*Hc+TWO*rc*(ONE-rc)
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
        if lo >= thresh:
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
        a, b = [(r0, r1), (b10, b11), (b20, b21), (d0, d1)][kq]
        m = 0.5*(a+b)
        for seg in ((a, m), (m, b)):
            nb = list(bx); nb[2*kq] = seg[0]; nb[2*kq+1] = seg[1]
            push(tuple(nb))
    return st, worst, time.time()-t0, len(heap)


if __name__ == '__main__':
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    sub = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    thr = float(sys.argv[3]) if len(sys.argv) > 3 else 0.15
    print(f'j=0 certificate (systematic Jacobian): budget={budget} grid={sub} thresh={thr}')
    st, worst, dt, left = certify(budget=budget, sub=sub, thresh=iv.mpf(str(thr)))
    print(f'processed {st["processed"]} in {dt:.1f}s; queue {left}')
    print(f'  certified={st["certified"]} infeasible={st["infeasible"]} split={st["split"]}')
    if worst:
        print(f'worst lower bound = {worst[0]:.6f}')
        bx = worst[1]
        print('   r=[%.6f,%.6f] b1=[%.6f,%.6f] b2=[%.6f,%.6f] d=[%.6f,%.6f]'
              % (bx[0], bx[1], bx[2], bx[3], bx[4], bx[5], bx[6], bx[7]))
    print('verdict:', 'CLOSED' if st['split'] == 0 and left == 0 else 'NOT CLOSED')
