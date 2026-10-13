"""cline2-coupled-factors R16j: interval certificate for the j=0 branch.

Claim attempted:  for every admissible point of the face-1 branch
    H = 2r sin(2 b1 - delta),   delta in [-b2, b1],
with  r in [.375,.38],  b1,b2 in [1, acos r],  and the box constraints
    (C2)  H <= 2 r sin(2 b2 + delta)             [inside the face-2 cap]
    (N)   H^2 - 2 s cos(delta) H + 2 r (1-r) <= 0    [hub inside the norm circle]
one has  dV/ddelta >= 0.15.

Everything is evaluated with mpmath.iv at 30 dps.  The derivative is assembled from
rigorous interval enclosures of each mathematically independent piece, so the interval
arithmetic does not have to fight the dependency between H and H'.

V(delta) = (z3-z1) delta + H r (sin b1 sin A + sin b2 sin B)
           + a1 phi1 + beta1 e1^2 + gamma1 e1
           + a2 phi2 + beta2 e2^2 + gamma2 e2
A = b1-delta, B = b2+delta, H = 2r sin(2b1-delta), s = sqrt(1-r^2), R = 19/50
ON face 1 : e1 = r sin(A)/R,  phi1 = b1
OFF face 2: Y = 2r sin b2 sin B,  X = H - 2r sin b2 cos B,  Q = X^2+Y^2,
            e2 = sqrt(Q)/(2R),  phi2 = atan2(Y,X)
"""
import math, json, sys, time, heapq
from pathlib import Path
from mpmath import iv

iv.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z3_Z1 = iv.mpf(f'{zJ[3]-zJ[1]:.9f}')
A1 = iv.mpf(f'{zJ[1]-zJ[9]:.9f}')
A2 = iv.mpf(f'{zJ[3]-zJ[9]:.9f}')
B1 = iv.mpf(f'{-zJ[16]:.9f}')
G1 = iv.mpf(f'{-zJ[78]:.9f}')
B2 = iv.mpf(f'{zJ[20]:.9f}')
G2 = iv.mpf(f'{zJ[82]:.9f}')
R = iv.mpf(19)/50
PI = iv.pi
TARGET = iv.mpf('.15')


def evaluate(rr, b1, b2, dl):
    """returns (dv, status) with status in {'certified','infeasible','split'}"""
    s = iv.sqrt(1-rr*rr)
    A = b1-dl
    B = b2+dl
    # branch height (exact) and derivative
    H = 2*rr*iv.sin(2*b1-dl)
    dH = -2*rr*iv.cos(2*b1-dl)
    # ---- admissibility ----
    cap2 = 2*rr*iv.sin(2*b2+dl)
    a2res = cap2-H                      # >= 0 required
    beta = H*H-2*s*iv.cos(dl)*H+2*rr*(1-rr)   # <= 0 required
    Hall = H
    # hub must lie outside the inner disk and inside the caps; H>0 is implied by cap2>=0
    if a2res.b < 0 or beta.a > 0:
        return None, 'infeasible'
    if a2res.a < 0 or beta.b > 0:
        return None, 'split'
    # ---- ON-face 1 ----
    e1 = rr*iv.sin(A)/R
    de1 = -rr*iv.cos(A)/R
    # ---- OFF-face 2 ----
    Y = 2*rr*iv.sin(b2)*iv.sin(B)
    X = H-2*rr*iv.sin(b2)*iv.cos(B)
    Q = X*X+Y*Y
    if Q.b < iv.mpf(1)/(50000**2) or Q.a > 4*rr.b*rr.b:
        return None, 'infeasible'
    sq = iv.sqrt(Q)
    phi2 = iv.atan2(Y, X)
    dY = 2*rr*iv.sin(b2)*iv.cos(B)
    dX = dH+2*rr*iv.sin(b2)*iv.sin(B)
    dQ = 2*X*dX+2*Y*dY
    de2 = dQ/(2*sq)/(2*R)
    dphi2 = (X*dY-Y*dX)/Q
    # ---- derivative assembly ----
    kprime = rr*(-iv.sin(b1)*iv.cos(A)+iv.sin(b2)*iv.cos(B))
    k = rr*(iv.sin(b1)*iv.sin(A)+iv.sin(b2)*iv.sin(B))
    dv = Z3_Z1 + Hall*kprime + dH*k + B1*2*e1*de1 + G1*de1 \
        + A2*dphi2 + B2*2*(iv.sqrt(Q)/(2*R))*de2 + G2*de2
    if A1 != 0:
        dv += A1*iv.mpf(0)      # phi1 = b1 has zero delta-derivative
    return dv, ('certified' if dv.a >= TARGET.a else 'split')


def certify(budget=200000, rlo=.375, rhi=.38, blo=1.0):
    bhi = math.acos(rlo)   # upper bound on acos(r) for r >= rlo
    box = [(rlo, rhi), (blo, bhi), (blo, bhi), (-bhi, bhi)]
    # delta domain: [max(-b2), min(b1)] -- use the sound box [-bhi, bhi]
    uid = 0
    heap = []
    stats = dict(infeasible=0, certified=0, split=0, count=0)
    worst = None
    t0 = time.time()
    cnt = [0]

    def push(bx, prio):
        c = cnt[0]
        cnt[0] = c+1
        heapq.heappush(heap, (prio, c, bx))
    push(box, 0.0)
    while heap and stats['count'] < budget:
        prio, _, bx = heapq.heappop(heap)
        r = iv.mpf([bx[0][0], bx[0][1]])
        b1 = iv.mpf([bx[1][0], bx[1][1]])
        b2 = iv.mpf([bx[2][0], bx[2][1]])
        dl = iv.mpf([bx[3][0], bx[3][1]])
        stats['count'] += 1
        try:
            dv, st = evaluate(r, b1, b2, dl)
        except (ValueError, ZeroDivisionError):
            st = 'split'; dv = None
        if st == 'infeasible':
            stats['infeasible'] += 1
            continue
        if st == 'certified':
            stats['certified'] += 1
            lo = float(dv.a)
            if worst is None or lo < worst[0]:
                worst = (lo, bx)
            continue
        if st == 'split' and dv is not None:
            lo = float(dv.a)
            if worst is None or lo < worst[0]:
                worst = (lo, bx)
        stats['split'] += 1
        # subdivide the widest scaled dimension
        scales = [rhi-rlo, bhi-blo, bhi-blo, 2*bhi]
        k = max(range(4), key=lambda i: (bx[i][1]-bx[i][0])/scales[i])
        l, h = bx[k]
        m = 0.5*(l+h)
        for seg in ((l, m), (m, h)):
            nb = list(bx); nb[k] = seg
            push(tuple(nb), -(seg[1]-seg[0]))
    return stats, worst, time.time()-t0


if __name__ == '__main__':
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    print(f'j=0 interval certificate attempt, budget={budget} boxes, dps=30')
    print(f'target: dV/ddelta >= 0.15 on the admissible set')
    stats, worst, dt = certify(budget=budget)
    print(f'\nboxes processed      : {stats["count"]}')
    print(f'  certified          : {stats["certified"]}')
    print(f'  infeasible         : {stats["infeasible"]}')
    print(f'  split (unresolved) : {stats["split"]}')
    print(f'elapsed              : {dt:.1f}s')
    if worst:
        print(f'\nsmallest derivative lower bound seen: {worst[0]:.6f}')
        bx = worst[1]
        print('   at box r=[%.6f,%.6f] b1=[%.6f,%.6f] b2=[%.6f,%.6f] delta=[%.6f,%.6f]'
              % (bx[0][0], bx[0][1], bx[1][0], bx[1][1], bx[2][0], bx[2][1],
                 bx[3][0], bx[3][1]))
    print('\nverdict:', 'CERTIFIED' if stats['split'] == 0 else
          'NOT closed within budget (split boxes remain)')
