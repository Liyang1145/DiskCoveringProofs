from mpmath import iv, mp
import json

iv.dps = 25
row = json.load(open('shared_moment_dense_0_4.json'))
z = [iv.mpf('%.9f' % v) for v in row['z']]
side, rr, kap, lam, eta, lin = 11, 32, 50, 71, 72, 73
R0 = iv.mpf(19)/50

print("z_lam =", z[lam], " z_eta =", z[eta])
print("sign(lambda) =", "NEG" if z[lam].b < 0 else ("POS" if z[lam].a > 0 else "zero"))
print()


def ring_atom(Rt, a, u, v, C):
    R2t = Rt*Rt
    q = (u-v)**2 + 4*u*v*iv.sin(a/2)**2
    w = 2*iv.atan2(Rt*iv.sqrt(q), iv.sqrt(1-R2t*q/4))
    return R2t*u*v*iv.sin(a)/2 + (w - iv.sin(w))/2 + C*w


print("IS THE RING ATOM MONOTONE IN R? scan a grid, compare value at t=1 vs t=0.5")
bad = 0; n = 0; worst = None
for ia in range(1, 12):
    a = iv.mpf(ia)*iv.pi/12
    for iu in [0, 1, 2, 3]:
        u = iv.mpf(iu)/3
        for ivv in [0, 1, 2, 3]:
            v = iv.mpf(ivv)/3
            hi = ring_atom(R0, a, u, v, z[lam]).b
            lo = ring_atom(R0/2, a, u, v, z[lam]).b
            n += 1
            d = lo - hi
            if d > 0:  # value at smaller R exceeds value at R0 -> NOT monotone
                bad += 1
                if worst is None or d > worst[0]:
                    worst = (d, float(a), float(u), float(v), float(hi), float(lo))
print("   samples", n, " monoticity violations", bad)
if worst:
    print("   worst violation: d=%.3e at a=%.3f u=%.2f v=%.2f  (S(R0)=%.6f, S(R0/2)=%.6f)"
          % worst)

print()
print("same test separating the cases lambda<0 contributions:")
C0 = z[lam]
for (a, u, v) in [(iv.pi, iv.mpf(1), iv.mpf(1)), (iv.mpf(2), iv.mpf(1), iv.mpf(1)),
                  (iv.mpf(1), iv.mpf('0.9'), iv.mpf('0.8'))]:
    S1 = ring_atom(R0, a, u, v, C0).b
    S2 = ring_atom(R0/2, a, u, v, C0).b
    print("   a=%.3f u=%.2f v=%.2f : S(R0)=%.9f  S(R0/2)=%.9f  direction=%s"
          % (float(a), float(u), float(v), float(S1), float(S2),
             "INCREASING" if S2 < S1 else "DECREASING"))
