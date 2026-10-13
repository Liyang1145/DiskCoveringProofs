from mpmath import iv, mp
import json

iv.dps = 25
row = json.load(open('shared_moment_dense_0_4.json'))
z = [iv.mpf('%.9f' % v) for v in row['z']]
R = iv.mpf(19)/50
R2 = R*R
side, rr, kap, lam, eta, lin = 11, 32, 50, 71, 72, 73


def ring_atom(Rt, a, u, v, C):
    R2t = Rt*Rt
    q = (u-v)**2 + 4*u*v*iv.sin(a/2)**2
    w = 2*iv.atan2(Rt*iv.sqrt(q), iv.sqrt(1-R2t*q/4))
    return R2t*u*v*iv.sin(a)/2 + (w - iv.sin(w))/2 + C*w


print("ring atom at degenerate / boundary points (R = 19/50):")
C0 = z[lam]
for (an, a, u, v) in [('a=pi,u=v=1', iv.pi, iv.mpf(1), iv.mpf(1)),
                      ('a=0,u=v=1', iv.mpf(0), iv.mpf(1), iv.mpf(1)),
                      ('a=pi,u=v=0', iv.pi, iv.mpf(0), iv.mpf(0)),
                      ('a=0,u=0,v=1', iv.mpf(0), iv.mpf(0), iv.mpf(1))]:
    S = ring_atom(R, a, u, v, C0)
    print('   %-14s -> S in [%s, %s]' % (an, mp.nstr(S.a, 10), mp.nstr(S.b, 10)))

print()
print("ring atom as R = t*(19/50) varies (a=1.2, u=0.9, v=0.8, C=lambda):")
for t in ['1', '0.5', '0.25', '0.1']:
    S = ring_atom((iv.mpf(19)/50)*iv.mpf(t), iv.mpf('1.2'), iv.mpf('0.9'), iv.mpf('0.8'), C0)
    print('   t=%-5s -> %s' % (t, mp.nstr(S.b, 12)))

print()
print("face atom as R varies (theta=(1.0,0.9,pi-1.9)):")
t_ = [iv.mpf('1.0'), iv.mpf('0.9'), iv.pi-iv.mpf('1.9')]
for t in ['1', '0.5', '0.25']:
    Rt = (iv.mpf(19)/50)*iv.mpf(t); R2t = Rt*Rt
    val = 2*R2t*iv.sin(t_[0])*iv.sin(t_[1])*iv.sin(t_[2])
    print('   t=%-5s -> R2-part = %s' % (t, mp.nstr(val.b, 14)))

print()
print("constant term pieces vs 2R:")
for t in ['1', '0.5', '0.25']:
    Rt = (iv.mpf(19)/50)*iv.mpf(t)
    two_R = 2*Rt
    print('   t=%-5s : 2R = %s ; 2R - 2asin(2R) = %s'
          % (t, mp.nstr(two_R.b, 8), mp.nstr((two_R - 2*iv.atan2(two_R, iv.sqrt(1-two_R*two_R))).b, 8)))
