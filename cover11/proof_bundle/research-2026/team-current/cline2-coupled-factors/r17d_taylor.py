"""cline2-coupled-factors R17d: settle the W'' disagreement by exact Taylor extraction."""
import math, json, sys
from pathlib import Path
from mpmath import mp

mp.dps = 60
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z = {i: mp.mpf(f'{zJ[i]:.9f}') for i in range(len(zJ))}
R = mp.mpf(19)/50


def consts(j):
    return ((Z[1], Z[112], Z[34], Z[96]) if j == 0 else (Z[3], Z[115], Z[39], Z[101]))


def Wval(r, b, w, j):
    mu, h, d, l = consts(j)
    s = mp.sqrt(1-r*r); ph = mp.asin(r)
    x0 = 2*b-mp.pi/2+ph
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    cn = 1+r*r-2*r*mp.cos(x0)
    q = 1+cn-2*p
    a = mp.atan2(x, 1-p)
    u = mp.sqrt(q)/R
    return -r*s*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+x/2+(mu+h)*a-d*u*u-l*u


def taylor2(r, b, w0, j, deg=6):
    """coefficients of the Taylor expansion of W about w0, via exact interpolation"""
    xs = [w0+mp.mpf(k)*mp.mpf('0.01') for k in range(-deg//2, deg//2+1)]
    ys = [Wval(r, b, x, j) for x in xs]
    # Newton/Vandermonde solve at high precision
    n = len(xs)
    A = mp.matrix(n, n)
    rhs = mp.matrix(n, 1)
    for i in range(n):
        for k in range(n):
            A[i, k] = (xs[i]-w0)**k
        rhs[i] = ys[i]
    c = mp.lu_solve(A, rhs)
    return [c[k] for k in range(n)]


print('=== Taylor coefficients about a test point vs the closed form ===')
cases = [(0, mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')),
         (0, mp.mpf('0.379'), mp.mpf('0.95'), mp.mpf('0.1679')),
         (1, mp.mpf('0.37999'), mp.mpf('1.19'), mp.mpf('0.35'))]
for (j, r, b, w0) in cases:
    c = taylor2(r, b, w0, j)
    mu, h, d, l = consts(j)
    print(f'  j={j} r={float(r)} b={float(b)} w0={float(w0)}')
    print(f'     W(w0)   = {mp.nstr(c[0],18)}')
    print(f"     W'(w0)  = {mp.nstr(c[1],18)}")
    print(f"     W''(w0) = {mp.nstr(c[2]*2,18)}      <- from Taylor")
    print(f"     W'''(w0)= {mp.nstr(c[3]*6,18)}")
    print(f"     W''''   = {mp.nstr(c[4]*24,18)}")
    # now the individual pieces, differentiated ANALLYTICALLY and also by Taylor
    s = mp.sqrt(1-r*r); ph = mp.asin(r)
    x0 = 2*b-mp.pi/2+ph
    # p, x and their derivatives wrt w
    p = mp.cos(w0)-r*mp.cos(x0+w0)
    p1 = -mp.sin(w0)+r*mp.sin(x0+w0)
    p2 = -mp.cos(w0)+r*mp.cos(x0+w0)
    x = -mp.sin(w0)+r*mp.sin(x0+w0)
    x1 = -mp.cos(w0)+r*mp.cos(x0+w0)
    x2 = mp.sin(w0)-r*mp.sin(x0+w0)
    cn = 1+r*r-2*r*mp.cos(x0)
    q = 1+cn-2*p
    sq = mp.sqrt(q)
    u = sq/R
    u1 = -p1/(R*sq)
    u2 = -p2/(R*sq)+p1*p1/(R*q*sq)
    # a = atan2(x, 1-p): derivatives by Taylor of a alone
    def aval(wv):
        pp = mp.cos(wv)-r*mp.cos(x0+wv)
        xx = -mp.sin(wv)+r*mp.sin(x0+wv)
        return mp.atan2(xx, 1-pp)
    xs = [w0+mp.mpf(k)*mp.mpf('0.01') for k in range(-3, 4)]
    ys = [aval(x) for x in xs]
    A = mp.matrix(7, 7); rhs = mp.matrix(7, 1)
    for i in range(7):
        for k in range(7):
            A[i, k] = (xs[i]-w0)**k
        rhs[i] = ys[i]
    ca = mp.lu_solve(A, rhs)
    a2_taylor = ca[2]*2
    a2_closed = (x2*(1-p)-x*(-p2))/((x*x+(1-p)**2)) \
        - 2*(x*x1-(1-p)*(-p1))*2*(x*x1+(1-p)*(-p1))/((x*x+(1-p)**2)**2)
    print(f'     pieces: x\'\'/2={mp.nstr(x2/2,14)}  u\'={mp.nstr(u1,12)}  '
          f'u\'\'={mp.nstr(u2,12)}')
    print(f'       a\'\' Taylor={mp.nstr(a2_taylor,14)}   a\'\' closed={mp.nstr(a2_closed,14)}'
          f'   diff={mp.nstr(abs(a2_taylor-a2_closed),4)}')
    cl = x2/2+(mu+h)*a2_closed-2*d*(u1*u1+u*u2)-l*u2
    print(f'     closed W\'\'={mp.nstr(cl,16)}   Taylor W\'\'={mp.nstr(c[2]*2,16)}   '
          f'diff={mp.nstr(abs(cl-c[2]*2),4)}')
    print()
