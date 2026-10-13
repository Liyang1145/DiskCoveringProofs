"""
Independent audit of the exact local envelope A(beta) from
lead/SHARED-FACE-RADIUS-THEOREM.md.

    A(beta) = sum_i sin beta_i                    if Bsum <= pi
            = x0(beta) * sum_i sin beta_i         if pi < Bsum < 2pi
    a = sum_i sin beta_i,  b = sum_{i<j} sin(beta_i+beta_j),  c = sin(Bsum),
    x0 = largest root in (0,1] of  a x^2 - b x + c = 0
       = (b + sqrt(b^2-4ac))/(2a)                  (c<0)
       = 1                                          (c>=0)

Reduction used everywhere below (equivalent to H(x0)=pi):
    H(x) = sum_i atan2(sin beta_i, x - cos beta_i)   strictly decreasing in x
    H(1) = (3pi - Bsum)/2  <=  pi   <=>   Bsum >= pi
so on Bsum >= pi the constraint H(x)>=pi is exactly x <= x0 and
A = max_{x<=x0} x*a = x0*a.  On Bsum <= pi the constraint is vacuous and A = a.

Module contents: exact/numeric envelope, self-test, analytic-slope checks,
direction+scale ray reduction, and a global maximization over the domain.
"""
import numpy as np

PI = float(np.pi)


def as_beta(beta):
    beta = np.asarray(beta, float)
    if beta.ndim == 1:
        beta = beta.reshape(3, 1)
    return beta


def coefs(beta):
    """a,b,c with the exact 3-angle identity
       b = sum_{i<j} sin(b_i+b_j) = (sum cos)(sum sin) - (sum sin)(sum cos).
    (Self-tested against the direct formula.)"""
    beta = as_beta(beta)
    s = np.sin(beta)
    w = np.cos(beta)
    S = s.sum(axis=0)
    a = S
    b = w.sum(axis=0) * S - S * w.sum(axis=0)
    c = np.sin(beta.sum(axis=0))
    return a, b, c


def coefs_direct(beta):
    beta = as_beta(beta)
    s = np.sin(beta)
    a = s.sum(axis=0)
    b = (np.sin(beta[0] + beta[1]) + np.sin(beta[0] + beta[2])
         + np.sin(beta[1] + beta[2]))
    c = np.sin(beta.sum(axis=0))
    return a, b, c


def H(beta, x):
    """H(x) = sum_i atan2(sin beta_i, x - cos beta_i),  vectorized."""
    beta = as_beta(beta)
    return np.arctan2(np.sin(beta), x - np.cos(beta)).sum(axis=0)


def envelope(beta, return_extra=False):
    """A(beta) for 0 < beta_i < pi, beta shaped (3,N)."""
    beta = as_beta(beta)
    a, b, c = coefs(beta)
    disc = np.maximum(b * b - 4.0 * a * c, 0.0)
    x0 = np.where(c < 0, (b + np.sqrt(disc)) / (2.0 * a), 1.0)
    A = x0 * a
    if return_extra:
        return A, x0, a, b, c
    return A


def envelope_scalar(beta):
    return float(envelope(np.asarray(beta, float).reshape(3, 1))[0])


def x0_scalar(beta):
    return float(envelope(np.asarray(beta, float).reshape(3, 1),
                          return_extra=True)[1][0])


# ------------------------------------------------------------------ self test
def self_test():
    rng = np.random.default_rng(20260218)
    out = {}
    beta = rng.uniform(0.02, PI - 0.02, size=(3, 4000))
    a1, b1, c1 = coefs(beta)
    a2, b2, c2 = coefs_direct(beta)
    out['pairsum_identity_max_res'] = float(max(np.max(np.abs(a1 - a2)),
                                                np.max(np.abs(b1 - b2)),
                                                np.max(np.abs(c1 - c2))))
    lhs = a2 - b2 + c2
    rhs = 4 * np.prod(np.sin(beta / 2), axis=0)
    out['abc_factor_identity_res'] = float(np.max(np.abs(lhs - rhs)))
    A, x0, a, b, c = envelope(beta, return_extra=True)
    m2 = c < 0
    m1 = ~m2
    # 1. branch consistency: c<0 <=> Bsum>pi
    out['c_sign_matches_Bsum'] = bool(((beta.sum(axis=0) > PI) == m2).all())
    # 2. x0 truly solves H(x0)=pi on branch 2
    out['H_at_x0_minus_pi'] = (float(np.abs(H(beta[:, m2], x0[m2]) - PI).max())
                               if m2.any() else 0.0)
    # 3. H(x0-eps) > pi  (x0 is the crossing)
    if m2.any():
        xm = np.maximum(x0[m2] * (1 - 1e-7) - 1e-12, 1e-300)
        out['H_just_below_x0_gt_pi'] = bool((H(beta[:, m2], xm) > PI).all())
    # 4. branch 1: A = a, x0 = 1, H(1) >= pi
    out['branch1_gap'] = float(np.max(np.abs(A[m1] - a[m1]))) if m1.any() else 0.0
    out['branch1_flat_x0'] = float(np.max(np.abs(x0[m1] - 1.0))) if m1.any() else 0.0
    out['branch1_min_H1_minus_pi'] = (float((H(beta[:, m1], 1.0) - PI).min())
                                      if m1.any() else 0.0)
    # 5. product identity  pi_i (x - cos b_i + i sin b_i) real/imag check
    z = (x0 - np.cos(beta)).astype(complex) + 1j * np.sin(beta)
    P = z[0] * z[1] * z[2]
    out['poly_ident_res'] = float(np.max(np.abs(np.imag(P) - (a * x0 ** 2 - b * x0 + c))))
    # 6. calibration: lead-reported candidate slack-face angle set
    cand = np.array([0.9223829833, 1.1925065472, 1.1925065472])
    Ac, x0c, ac, bc, cc = envelope(cand, return_extra=True)
    out['cand_sum'] = float(cand.sum())
    out['cand_a'] = float(ac)
    out['cand_b'] = float(bc)
    out['cand_c'] = float(cc)
    out['cand_x0'] = float(x0c)
    out['cand_A'] = float(Ac)
    out['cand_H_at_x0'] = float(H(cand, float(x0c)))
    out['cand_H_plus_pi_c1'] = float(H(cand, 1.1925065472 / (2 * PI / 3)))
    return out


# --------------------------------------------------------- diagonal slice (t,t,t)
def diag_checks():
    """Closed form on the diagonal (t,t,t), t in [pi/3, 2pi/3]:
         x0(t) = cos t + sin t/sqrt(3),   A(t) = 3 sin t cos t + sqrt3 sin^2 t,
         A'(t)  = 3cos2t + sqrt3 sin2t = 2 cos t * sqrt3 cos(t-pi/3),
         A''(t) = -6 sin2t + 2 sqrt3 cos2t.
    """
    res = {}
    ts = np.linspace(PI / 3, 2 * PI / 3, 1000001)
    beta = np.vstack([ts, ts, ts])
    A, x0, a, b, c = envelope(beta, return_extra=True)
    x0cf = np.cos(ts) + np.sin(ts) / np.sqrt(3.0)
    Acf = 3 * np.sin(ts) * np.cos(ts) + np.sqrt(3.0) * np.sin(ts) ** 2
    res['x0_closedform_maxerr'] = float(np.max(np.abs(x0 - x0cf)))
    res['A_closedform_maxerr'] = float(np.max(np.abs(A - Acf)))
    res['A_max_on_diag'] = float(A.max())
    res['argmax_t'] = float(ts[int(np.argmax(A))])
    d1 = 3 * np.cos(2 * ts) + np.sqrt(3.0) * np.sin(2 * ts)
    res['d1_min_on_interval'] = float(d1.min())
    res['d1_at_pi2'] = float(3 * np.cos(PI) + np.sqrt(3.0) * np.sin(PI))
    d2 = -6 * np.sin(2 * ts) + 2 * np.sqrt(3.0) * np.cos(2 * ts)
    res['d2_at_pi3'] = float(-6 * np.sin(2 * PI / 3) + 2 * np.sqrt(3.0) * np.cos(2 * PI / 3))
    res['d2_max_on_interval'] = float(d2.max())
    res['d2_min_on_interval'] = float(d2.min())
    # explicit convexity witnesses
    pts = [(1.0, 1.3), (0.95, 1.25), (1.0, 1.2)]
    wit = []
    for t1, t2 in pts:
        A1 = envelope_scalar([t1, t1, t1])
        A2 = envelope_scalar([t2, t2, t2])
        tm = (t1 + t2) / 2
        Am = envelope_scalar([tm, tm, tm])
        wit.append(dict(t1=t1, t2=t2, A1=A1, A2=A2, mid=Am,
                        chord_mid=(A1 + A2) / 2, excess=Am - (A1 + A2) / 2))
    res['convexity_witnesses'] = wit
    # junction-adjacent slope difference (kink check)
    for t in [PI / 3 + 1e-6, PI / 3 + 1e-3]:
        res[f'd1_at_{t:.6f}'] = float(3 * np.cos(2 * t) + np.sqrt(3.0) * np.sin(2 * t))
    return res


# ------------------------------------------- direction + scale ray reduction
def ray_profile(d):
    """For a direction d (positive orthant, sum(d)>0), describe A along r*d,
    0<r<2pi/sum(d).

    Let s=sin(d), a=sum s, Q=sum cos d,
        K(x) = a x^2 - b x + c  with  Q(x)=sum cos(r d_i),
    and K(1) = a - Q = H(1,d)-pi indicator:  K(1)>0 <=> sum(d)<pi.
      sum(d) <= pi : x=1 on the whole feasible r-interval,  A(r d)=r*a, sup at
                     r=pi/sum(d)  (value pi*a/sum(d)).
      sum(d) >  pi : x(r)=min(r*x0,1) with
                     x0   = (K1+sqrt(K1^2+4a))/(2a),
                     r*   = -x0*Q/K1,          A(r d)= r*x0*a  for r<=r*,
                     then x=1 and A = r*a = a (constant in r).
    Returns dict with the sup and where it occurs.
    """
    d = np.asarray(d, float)
    sd = d.sum()
    s = np.sin(d)
    a = s.sum()
    Q = np.cos(d).sum()
    K1 = a - Q
    out = dict(d=d, sd=sd, a=a, Q=Q, K1=K1, r_feas=2 * PI / sd)
    if K1 > 0:                       # sum(d) < pi  -> x capped at 1
        r = PI / sd
        out.update(regime='I(x=1)', r=r, sum_beta=PI, value=r * a, x=1.0)
        return out
    if K1 == 0:                      # sum(d) == pi exactly
        r = PI / sd
        out.update(regime='junction', r=r, sum_beta=PI, value=r * a, x=1.0)
        return out
    x0 = (K1 + np.sqrt(K1 * K1 + 4 * a)) / (2 * a)
    r_star = -x0 * Q / K1
    r_feas = 2 * PI / sd
    if r_star < r_feas:
        out.update(regime='II(x<1)', r=r_star, sum_beta=r_star * sd,
                   value=r_star * x0 * a, x=x0)
    else:
        r = r_feas
        out.update(regime='II(x=1)', r=r, sum_beta=2 * PI, value=r * a, x=1.0)
    return out


def ray_sup(d):
    return ray_profile(d)['value']


def coord_ascent(d0, sweeps=2000, step0=0.3):
    """Coordinate ascent maximizing ray_sup over directions d>0.

    NOTE: ray_sup itself is a closed-form smooth-ish function of d; the
    maximizer of ray_sup over the direction simplex is *not* automatically a
    local max of A (A is homogeneous of degree 1), see notes: the junction
    directions are handled separately by the exact junction analysis.
    """
    d = np.maximum(np.asarray(d0, float), 1e-9)
    best = ray_sup(d)
    step = step0
    for _ in range(sweeps):
        improved = False
        for i in range(3):
            for sgn in (1.0, -1.0):
                cand = d.copy()
                cand[i] = max(cand[i] + sgn * step, 1e-9)
                val = ray_sup(cand)
                if val > best * (1 + 1e-15):
                    best, d = val, cand
                    improved = True
        if not improved:
            step *= 0.5
            if step < 1e-13:
                break
    return best, d


def search_directions(seed=12345, n_restart=150, sweeps=1500):
    rng = np.random.default_rng(seed)
    starts = [np.array([PI / 3] * 3), np.array([PI / 2] * 3),
              np.array([2 * PI / 3 - 1e-9] * 3), np.array([2.0, 0.57, 0.57]),
              np.array([0.57, 2.0, 0.57]), np.array([0.57, 0.57, 2.0]),
              np.array([PI - 1e-9, 1e-9, 1e-9]), np.array([1e-9, PI - 1e-9, 1e-9])]
    best = -1.0
    arg = None
    for s in starts:
        v, a_ = coord_ascent(s, sweeps=sweeps)
        if v > best:
            best, arg = v, a_
    for _ in range(n_restart):
        u = rng.dirichlet(np.ones(3) * 2.5) * PI * rng.uniform(0.02, 1.1)
        v, a_ = coord_ascent(u, sweeps=sweeps)
        if v > best:
            best, arg = v, a_
    return best, arg


# ------------------------------------------------- global grid+refine on A
def grid_scan(ns=140, nu=140, seed=3):
    """Uniform scan of the domain (0,pi)^3 with sum<2pi, plus a scan of the
    junction sum=pi.  Cheap because H(x) uses one vectorized evaluation."""
    rng = np.random.default_rng(seed)
    # random Monte Carlo for the maximum of A
    best_mc = -1.0
    arg_mc = None
    for _ in range(40):
        beta = rng.dirichlet(np.ones(3)) * 2 * PI * 0.999
        beta = np.clip(beta, 1e-9, PI - 1e-9)
        v = envelope_scalar(beta)
        if v > best_mc:
            best_mc, arg_mc = v, beta
    # junction surface scan: all three equal? no - scan the 2D triangle sum=pi
    us = np.linspace(1e-6, PI - 1e-6, ns)
    best_j = -1.0
    arg_j = None
    B1 = us
    B2 = us
    M1, M2 = np.meshgrid(B1, B2, indexing='ij')
    ok = (M1 + M2) < PI
    B3 = PI - M1 - M2
    beta = np.vstack([M1[ok], M2[ok], B3[ok]])
    v = envelope(beta)
    i = int(np.argmax(v))
    best_j = float(v[i])
    arg_j = beta[:, i]
    return dict(mc_best=best_mc, mc_arg=arg_mc, junction_best=best_j,
                junction_arg=arg_j)
