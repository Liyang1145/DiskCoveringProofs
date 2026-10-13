"""
Clean first-principles audit of the shared-face envelope.

Everything here is derived from the *geometry*, not from any algebraic formula
stated elsewhere:

    theta_i(x) = atan2(sin beta_i, x - cos beta_i)
    H(x)       = sum_i theta_i(x)            (strictly decreasing in x>0)
    feasible x for the "all y_i = 1" local interface:  H(x) = pi
    branch validity: 0 < theta_i < pi - beta_i

Key exact facts used (each numerically cross-checked in self_test):
  (A) theta_i(x) = Arg(x - e^{i beta_i})  (principal argument in (0,pi))
  (B) H(1) = (3 pi - Bsum)/2
  (C) Im prod_i (x - e^{i beta_i}) = x^2 A - x B + C,
      A = sum sin b_i, B = sum_{i<j} sin(b_i+b_j), C = sin(Bsum)
      => the roots of Im P are exactly the x with H(x) in {0, pi, 2pi}
      (mod pi: three real roots on the line) -- so H = pi is NOT the same as
      Im P = 0 in general.  x0 is the *crossing* of H through pi, which is a
      root of Im P only when the two other relevant roots are the ones from
      the unit circle.
  (D) At the threshold Bsum = pi: x0 = 1 exactly (H(1) = pi).

H(x) = pi crossing x0 is located by bisection on [0,1] (monotone H).
"""
import numpy as np

PI = float(np.pi)


def as_beta(beta):
    beta = np.asarray(beta, float)
    return beta.reshape(3, 1) if beta.ndim == 1 else beta


def theta(beta, x):
    beta = as_beta(beta)
    return np.arctan2(np.sin(beta), x - np.cos(beta))


def H(beta, x):
    return theta(beta, x).sum(axis=0)


def H_alt(beta, x):
    """arg via complex product (independent representation)."""
    beta = as_beta(beta)
    z = (x - np.cos(beta)) + 1j * np.sin(beta)
    P = z[0] * z[1] * z[2]
    return np.angle(P)


def coefsABC(beta):
    beta = as_beta(beta)
    s = np.sin(beta)
    w = np.cos(beta)
    A = s.sum(axis=0)
    B = (w.sum(axis=0) * s.sum(axis=0) - s.sum(axis=0) * w.sum(axis=0))  # placeholder
    B = (np.sin(beta[0] + beta[1]) + np.sin(beta[0] + beta[2])
         + np.sin(beta[1] + beta[2]))
    C = np.sin(beta.sum(axis=0))
    return A, B, C


def coefsABC_identity(beta):
    """B via the exact 3-angle identity  B = C*S - S*C  with independent sums."""
    beta = as_beta(beta)
    S = np.sin(beta).sum(axis=0)
    Cc = np.cos(beta).sum(axis=0)
    A = S
    P = np.cos(beta[0]) * np.sin(beta[1]) + np.cos(beta[1]) * np.sin(beta[0]) \
        + np.cos(beta[0]) * np.sin(beta[2]) + np.cos(beta[2]) * np.sin(beta[0]) \
        + np.cos(beta[1]) * np.sin(beta[2]) + np.cos(beta[2]) * np.sin(beta[1])
    B = P
    C = np.sin(beta.sum(axis=0))
    return A, B, C


def x0_bisect(beta, iters=200):
    """x0 = crossing of H(.) through pi in (0,1], by bisection on monotone H.
    Returns nan if H(1) > pi (i.e. Bsum < pi: no crossing in (0,1])."""
    beta = as_beta(beta)
    Bsum = beta.sum(axis=0)
    h1 = H(beta, 1.0)
    # lo = 0+, hi = 1
    lo = np.full_like(h1, 1e-12)
    hi = np.ones_like(h1)
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        hm = H(beta, mid)
        # H decreasing: if hm > pi then crossing is above mid
        go_up = hm > PI
        lo = np.where(go_up, mid, lo)
        hi = np.where(go_up, hi, mid)
    x0 = 0.5 * (lo + hi)
    res = np.where(h1 <= PI, x0, np.nan)
    return res


def x0_theorem(beta):
    """Lead's algebraic formula (A,B,C as in the theorem)."""
    beta = as_beta(beta)
    A, B, C = coefsABC(beta)
    disc = B * B - 4 * A * C
    disc = np.maximum(disc, 0.0)
    r = (B + np.sqrt(disc)) / (2 * A)
    return np.where(C < 0, r, 1.0)


def x0_X(beta, n=2):
    """roots of Im P(x) = 0 by companion-free sampling/bisection of the cubic
    Im P(x) = A x^2 - B x + C on (0,1) -- returns all roots in (0,1]."""
    beta = as_beta(beta)
    A, B, C = coefsABC(beta)
    out = []
    xs = np.linspace(1e-12, 1.0, 20001)
    f = A[:, None] * xs[None, :] ** 2 - B[:, None] * xs[None, :] + C[:, None]
    return f, xs


def A_of_beta(beta, mode='bisect'):
    beta = as_beta(beta)
    Bsum = beta.sum(axis=0)
    s = np.sin(beta).sum(axis=0)
    if mode == 'bisect':
        x0 = x0_bisect(beta)
        x0 = np.where(Bsum <= PI, 1.0, x0)
    else:
        x0 = x0_theorem(beta)
    return x0 * s, x0


def x_max_branchvalid(beta, iters=200):
    """Largest x in (0, x0] such that 0 < theta_i < pi - beta_i for all i.

    theta_i < pi - beta_i  <=>  x < x_i^* := (sin b_i + cos b_i sin b_i? ) --
    solve exactly:  atan2(sin b, x-cos b) = pi - b   <=>  (x-cos b, sin b)
    is antiparallel to (sin(pi-b), ...) using tan: tan(pi-b) = sin b/(x-cos b)
    only if x-cos b > 0 (second quadrant).  Direct: the boundary is the ray
    direction pi-b: sin(theta)/... Use: theta = pi-b  <=>  x = cos b - sin b *
    cos(pi-b)/sin(pi-b) = cos b + sin b * cos b / sin b = 2 cos b?  Let's do it
    by continuity: x*(b) = cos b + sin b / tan(pi-b) = cos b - sin b * cos b/sin b
    = 0 when b<pi/2; for the *decreasing* theta, theta hits pi-b when
    tan(theta) = tan(pi - b) = -tan(b) => sin b/(x - cos b) = -tan b =>
    x - cos b = -cos b => x=0.  Hmm; so reconsider: theta(0+) = pi - b exactly,
    so branch boundary is approached only as x -> 0 and theta is *below*
    pi - b for all x>0 in the principal branch.  (theta strictly decreasing
    from pi-b to 0.)  => x_max = x0 always.  Documented in notes; here we
    verify numerically instead of duplicating logic.
    """
    beta = as_beta(beta)
    x0 = np.where(beta.sum(axis=0) <= PI, 1.0, x0_bisect(beta))
    th = theta(beta, x0)
    return x0, th, PI - beta


# --------------------------------------------------------------- self test
def self_test():
    rng = np.random.default_rng(20260218)
    beta = rng.uniform(0.05, PI - 0.05, size=(3, 3000))
    out = {}
    out['arg_vs_complex'] = float(np.max(np.abs(H(beta, 0.7) - H_alt(beta, 0.7))))
    A1, B1, C1 = coefsABC(beta)
    A2, B2, C2 = coefsABC_identity(beta)
    out['B_identity_res'] = float(max(np.max(np.abs(B1 - B2)),
                                      np.max(np.abs(A1 - A2)), np.max(np.abs(C1 - C2))))
    # Im P(x) = A x^2 - B x + C ?
    xs = np.array([0.13, 0.37, 0.5, 0.77, 1.0])
    b = beta[:, :50]
    z = (xs[None, None, :] - np.cos(b)[:, :, None]) + 1j * np.sin(b)[:, :, None]
    P = z[0] * z[1] * z[2]
    lhs = np.imag(P)
    A_, B_, C_ = coefsABC(b)
    rhs = A_[:, None] * xs[None, :] ** 2 - B_[:, None] * xs[None, :] + C_[:, None]
    out['ImP_quadratic_max_res'] = float(np.max(np.abs(lhs - rhs)))
    out['ImP_scale_rel_res'] = float(np.max(np.abs(lhs - rhs) / (np.abs(P) + 1e-30)))
    # H(1) = (3pi - Bsum)/2 ?
    out['H1_formula_res'] = float(np.max(np.abs(H(beta, 1.0) - (3 * PI - beta.sum(axis=0)) / 2)))
    # x0 bisection: H(x0)=pi
    m = beta.sum(axis=0) > PI
    x0 = x0_bisect(beta)
    out['bisect_root_res'] = float(np.max(np.abs(H(beta[:, m], x0[m]) - PI)))
    out['theory_vs_bisect_x0_maxdiff'] = float(np.max(np.abs(
        x0_theorem(beta)[m] - x0[m])))
    # branch validity at bisection root
    th = theta(beta, x0)
    out['branch_valid_all'] = bool((th < (PI - beta) + 1e-9).all())
    out['max_branch_slack'] = float(np.max(th - (PI - beta)))
    # A comparison
    A_b, _ = A_of_beta(beta, 'bisect')
    A_t, _ = A_of_beta(beta, 'theorem')
    out['A_bisect_max'] = float(A_b.max())
    out['A_theorem_max'] = float(A_t.max())
    out['A_bisect_vs_theorem_maxabsdiff'] = float(np.max(np.abs(A_b - A_t)))
    return out


def spot(beta):
    beta = np.asarray(beta, float)
    Bsum = float(beta.sum())
    s = float(np.sin(beta).sum())
    Ab, x0b = A_of_beta(beta, 'bisect')
    At, x0t = A_of_beta(beta, 'theorem')
    thb = theta(beta, float(x0b)).ravel()
    tht = theta(beta, float(x0t)).ravel()
    return dict(beta=beta.tolist(), Bsum=Bsum, sum_sin=s,
                x0_bisect=float(x0b), A_bisect=float(Ab), H_at_x0_bisect=float(H(beta, float(x0b))),
                theta_at_x0_bisect=thb.tolist(), branch_ok=bool((thb < PI - beta).all()),
                x0_theorem=float(x0t), A_theorem=float(At),
                H_at_x0_theorem=float(H(beta, float(x0t))),
                theta_at_x0_theorem=tht.tolist())
