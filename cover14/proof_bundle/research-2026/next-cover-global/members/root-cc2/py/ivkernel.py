"""root-cc2: interval kernel for the n14 local root certificate  (final).

Object
------
Phi : R^3 -> R^3,   Phi(z,C,r) = ( F, G, J ),
    F, G : the two contact equations of the n14 D2 family
           (definitions re-derived and audited in audit01_root.py),
    J    = F_z G_C - F_C G_z     (stationarity of the 2-contact system at fixed r).

Certificate needs
-----------------
(a) an interval enclosure of Phi on a box;
(b) an interval enclosure of the Jacobian DPhi on the same box:
      DPhi = [ dF ; dG ; dJ ],
      dJ_k = sum_m ( F_{zk} G_C + F_z G_{Ck} - F_{Ck} G_z - F_C G_{zk} )
           = [ (H_F[0][k] G_C + F_z H_G[1][k] - H_F[1][k] G_z - F_C H_G[0][k]) ]
    so second derivatives of F and G suffice.

Realisation
-----------
A single expression tree `_expr` of +,-,*,/,sqrt is evaluated in two algebras:

  * Val  (a + b*eps, eps^2 = 0): value and first derivatives of F, G, J.
  * Hyper (hyper-dual: a + b*d + c*e + k*d*e with d^2 = e^2 = 0): setting
    x_k -> x_k + d (direction e_i) and x_k -> x_k + e (direction e_j) gives the
    mixed second derivative d_i d_j F as the d*e coefficient == its .r4 field.
    Values always stay at the true point, so radicands stay strictly positive for
    the whole box; there is no step size, no truncation and no sampling.

Checks (calib01_kernel.py): textbook functions with hand values; Phi at the lead
root vs an mpmath .diff reference kernel; dF, dG vs mp.diff; the whole Hessian of
F and G plus (J, dJ) vs EXACT sympy differentiation (~1e-50 at 60 dps); interval
containment over a box; and a finite-difference enclosure check of the Jacobian on
a small box.

Development failure modes (recorded in DEAD.md):
  * plain intervals in the gradient slots           -> products lost second order,
                                                       dJ came out identically 0;
  * nested Jet objects                              -> infinite recursion;
  * "unit-direction" Val coordinates (value + 1)    -> negative radicands.
"""
import mpmath as mp
from mpmath import iv


# --------------------------------------------------------------------------- #
# interval helpers
# --------------------------------------------------------------------------- #
def L(x):
    return mp.mpf(x.a.a)


def R(x):
    return mp.mpf(x.b.b)


def iv_thin(x):
    return iv.mpf(mp.mpf(x))


def iv_from(a, b):
    return iv.mpf([mp.mpf(a), mp.mpf(b)])


def mid(x):
    return (L(x) + R(x)) / 2


def wid(x):
    return R(x) - L(x)


def _z0():
    return iv_thin(0)


def _o1():
    return iv_thin(1)


def _half():
    return iv_thin(mp.mpf(1) / 2)


def _quarter():
    return iv_thin(mp.mpf(1) / 4)


def _guard(v, what):
    a, b = L(v), R(v)
    if not (mp.isfinite(a) and mp.isfinite(b)):
        raise ValueError('%s produced an unbounded interval %s' % (what, v))
    return v


def as_iv(x):
    if hasattr(x, 'a') and hasattr(x, 'b'):
        return x
    if hasattr(x, 'v'):                                # Val / Hyper
        return x.v
    if isinstance(x, mp.mpf):
        return iv_thin(x)
    if isinstance(x, (int, float, str)):
        return iv_thin(mp.mpf(x))
    raise TypeError('cannot make an interval from %r' % (x,))


# --------------------------------------------------------------------------- #
# Val : first-order object
# --------------------------------------------------------------------------- #
class Val:
    __slots__ = ('v', 'g')

    def __init__(self, v, g=None):
        self.v = v
        self.g = list(g) if g is not None else [_z0(), _z0(), _z0()]

    @staticmethod
    def cst(x):
        return x if isinstance(x, Val) else Val(as_iv(x))

    @staticmethod
    def var(v, k):
        """independent coordinate x_k over interval v"""
        g = [_z0(), _z0(), _z0()]
        g[k] = _o1()
        return Val(v, g)

    def __add__(self, o):
        o = as_val(o)
        return Val(self.v + o.v, [self.g[k] + o.g[k] for k in range(3)])

    __radd__ = __add__

    def __neg__(self):
        return Val(-self.v, [-a for a in self.g])

    def __sub__(self, o):
        return self + (-as_val(o))

    def __rsub__(self, o):
        return as_val(o) + (-self)

    def __mul__(self, o):
        o = as_val(o)
        return Val(self.v * o.v, [self.g[k] * o.v + self.v * o.g[k] for k in range(3)])

    __rmul__ = __mul__

    def __truediv__(self, o):
        return self * as_val(o).inv()

    def __rtruediv__(self, o):
        return as_val(o) * self.inv()

    def inv(self):
        v = self.v
        if not (L(v) > 0 or R(v) < 0):
            raise ValueError('reciprocal of interval containing 0: %s' % v)
        d = _guard(1 / v, 'reciprocal')
        d2 = d * d
        return Val(d, [-self.g[k] * d2 for k in range(3)])

    def sqrt(self):
        v = self.v
        if not (L(v) > 0):
            raise ValueError('sqrt of interval not strictly positive: %s' % v)
        w = iv.sqrt(v)
        A1 = _guard(1 / w, 'sqrt') * _half()
        return Val(w, [self.g[k] * A1 for k in range(3)])

    def pow_int(self, n):
        if n < 1:
            raise ValueError('pow_int needs n >= 1')
        r = Val(self.v, [self.g[k] for k in range(3)])
        for _ in range(n - 1):
            r = r * self
        return r

    def __pow__(self, n):
        return self.pow_int(n)

    def __repr__(self):
        return 'Val(%s)' % (self.v,)


def as_val(x):
    if isinstance(x, Val):
        return x
    return Val(as_iv(x))


# --------------------------------------------------------------------------- #
# Hyper : hyper-dual second-order object,  d^2 = e^2 = 0, d*e != 0
# --------------------------------------------------------------------------- #
class Hyper:
    """a + b*d + c*e + k*d*e.  .r4 holds the mixed coefficient."""
    __slots__ = ('v', 'd', 'e', 'r4')

    def __init__(self, v, d=None, e=None, r4=None):
        self.v = v
        self.d = d if d is not None else _z0()
        self.e = e if e is not None else _z0()
        self.r4 = r4 if r4 is not None else _z0()

    @staticmethod
    def cst(x):
        return Hyper(as_iv(x))

    @staticmethod
    def dvar(v):
        """x + d"""
        return Hyper(v, _o1(), _z0(), _z0())

    @staticmethod
    def evar(v):
        """x + e"""
        return Hyper(v, _z0(), _o1(), _z0())

    def __add__(self, o):
        o = as_hyper(o)
        return Hyper(self.v + o.v, self.d + o.d, self.e + o.e, self.r4 + o.r4)

    __radd__ = __add__

    def __neg__(self):
        return Hyper(-self.v, -self.d, -self.e, -self.r4)

    def __sub__(self, o):
        return self + (-as_hyper(o))

    def __rsub__(self, o):
        return as_hyper(o) + (-self)

    def __mul__(self, o):
        o = as_hyper(o)
        # (a+b d+c e+k de)(A+B d+C e+K de):
        #   value aA
        #   d: aB + bA
        #   e: aC + cA
        #   de: aK + bC + cB + kA
        return Hyper(self.v * o.v,
                     self.v * o.d + self.d * o.v,
                     self.v * o.e + self.e * o.v,
                     self.v * o.r4 + self.d * o.e + self.e * o.d + self.r4 * o.v)

    __rmul__ = __mul__

    def inv(self):
        v = self.v
        if not (L(v) > 0 or R(v) < 0):
            raise ValueError('reciprocal of interval containing 0: %s' % v)
        d = _guard(1 / v, 'reciprocal')
        d2 = d * d
        d3 = d2 * d
        # u = 1/q ; u' = -q'/q^2 ; (u)_{de} = -(q)_{de}/q^2 + 2 q_d q_e / q^3
        return Hyper(d, -self.d * d2, -self.e * d2,
                     -self.r4 * d2 + self.d * self.e * (2 * d3))

    def __truediv__(self, o):
        return self * as_hyper(o).inv()

    def __rtruediv__(self, o):
        return as_hyper(o) * self.inv()

    def sqrt(self):
        v = self.v
        if not (L(v) > 0):
            raise ValueError('sqrt of interval not strictly positive: %s' % v)
        w = iv.sqrt(v)
        r = _guard(1 / w, 'sqrt')                  # v^{-1/2}
        h = _half()
        A1 = r * h                                 # phi'  = 1/(2 sqrt q)
        A2 = -(r * r * r) * _quarter()             # phi'' = -1/(4 q^{3/2})
        return Hyper(w, self.d * A1, self.e * A1,
                     self.r4 * A1 + self.d * self.e * A2)

    def pow_int(self, n):
        if n < 1:
            raise ValueError('pow_int needs n >= 1')
        r = Hyper(self.v, self.d, self.e, self.r4)
        for _ in range(n - 1):
            r = r * self
        return r

    def __pow__(self, n):
        return self.pow_int(n)

    def __repr__(self):
        return 'Hyper(%s)' % (self.v,)


def as_hyper(x):
    if isinstance(x, Hyper):
        return x
    return Hyper(as_iv(x))


# --------------------------------------------------------------------------- #
# the shared expression tree
# --------------------------------------------------------------------------- #
def _expr(z, C, r, F):
    """F, G, J built from the same operands in whichever algebra F is.

    `F` must supply cst(x) and the four basic operations on its elements.
    """
    s = (1 - r * r).sqrt()                              # s = sqrt(1-r^2)
    A = (s + z) / 2
    t = r + (r * r - z * z).sqrt()                      # site3 (0,t)
    B = r + (r * r - (A - z) * (A - z)).sqrt()          # site1 (A,B)
    D = 1 - (r * r - C * C).sqrt()                      # site2 (C,D)

    v1 = (1 + A * A + B * B - r * r) / 2
    v2 = (1 + C * C + D * D - r * r) / 2
    det = A * D - B * C
    p1x = (v1 * D - v2 * B) / det
    p1y = (A * v2 - C * v1) / det

    Fv = (p1x * p1x + p1y * p1y - 1) ** 2 + (p1x - A) ** 2 + (p1y - B) ** 2 - r * r

    cross = (C - A) * (t - B) - (D - B) * (-A)
    l1 = (A - C) ** 2 + (B - D) ** 2
    l2 = C * C + (D - t) ** 2
    l3 = A * A + (B - t) ** 2
    Gv = l1 * l2 * l3 - 4 * r * r * cross * cross

    J = Fv * Gv                                         # only for its value (Val)
    return Fv, Gv, J, dict(s=s, A=A, B=B, C=C, D=D, t=t, p1x=p1x, p1y=p1y,
                           cross=cross, l1=l1, l2=l2, l3=l3, det=det)


# --------------------------------------------------------------------------- #
# the map Phi
# --------------------------------------------------------------------------- #
def phi_objects(z, C, r):
    """(Fv, Gv, Jv) as Vals: values and first derivatives of Phi."""
    vals = (z, C, r)
    Fv, Gv = _val_FG(vals)
    Jv = _J_val(vals)
    return (Fv, Gv, Jv), {}


def _val_FG(vals):
    """F and G as Vals with their gradients: coordinate k is Val.var(v_k, k)."""
    z, C, r = (Val.var(as_iv(vals[k]), k) for k in range(3))
    Fv, Gv, _, info = _expr(z, C, r, Val)
    return Fv, Gv


def phi_intervals(z, C, r):
    """Phi as an interval vector (point value when the arguments are thin)."""
    vals = (z, C, r)
    Fv, Gv = _val_FG(vals)
    Jv = _J_val(vals)
    return [Fv.v, Gv.v, Jv.v]


def _second_derivatives(vals):
    """H[t][i][j] = d_i d_j (F if t=0 else G) at vals, in ONE hyper-dual pass.

    Every coordinate is perturbed as x_k + d + e with d^2 = e^2 = 0.  The d*e
    coefficient (.r4) of the result is the mixed second derivative, and taking the
    (d*e)-coefficient of the output for each output component i,j at once is
    legitimate precisely because the two perturbations are independent nilpotents:
    for i != j the term a_{ij} b + a_i b_j + a_j b_i + a b_{ij} is exactly the
    coefficient, and for i == j it is the pure second derivative.  Values stay at
    the true point throughout.
    """
    coords = [Hyper(as_iv(vals[m]), _o1(), _o1(), _z0()) for m in range(3)]
    Fv, Gv, _, _ = _expr(*coords, Hyper)
    H = [[[None]*3 for _ in range(3)] for _ in range(2)]
    # the single pass gives the full Hessian of F and G only for i=0,j=... pairs;
    # to obtain every (i,j) entry independently we perturb direction pairs:
    H = [[[None]*3 for _ in range(3)] for _ in range(2)]
    for i in range(3):
        for j in range(3):
            ci = []
            for m in range(3):
                ci.append(Hyper(as_iv(vals[m]),
                                _o1() if m == i else _z0(),
                                _o1() if m == j else _z0(),
                                _z0()))
            Fi, Gi, _, _ = _expr(*ci, Hyper)
            H[0][i][j] = Fi.r4
            H[1][i][j] = Gi.r4
    return H


def _J_val(vals):
    """J as a Val: value from F_z G_C - F_C G_z, gradient from the hyper-dual passes.

    Fv.g[k] is the interval d_k F (rows are the gradients); Gv.g[k] likewise.
    """
    Fv, Gv = _val_FG(vals)
    H = _second_derivatives(vals)
    Fz, FC, Gz, GC = Fv.g[0], Fv.g[1], Gv.g[0], Gv.g[1]
    JV = Fz * GC - FC * Gz
    dJ = [H[0][0][k] * GC + Fz * H[1][1][k] - H[0][1][k] * Gz - FC * H[1][0][k]
          for k in range(3)]
    return Val(JV, dJ)


def jacobian_intervals(z, C, r):
    """Jacobian of Phi, as an interval 3x3 matrix."""
    vals = (z, C, r)
    Fv, Gv = _val_FG(vals)
    Jv = _J_val(vals)
    return [[Fv.g[0], Fv.g[1], Fv.g[2]],
            [Gv.g[0], Gv.g[1], Gv.g[2]],
            [Jv.g[0], Jv.g[1], Jv.g[2]]]
