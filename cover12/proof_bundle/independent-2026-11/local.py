"""Interval inequalities for local optimality without a symmetry assumption."""
from symmetric import Interval, alpha_prime, cos_arc


def alpha_second(r, t):
    g = cos_arc(r, t)
    d = (1-g*g).sqrt()
    gp = (1-(1-r*r)/(t*t))/2
    gpp = (1-r*r)/(t*t*t)
    return -gpp/d - g*gp*gp/(d*d*d)


def certify_local_inequalities():
    r = Interval(".361102963744", ".361102963745")
    u = Interval(".27824166087", ".27824166088")
    b = u+r
    t = (b+r*r).sqrt()
    g = (b*b+t*t-r*r)/(2*b*t)
    beta_prime = ((b*b-r*r)/(t*t)-1)/(2*b*(1-g*g).sqrt())
    assert (alpha_prime(r, t)+beta_prime).hi < 0

    # Derivatives of the outer lens radius h(w, d) at d=2*pi/3, w=u.
    s, c = Interval(3).sqrt()/2, Interval(1)/2
    z = (r*r-u*u*s*s).sqrt()
    h = u*c+z
    hw = c-u*s*s/z
    hd = -u*s/2-u*u*s*c/(2*z)
    hww = -s*s/z-u*u*s*s*s*s/(z*z*z)
    hwd = -s/2-u*s*c/z-u*u*u*s*s*s*c/(2*z*z*z)
    hdd = -u*c/4-u*u*(c*c-s*s)/(4*z)-u*u*u*u*s*s*c*c/(4*z*z*z)

    v = r+h
    d1, d2 = alpha_prime(r, v), alpha_second(r, v)
    h2 = alpha_second(r, t)/(2*t*t)-alpha_prime(r, t)/(2*t*t*t)
    kww = h2 + d2*hw*hw+d1*hww
    kwd = d2*hw*hd+d1*hwd
    kdd = d2*hd*hd+d1*hdd
    det = kww*kdd-kwd*kwd
    assert kww.hi < 0 and det.lo > 0
    print(f"Local Hessian determinant is greater than {float(det.lo):.6f}.")


if __name__ == "__main__":
    certify_local_inequalities()
