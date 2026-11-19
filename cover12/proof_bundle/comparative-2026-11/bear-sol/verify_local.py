"""Exact derivative checks for a local lower bound at the construction."""

from verify_upper import I, J, geometry, sq, vecsub


def acos_derivatives(z):
    # Only the first and second derivatives are used.
    w = (1-z.f*z.f).sqrt()
    return J(0,-z.d/w,-z.dd/w-z.f*z.d*z.d/(w*w*w))


def outer(r,t):
    d = t+r
    return acos_derivatives((1+d*d-r*r)/(2*d))


def inner(r,t,s):
    return acos_derivatives((t*t+s*s-r*r)/(2*t*s))


def checks():
    r = I("0.361102963744","0.361102963745")
    s = I("0.27824163","0.27824168")
    x,y,t,b,_,_ = geometry(r,s)

    # Fixed normal at the plus lens vertex, with coordinates in the join frame.
    nx,ny = (1-x)/r,y/r
    h = (x*x+y*y).sqrt()
    sa,ca = y/h,x/h
    sin,cos = J(sa,ca,-sa),J(ca,-sa,-ca)
    d = cos-(J(r)*J(r)-sin*sin).sqrt()
    H = (cos*J(nx)+sin*J(ny))*d
    assert H.d.pos() and H.dd.pos()
    # These determinants put -n in the strict normal cone of the inward
    # vertex, formed by the rays c-(1,0) and c-(cos(2a),sin(2a)).
    _,_,_,_,qx,qy = geometry(r,s)
    assert ((x-1)*(-ny)+y*nx).pos()
    assert ((-nx)*(y-qy)+ny*(x-qx)).pos()
    # Identify the inner (rather than outer) vertex of the endpoint lens.
    assert (ca-h).pos()

    ta = outer(J(r),J(t,1))
    gt = inner(J(r),J(t,1),J(s))
    gs = inner(J(r),J(t),J(s,1))
    gdiag = inner(J(r),J(t,1),J(s,1))
    a = -ta.d/(2*gt.d)
    assert a.pos()
    assert ((1-r*r).sqrt()-b).pos()
    xj,yj,_,_,_,_ = geometry(J(r),J(s,1))
    h2 = x*x+y*y
    ap = (x*yj.d-y*xj.d)/h2
    app = (x*yj.dd-y*xj.dd-2*ap*(x*xj.d+y*yj.d))/h2
    tt = ta.dd/2+a*gt.dd
    ss = a*gs.dd+app
    ts = a*(gdiag.dd-gt.dd-gs.dd)/2
    assert (-tt).pos() and (-ss).pos() and (tt*ss-ts*ts).pos()

    sqrt3 = I(3).sqrt()

    def rot(c):
        X,Y = c
        return [(-X-sqrt3*Y)/2,(sqrt3*X-Y)/2]

    centers = [[x,-y],[x,y],[b/2,b*sqrt3/2],[s,I(0)]]
    centers += [rot(c) for c in centers[:4]]
    centers += [rot(c) for c in centers[4:8]]
    # The named triples are the only disks at each of these contact points.
    for p, allowed in (([s+r,I(0)],(0,1,3)),([t/2,t*sqrt3/2],(2,3,7))):
        assert (1-sq(p)).pos()
        for i,c in enumerate(centers):
            if i not in allowed:
                assert (sq(vecsub(c,p))-r*r).pos()
    print("PASS: high-pair tangent bound has positive slope and strict convexity")
    print("PASS: combined bridge potential has negative definite Hessian")
    print("PASS: the active triples exclude all other disks")


if __name__ == "__main__":
    checks()
