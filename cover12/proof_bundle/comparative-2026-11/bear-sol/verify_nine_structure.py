"""Fixed-point certificates for a designated nine-disk boundary chain."""

from verify_arcs import sincos
from verify_upper import I

R0 = I("0.361102963744","0.361103")
PI0 = I("3.1415926","3.1415927")
AH = I("0.36946")
STEP = I("0.001").a
D = (9*AH-PI0).b
N = D//STEP


def pt(k):
    return I.make(k,k)


def downset(step=STEP):
    return range(D//step+1)


def lens_data(r, nu, step=STEP):
    data = []
    for a in downset(step):
        v = pt(AH.a-(a+1)*step)
        sv,cv = sincos(v)
        q = (r*r-sv*sv).sqrt()
        dr = cv-q
        term = sv-r*sincos(nu-v)[0]
        t1 = sincos(2*v-nu)[1]-r
        t2 = dr*sincos(nu-v)[1]
        h = t2.a if term.a >= 0 else (t1.a if term.b <= 0 else min(t1.a,t2.a))
        data.append((dr.a,h))
    return data


def pairs(data, r, step=STEP):
    h = [q[1] for q in data]
    return [min(h[i]+h[s-i] for i in range(s+1))-2*r.b for s in downset(step)]


def coef(s, c, nu):
    sn,cn = sincos(nu)
    a,b = s/(2*cn),c/(2*sn)
    return (a+b).a,(a-b).a


def tests():
    r = R0
    assert (sincos(AH)[0]-r).pos()
    assert (I("0.19")-pt(D)).pos()
    dlow = (I("0.30")+r).b
    assert (lens_data(r,I("0.85"))[-1][0] > dlow)
    assert I("0.81").a < PI0.a//2 and (sincos(I("0.81"))[0]-2*r).pos()
    assert 2*I("0.81").a+4*AH.a < PI0.a
    assert 2*(4*AH.a-D)-2*I("0.81").a>0

    nu = I("0.85")
    data = lens_data(r,nu)
    pairsums = pairs(data,r)
    assert min(pairsums)>0
    for k in (3,4):
        lower = 10*I.scale**2
        for w in downset():
            glo = pt(k*AH.a-(w+k)*STEP)
            ghi = pt(k*AH.a-w*STEP)
            assert 0 < glo.a <= ghi.a < PI0.a//2
            slo,clo = sincos(glo)
            _,chi = sincos(ghi)
            cp,_ = coef(slo,chi,nu)
            _,cm = coef(slo,clo,nu)
            assert cp > 0 and cm > 0
            for f in range(N-w+1):
                base = cp*pairsums[f]
                for e in range(w+1):
                    lower = min(lower,base+cm*pairsums[e])
        assert lower > 2*r.b*I.scale
        print(f"PASS: join corners separated by {k} arcs have distance > "
              f"{lower*1000//I.scale**2}/1000")

    cosD,sinD = sincos(pt(D))[::-1]
    _,lam = coef(cosD,sinD,nu)
    assert lam>0
    lower = min((dl-r.b)*I.scale+lam*pairsums[e]
                for i,(dl,_) in enumerate(data) for e in range(N-i+1))
    assert lower>2*r.b*I.scale
    print(f"PASS: bridge disk and opposite join corner separated by > "
          f"{lower*1000//I.scale**2}/1000")

    # Two corners with a single other corner between them impose |S| > 0.14.
    nu,kappa = I("0.77"),I("0.20")
    sums = pairs(lens_data(r,nu),r)
    assert min(sums)>0
    sk,ck = sincos(kappa)
    cp,cm = coef(ck,sk,nu)
    assert min(cp,cm)>0
    margin = 10*I.scale**2
    for e in downset():
        glo = pt(2*AH.a-(e+2)*STEP)
        assert 0<glo.a+kappa.a<=2*AH.a+kappa.a<PI0.a//2
        cb = sincos(glo+kappa)[1].b
        need = 2*r.b*I.scale+2*I("0.14").a*cb
        for f in range(N-e+1):
            margin = min(margin,cp*sums[f]+cm*sums[e]-need)
    assert margin>0
    print("PASS: every disk covering the two extreme corners of a triple has |S| > 0.14")


if __name__ == "__main__":
    tests()
