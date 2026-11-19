from graphs import MAIN, boundary_pairs, graph
from intervals import D, Interval, Jet, ONE, PI, Q, SCALE, ZERO, cos, sin
from network import CAP, R, effective


SQ3 = Q(3).sqrt()


def motif(r,x):
    y = (1-x*x).sqrt()
    u = (r*r-x*x).sqrt()
    sb = (1-2*x*x)*(SQ3/2) - x*y
    cb = (1-2*x*x)/2 + x*y*SQ3
    v = (r*r-sb*sb).sqrt()
    U = y-u
    V = cb-v
    P = U*U-r*r
    T = V-r
    S = P-r
    return S*S+T*T-S*T-r*r, (r,x,y,u,sb,cb,v,U,V,P,T,S)


def jet(x):
    return motif(Jet.var(x[0],0), Jet.var(x[1],1))[0]


def isolate():
    X = [Interval(D('0.36110296374450').lo,D('0.36110296374452').hi),
         Interval(D('0.35658979904815').lo,D('0.35658979904818').hi)]
    c = [x.mid() for x in X]
    jc, jX = jet(c), jet(X)
    fc = [jc.v,jc.g[1]]
    J = [jX.g,jX.h[1]]
    B = [[D('-0.235686'),ZERO],[D('-0.19047'),D('0.0018966')]]
    assert (B[0][0]*B[1][1]).hi < 0
    E = [[Q(i == j)-sum(B[i][k]*J[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    assert all(1000*sum(e.absupper() for e in row)<SCALE for row in E)
    for i in range(2):
        image = c[i]-sum(B[i][k]*fc[k] for k in range(2)) + sum(E[i][k]*(X[k]-c[k]) for k in range(2))
        assert X[i].lo < image.lo <= image.hi < X[i].hi
        if i == 0:
            assert D('0.361102963744505').hi < image.lo <= image.hi < D('0.361102963744515').lo
    return X


def sub(a,b):
    return a[0]-b[0],a[1]-b[1]


def scale(k,a):
    return k*a[0],k*a[1]


def rotate(a):
    x,y = a
    return (-x-SQ3*y)/2,(SQ3*x-y)/2


def norm2(a):
    return a[0].square()+a[1].square()


def cross(a,b):
    return a[0]*b[1]-a[1]*b[0]


def circum_radius2(A,B,C):
    v,w = sub(B,A),sub(C,A)
    v2,w2 = norm2(v),norm2(w)
    det = 2*cross(v,w)
    rel = ((v2*w[1]-w2*v[1])/det,(v[0]*w2-w[0]*v2)/det)
    return norm2(rel)


def verify_construction(p):
    r,x,y,u,sb,cb,v,U,V,P,T,S = p
    assert r.hi < R.lo
    assert 0 < x.lo < x.hi < Q(1,2).lo
    assert all(z.lo > 0 for z in (U,V,S,T,P,u,v,sb,cb))
    E0m,E0p = scale(U,(y,-x)),scale(U,(y,x))
    V0m,V0p = scale(V,(Q(1,2),-SQ3/2)),scale(V,(Q(1,2),SQ3/2))
    I0 = S,ZERO
    I1 = rotate(I0)
    I2 = rotate(I1)
    faces = [(V0m,E0m,I0),(E0m,E0p,I0),(E0p,V0p,I0),(V0p,I1,I0),(I0,I1,I2)]
    for A,B,C in faces:
        assert cross(sub(B,A),sub(C,A)).lo > 0
    assert S.square().hi < r.square().lo
    slack = r.square()-circum_radius2(E0p,V0p,I0)
    assert slack.lo > D('0.000042').hi
    print(f'construction: positive face orientations, floor(10^9 * mixed-face squared slack) >= {slack.lo*10**9//SCALE}')


def stress(p):
    r,x,y,u,sb,cb,v,U,V,P,T,S = p
    c = ONE
    a0 = ((U-P*y)/u-P)/2
    a1 = ((U-P*y)/u+P)/2
    d = (1-P)/r
    f = d*r/(2*S-T)
    e = f*(2*T-S)/r
    b = e*r/(2*v)
    assert all(z.lo > 0 for z in (a0,a1,b,c,d,e,f))
    rim_sides = [b,a1,a0]*3 + [b,a0,a1]*3
    faces = [ZERO]*3+[c,c,d]+[ZERO]*3+[e,f,f]
    return rim_sides+faces*3


def main_hessian(p):
    b = MAIN[0]
    n, edges = graph(*MAIN)
    k = effective(b,n,edges,stress(p))
    H = [[ZERO for j in range(b-1)] for i in range(b-1)]
    for (_,_,chain),weight in zip(boundary_pairs(b),k):
        v = [int(i in chain)-int(b-1 in chain) for i in range(b-1)]
        assert 2*len(chain)*CAP.hi < SCALE
        weight = weight*cos(2*PI*CAP*len(chain))
        for i in range(b-1):
            for j in range(b-1):
                H[i][j] += weight*(v[i]*v[j])
    smallest = None
    for p in range(b-1):
        pivot = H[p][p]
        assert pivot.lo > 0
        smallest = pivot.lo if smallest is None else min(smallest,pivot.lo)
        for i in range(p+1,b-1):
            for j in range(p+1,b-1):
                H[i][j] -= H[i][p]*H[p][j]/pivot
    print(f'main topology: positive Hessian certificate, floor(10^6 * smallest pivot) >= {smallest*10**6//SCALE}')


def geometric_constants():
    assert sin(PI*CAP).lo > R.hi
    assert 2*PI.hi*CAP.hi < D('0.739').lo*SCALE
    assert 8*CAP.hi < SCALE
    M = D('0.690')
    alpha = D('0.224')
    q = (1+M.square()-R.square())/(2*M)
    assert q.lo > cos(alpha).hi
    amin = D('0.3695')
    assert (2*M*sin(PI-7*amin)).lo > (2*R).hi
    assert (2*(1-R)*sin(PI-(13*amin+alpha)/2)).lo > (2*R).hi
    print('geometric constants: verified')


def replay_main():
    geometric_constants()
    X = isolate()
    print('root: contraction and inclusion on the stated rational box verified')
    _,p = motif(*X)
    verify_construction(p)
    main_hessian(p)
