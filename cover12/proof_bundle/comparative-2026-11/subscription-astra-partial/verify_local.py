"""Exact interval certificates for a C3-symmetric local optimum."""
from fractions import Fraction
from intervals import I, Q, AD, hull, midpoint_inverse

CENTRE = [Fraction(s) for s in (
    "0.3611029637445086441130877020170651808485",
    "0.2782416608744279121486310228984788103685",
    "0.4080660554188964491866816423005303657064",
)]
ROOT_WIDTH = Fraction(1,10**36)


def cos_angle(r,x,y):
    return (x*x+y*y-r*r)/(2*x*y)


def angle_derivatives(r,x,y):
    g = cos_angle(r,x,y)
    f = 2*(1-g*g).sqrt()
    return (y*y-x*x-r*r)/(f*y*x*x), (x*x-y*y-r*r)/(f*x*y*y)


def parameters(r,a,t):
    u = a+r
    b = t+r
    c = (u+r*r).sqrt()
    p = angle_derivatives(r,1,c)[1]
    q, v = angle_derivatives(r,c,u)
    mu = (-p-q)/(p-q)
    lam = -angle_derivatives(r,1,b)[1]/angle_derivatives(r,a,t)[1]
    return u,b,c,mu,lam


def root_equations(r,a,t):
    u,b,c,mu,lam = parameters(r,a,t)
    f = cos_angle(r,1,c)
    # cos(pi/3-2*acos(f)), written algebraically.
    h = (2*f*f-1)/2 + I(3).sqrt()*f*(1-f*f).sqrt()
    g = ((1-mu)*angle_derivatives(r,c,u)[1]
         +lam*angle_derivatives(r,a,t)[0])
    return cos_angle(r,1,b)-h, a*a+t*t-r*r-a*t, g


def isolate_root():
    box = [hull(x,ROOT_WIDTH) for x in CENTRE]
    eq = root_equations(*[AD.variable(x,k) for k,x in enumerate(box)])
    jac = [row.d for row in eq]
    y = midpoint_inverse(jac)
    residual = root_equations(*[I(x) for x in CENTRE])
    contraction = []
    for i in range(3):
        norm=0
        for j in range(3):
            cell=I(int(i==j))-sum((I(y[i][k])*jac[k][j] for k in range(3)), I(0))
            norm += cell.maximum_abs()
        contraction.append(Fraction(norm,Q))
        offset = sum((I(y[i][k])*residual[k] for k in range(3)),I(0))
        assert contraction[i]<Fraction(1,10**25)
        assert Fraction(offset.maximum_abs(),Q) + ROOT_WIDTH*contraction[i] < ROOT_WIDTH
    print('one root in the indicated 3D box, contraction norm < 1e-25')
    r,a,t=box
    u,b,c,mu,lam=parameters(r,a,t)
    assert I('.7').hi < mu.lo < mu.hi < I('.8').lo
    assert I('.27').hi < lam.lo < lam.hi < I('.28').lo
    return box


def det3(m):
    return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
            -m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
            +m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))


def gradient(r,mu,lam,aa,tt,cc):
    h1,h2=angle_derivatives(r,aa,tt)
    gc,gu=angle_derivatives(r,cc,aa+r)
    return [
        (1-mu)*gu+lam*h1,
        angle_derivatives(r,1,tt+r)[1]+lam*h2,
        (1+mu)*angle_derivatives(r,1,cc)[1]+(1-mu)*gc,
    ]


def check_concavity(r,a,t):
    u,b,c,mu,lam=parameters(r,a,t)
    aa,tt,cc=[AD.variable(hull(x,Fraction(1,100000)),k)
              for k,x in enumerate((a,t,c))]
    grad=gradient(r,mu,lam,aa,tt,cc)
    negative_hessian=[[-v for v in g.d] for g in grad]
    h=negative_hessian
    minor1=h[0][0]
    minor2=h[0][0]*h[1][1]-h[0][1]*h[1][0]
    minor3=det3(h)
    assert [minor1.lo//Q, minor2.lo//Q, minor3.lo//Q] >= [3,10,1]
    assert min(minor1.lo,minor2.lo,minor3.lo) > 0
    # Check the monotonicities replacing b by t+r and u by a+r locally.
    assert angle_derivatives(r,1,tt+r)[1].v.lo > 0
    assert angle_derivatives(r,cc,aa+r)[1].v.lo > 0
    print('Sylvester determinants of -H have lower integer bounds',
          *(n.lo//Q for n in (minor1,minor2,minor3)))


def det(p,q):
    return p[0]*q[1]-p[1]*q[0]


def sub(p,q):
    return p[0]-q[0],p[1]-q[1]


def norm2(p):
    return p[0]*p[0]+p[1]*p[1]


def unique_at(point,centers,active,r):
    for i,p in enumerate(centers):
        if i not in active:
            assert (norm2(sub(p,point))-r*r).lo>0


def geometry(r,a,t):
    u,b,c,mu,lam=parameters(r,a,t)
    x=(1+u)/2
    y=(c*c-x*x).sqrt()
    s=I(3).sqrt()/2
    def orbit(p):
        p0,p1=p
        return [p,(-p0/2-s*p1,s*p0-p1/2),(-p0/2+s*p1,-s*p0-p1/2)]
    A=orbit((a,I(0)))
    B=orbit((b/2,b*s))
    Cp=orbit((x,y))
    Cm=orbit((x,-y))
    centers=A+B+Cp+Cm
    T=(t/2,t*s); H=(u,I(0)); P=(I(1),I(0))
    # A0,A1,B0 meet at T, A0,C0+,C0- at H; no fourth disk.
    unique_at(T,centers,{0,1,3},r)
    unique_at(H,centers,{0,6,9},r)
    unique_at(P,centers,{6,9},r)
    gc=cos_angle(r,1,c)
    q=(2*gc*gc-1,2*gc*(1-gc*gc).sqrt())
    unique_at(q,centers,{3,6},r)
    # q is between 0 and pi/3. 2*h < pi/3 since gc>cos(pi/6).
    assert (gc-s).lo>0 and (1-gc).lo>0
    assert (r-a).lo>0 and (1-u).lo>0 and (1-t).lo>0
    assert (a-t).hi<0 and (t-b).hi < 0
    # Six congruent additional triangles have total positive slack.
    p,v,w=A[0],Cp[0],B[0]
    pv,pw=sub(v,p),sub(w,p)
    area2=det(pv,pw)
    assert area2.lo>0
    remain=4*area2*area2*r*r - norm2(pv)*norm2(pw)*norm2(sub(w,v))
    assert remain.lo>0
    # Directed triangles for the interior polygon.
    triangles=[]
    triangles.append((0,1,2))
    for i in range(3):
        j=(i+1)%3
        triangles.extend([(i,i+6,i+3),(i,i+3,j),
                          (j,i+3,j+9),(i,i+9,i+6)])
    hull_order=[9,6,3,10,7,4,11,8,5]
    outer=[centers[i] for i in hull_order]
    for i in range(9):
        h=sub(outer[(i+1)%9],outer[i])
        for j in range(9):
            if j!=i and j!=(i+1)%9:
                assert det(h,sub(outer[j],outer[i])).lo>0
    edges={}
    for i,j,k in triangles:
        v,w,z=centers[i],centers[j],centers[k]
        assert det(sub(w,v),sub(z,v)).lo>0
        for h,g in [(i,j),(j,k),(k,i)]:
            key=tuple(sorted((h,g)))
            edges[key]=edges.get(key,0)+(1 if h<g else -1)
    for j,k in zip(hull_order,hull_order[1:]+hull_order[:1]):
        edges[tuple(sorted((j,k)))]+=(-1 if j<k else 1)
    assert all(x==0 for x in edges.values())
    print('candidate cover verified, six unused circumradius constraints have strict slack')
    print('candidate junctions meet only their stated nearest centers')


if __name__=='__main__':
    box=isolate_root()
    check_concavity(*box)
    geometry(*box)
