"""Interval certificate for a full-dimensional neighbourhood of the 4+5 candidate."""

from fractions import Fraction

from construction import CENTER, ETA, cross, geometry, inverse_mid, minus, verify_geometry, verify_root
from intervals import Interval as I


N = 22
ZERO, ONE = I(0), I(1)
HALF = I("0.5")
KAPPA = I("0.1")
ACTIVE_INNER = (0, 1, 2, 4, 6, 7, 8)
P_FAN = (0, 1, 7, 8)
PIVOTS = tuple(j for j in range(N) if j not in (1, 12, 14, 20))
DUAL_SLOPES = tuple(tuple(I(Fraction(x, 100000)) for x in row) for row in (
    (-2670,6500,-546), (-2300,6696,-3671), (601,-532,-4912),
    (537,-2498,-1258), (530,-3570,0), (537,-2498,1258),
    (601,-532,4912), (-2300,6696,3671), (-2670,6500,546),
))


def dot(a, b):
    return sum(u * v for u, v in zip(a, b))


def exact(value):
    return I(value.mid())


def symmetric_point(box):
    r, a, b, t = box
    _, _, _, c, right, e, left, d, *_ = geometry(r, a, b, t)
    sites = [(e[0], ZERO), right, c, left, d, (d[0], -d[1]), (left[0], -left[1]),
             (c[0], -c[1]), (right[0], -right[1])]
    return [r, a, b, ZERO, *(v for xy in sites for v in xy)]


def verify_active_arcs(box, root):
    r,a,b,t = box
    p,q,_,_,_,_,_,_,_,_,v,v1,_,_,z = geometry(r,a,b,t)
    reflect = lambda w: (w[0],-w[1])
    witnesses = (v1,v,z,(-b-r,ZERO),reflect(z),reflect(v),reflect(v1))
    sites = list(zip(root[4::2],root[5::2]))
    for edge, witness in zip(ACTIVE_INNER,witnesses):
        f = p if edge in P_FAN else q
        u = minus(witness,f)
        assert cross(minus(sites[edge],f),u).lo>0
        assert cross(minus(sites[(edge+1)%9],f),u).hi<0


def export_constants(root):
    scale = 1<<51
    lam = multipliers(fan_rows(root))
    for x in [*root,*lam]:
        print(x.lo*scale//I.SCALE,-(-x.hi*scale//I.SCALE))


def endpoint_derivatives(x, y, r, sign, outer, weight=ONE):
    """Derivatives of sign*arg(x+iy) minus weight times its half-width."""
    distance2 = x.square() + y.square()
    distance = distance2.sqrt()
    er = (x / distance, y / distance)
    et = (-er[1], er[0])
    if outer:
        k = 1 - r.square()
        cosine = (distance + k / distance) / 2
        sine = (1 - cosine.square()).sqrt()
        c1 = (1 - k / distance2) / 2
        c2 = k / (distance2 * distance)
        radial1 = c1 / sine
        radial2 = c2 / sine + cosine * c1.square() / (sine.square() * sine)
        r1 = -r / (distance * sine)
    else:
        gap = 4 * r.square() - distance2
        delta = gap.sqrt()
        radial1 = 1 / delta
        radial2 = distance / (gap * delta)
        r1 = -distance / (r * delta)
    radial1, radial2 = weight*radial1, weight*radial2
    gradient = [radial1 * er[i] + sign * et[i] / distance for i in range(2)]
    hessian = [[
        radial2 * er[i] * er[j] + (radial1 / distance) * et[i] * et[j]
        - sign * (er[i] * et[j] + et[i] * er[j]) / distance2
        for j in range(2)
    ] for i in range(2)]
    return weight*r1, gradient, hessian


def fan_rows(point):
    """Gradients and spatial Hessians of the 18 active inequalities."""
    r, a, b, v = point[:4]
    rows = []

    def empty():
        return [ZERO] * N, [[ZERO] * (N-1) for _ in range(N-1)]

    def endpoint(row, site, sign, inner):
        gradient, hessian = row
        xi, yi = 4+2*site, 5+2*site
        x, y = point[xi], point[yi]
        dx, dy = [(xi, 1)], [(yi, 1)]
        if inner is not None:
            if inner == 1:
                x = x - a
                dx.append((1, -1))
            else:
                x = x + b
                dx.append((2, 1))
            y = y - v
            dy.append((3, -1))
        r1, g, h = endpoint_derivatives(x, y, r, sign, inner is None)
        gradient[0] += r1
        derivatives = (dx, dy)
        for k in range(2):
            for i, u in derivatives[k]:
                gradient[i] += u * g[k]
                for l in range(2):
                    for j, w in derivatives[l]:
                        hessian[i-1][j-1] += u * w * h[k][l]

    for outer, edges in ((True, range(9)), (False, ACTIVE_INNER)):
        for i in edges:
            row = empty()
            inner = None if outer else 1 if i in P_FAN else 2
            endpoint(row, i, -1, inner)
            endpoint(row, (i + 1) % 9, 1, inner)
            rows.append(row)

    mid, d = (a - b) / 2, (a + b) / 2
    h = (r.square() - d.square()).sqrt()
    for site, sign in ((2, 1), (7, -1)):
        x, y = 4+2*site, 5+2*site
        sx, sy = point[x]-mid, point[y]-v-sign*h
        grad, hess = empty()
        grad[0] = -2 * (sign*sy*r/h + r)
        dx = ((1, -HALF), (2, HALF), (x, ONE))
        along = sign * d / (2*h)
        dy = ((1, along), (2, along), (3, -ONE), (y, ONE))
        for residual, derivatives in ((sx, dx), (sy, dy)):
            for i, u in derivatives:
                grad[i] += 2 * residual * u
                for j, w in derivatives:
                    hess[i-1][j-1] += 2 * u * w
        y2 = sign * r.square() / (4 * h.square() * h)
        for i in (0, 1):
            for j in (0, 1):
                hess[i][j] += 2 * sy * y2
        rows.append((grad, hess))
    return rows


def multipliers(rows):
    matrix = [[grad[j] for grad, _ in rows] for j in PIVOTS]
    inverse = inverse_mid(matrix)
    size = len(matrix)
    defect = max(sum((I(int(i == j)) - dot(inverse[i], [row[j] for row in matrix])).abs_upper()
                     for j in range(size)) for i in range(size))
    assert defect < I.SCALE // 2
    center = [-row[0] for row in inverse]
    norm = max(v.abs_upper() for v in center)
    radius = Fraction(defect*norm, (I.SCALE-defect)*I.SCALE)
    assert all(lam.lo > I(radius).hi for lam in center)
    return [lam + I(-radius, radius) for lam in center]


def lagrangian_hessian(rows, lam, root, box):
    dim = N-1
    matrix = [[ZERO] * dim for _ in range(dim)]
    widths = [I.raw(0, (x-y).abs_upper()) for x, y in zip(box, root)]
    for k, (grad, hess) in enumerate(rows):
        coefficient = lam[k]
        if k < 9:
            error = sum(I.raw(0, g.abs_upper()) * w for g, w in zip(grad[1:], widths[1:]))
            error = I.raw(-error.hi, error.hi)
            assert (lam[k] + (KAPPA/2) * error).lo > 0
            coefficient += KAPPA * error
        for i in range(dim):
            for j in range(dim):
                matrix[i][j] += coefficient * hess[i][j]
                if k < 9:
                    matrix[i][j] += KAPPA * grad[i+1] * grad[j+1]
    return matrix


def preconditioner(matrix):
    """Build a fixed dyadic congruence near an inverse Cholesky factor."""
    dim = len(matrix)
    lower = [[I(int(i == j)) for j in range(dim)] for i in range(dim)]
    diagonal = [ZERO] * dim
    for i in range(dim):
        diagonal[i] = exact(exact(matrix[i][i]) -
                            sum(lower[i][k].square()*diagonal[k] for k in range(i)))
        assert diagonal[i].lo > 0
        for j in range(i+1, dim):
            lower[j][i] = exact((exact(matrix[j][i]) -
                                 sum(lower[j][k]*lower[i][k]*diagonal[k] for k in range(i)))
                                / diagonal[i])
    vectors = []
    for i in range(dim):
        u = [ZERO] * dim
        u[i] = exact(1 / diagonal[i].sqrt())
        for j in range(i-1, -1, -1):
            u[j] = exact(-sum(lower[k][j]*u[k] for k in range(j+1, i+1)))
        vectors.append(u)
    return vectors


def diagonal_dominance(matrix, vectors):
    products = [[dot(row, u) for row in matrix] for u in vectors]
    transformed = [[dot(u, row) for u in vectors] for row in products]
    return min(row[i].lo - sum(z.abs_upper() for j, z in enumerate(row) if j != i)
               for i, row in enumerate(transformed))


def check(root, radius):
    rows = fan_rows(root)
    lam = multipliers(rows)
    print("Positive multipliers:", [float(l.mid()) for l in lam])
    at_root = lagrangian_hessian(rows, lam, root, root)
    basis = preconditioner(at_root)
    box = [root[0], *(x + I(-radius, radius) for x in root[1:])]
    matrix = lagrangian_hessian(fan_rows(box), lam, root, box)
    margin = diagonal_dominance(matrix, basis)
    print("Congruence diagonal dominance margin:", margin / I.SCALE)
    assert margin > 0
    print(f"Strict local minimum in the full 4+5 branch within coordinate distance {radius}.")


def separable_hessian(rows, lam, root, box):
    dim = N-1
    matrix = [[ZERO] * dim for _ in range(dim)]
    widths = [x-y for x, y in zip(box[1:4], root[1:4])]
    w = [lam[k]+dot(DUAL_SLOPES[k], widths) for k in range(9)]
    assert all(t.lo > 0 for t in w)
    inner = [ZERO] * 9
    for i, weight in zip(ACTIVE_INNER, lam[9:16]):
        inner[i] = weight
    r, a, b, v = box[:4]
    for site in range(9):
        previous = (site+8) % 9
        xi, yi = 3+2*site, 4+2*site
        x, y = box[xi+1], box[yi+1]
        _, _, h = endpoint_derivatives(x, y, r, w[previous]-w[site], True, w[previous]+w[site])
        for i in range(2):
            for j in range(2):
                matrix[xi+i][xi+j] += h[i][j]
        _, grad_angle, _ = endpoint_derivatives(x, y, r, ONE, True, ZERO)
        _, grad_width, _ = endpoint_derivatives(x, y, r, ZERO, True)
        for i, (di, do) in enumerate(zip(DUAL_SLOPES[previous], DUAL_SLOPES[site])):
            for j in range(2):
                u = (di-do)*grad_angle[j]+(di+do)*grad_width[j]
                matrix[i][xi+j] += u
                matrix[xi+j][i] += u
        for p in (True, False):
            wi = inner[previous] if (previous in P_FAN) == p else ZERO
            wo = inner[site] if (site in P_FAN) == p else ZERO
            if (wi+wo).hi == 0:
                continue
            dx = [(xi, 1), (0, -1) if p else (1, 1)]
            dy = [(yi, 1), (2, -1)]
            _, _, h = endpoint_derivatives(x-a if p else x+b, y-v, r, wi-wo, False, wi+wo)
            for k, local_i in enumerate((dx,dy)):
                for l, local_j in enumerate((dx,dy)):
                    for i, di in local_i:
                        for j, dj in local_j:
                            matrix[i][j] += di*dj*h[k][l]
    for coefficient, (_, hess) in zip(lam[-2:], rows[-2:]):
        for i in range(dim):
            for j in range(dim):
                matrix[i][j] += coefficient * hess[i][j]
    return matrix


def transpose(a):
    return list(map(list, zip(*a)))


def matmul(a, b):
    return [[dot(x, y) for y in transpose(b)] for x in a]


def schur_bounds(h, reference):
    schur = [row[:3] for row in h[:3]]
    margins = []
    for idx in range(3, N-1, 2):
        a = [row[idx:idx+2] for row in h[idx:idx+2]]
        ar = [row[idx:idx+2] for row in reference[idx:idx+2]]
        b = [row[idx:idx+2] for row in h[:3]]
        br = [row[idx:idx+2] for row in reference[:3]]
        t = [[exact(x) for x in row] for row in matmul(inverse_mid(ar), transpose(br))]
        v = preconditioner(ar)
        margin = diagonal_dominance(a, v)
        margins.append(margin / I.SCALE)
        assert margin > 0
        at = matmul(a, t)
        bt = matmul(b, t)
        tat = matmul(transpose(t), at)
        e = [[b[i][j] - at[j][i] for j in range(2)] for i in range(3)]
        ev = matmul(e, transpose(v))
        correction = matmul(ev, transpose(ev))
        for i in range(3):
            for j in range(3):
                schur[i][j] += tat[i][j]-bt[i][j]-bt[j][i]
                # Keep the small residual as a uniform PSD error rather than
                # inverting the uncertain block entry by entry.
            err = sum(correction[i][j].abs_upper() for j in range(3))
            schur[i][i] -= I.raw(err, err) / I.raw(margin, margin)
    return schur, min(margins)


def check_separable(root, inner_radius, site_radius):
    rows = fan_rows(root)
    lam = multipliers(rows)
    ref = separable_hessian(rows, lam, root, root)
    box = [root[0], *(x+I(-inner_radius, inner_radius) for x in root[1:4]),
           *(x+I(-site_radius, site_radius) for x in root[4:])]
    h = separable_hessian(fan_rows(box), lam, root, box)
    sr, _ = schur_bounds(ref, ref)
    sh, outer_margin = schur_bounds(h, ref)
    margin = diagonal_dominance(sh, preconditioner(sr))
    print("Outer block margin:", outer_margin, "inner Schur margin:", margin / I.SCALE)
    assert margin > 0
    print(f"Positive definite separable dual for inner radius {inner_radius}, site radius {site_radius}.")


def site_hessian(r, inner_box, center, anchor, lam, site):
    previous = (site+8) % 9
    w = [lam[k]+dot(DUAL_SLOPES[k], [x-y for x,y in zip(inner_box,anchor)])
         for k in (previous,site)]
    assert all(t.lo > 0 for t in w)
    mu = [ZERO]*9
    for i, weight in zip(ACTIVE_INNER,lam[9:16]):
        mu[i] = weight
    a,b,v = inner_box
    x,y = center
    ans = [[ZERO]*5 for _ in range(5)]
    _,_,h = endpoint_derivatives(x,y,r,w[0]-w[1],True,w[0]+w[1])
    for i in range(2):
        for j in range(2):
            ans[3+i][3+j] = h[i][j]
    _,angle,_ = endpoint_derivatives(x,y,r,ONE,True,ZERO)
    _,width,_ = endpoint_derivatives(x,y,r,ZERO,True)
    for i,(di,do) in enumerate(zip(DUAL_SLOPES[previous],DUAL_SLOPES[site])):
        for j in range(2):
            ans[i][3+j] = ans[3+j][i] = (di-do)*angle[j]+(di+do)*width[j]
    for p in (True,False):
        wi = mu[previous] if (previous in P_FAN)==p else ZERO
        wo = mu[site] if (site in P_FAN)==p else ZERO
        if (wi+wo).hi == 0:
            continue
        maps = ([(3,1),(0,-1) if p else (1,1)], [(4,1),(2,-1)])
        _,_,h = endpoint_derivatives(x-a if p else x+b,y-v,r,wi-wo,False,wi+wo)
        for k, mi in enumerate(maps):
            for l, mj in enumerate(maps):
                for i,ci in mi:
                    for j,cj in mj:
                        ans[i][j] += ci*cj*h[k][l]
    if site in (2,7):
        sign = 1 if site==2 else -1
        weight = lam[16 if site==2 else 17]
        d = (a+b)/2
        h = (r.square()-d.square()).sqrt()
        sy = y-v-sign*h
        z = sign*d/(2*h)
        dx,dy = (-HALF,HALF,ZERO,ONE,ZERO),(z,z,-ONE,ZERO,ONE)
        for i in range(5):
            for j in range(5):
                ans[i][j] += 2*weight*(dx[i]*dx[j]+dy[i]*dy[j])
        mixed = weight*sy*sign*r.square()/(2*h.square()*h)
        for i in (0,1):
            for j in (0,1):
                ans[i][j] += mixed
    return ans


def site_schur(h, t, basis):
    a = [row[3:] for row in h[3:]]
    b = [row[3:] for row in h[:3]]
    margin = diagonal_dominance(a,basis)
    if margin <= 0:
        return None
    at = matmul(a,t)
    bt = matmul(b,t)
    tat = matmul(transpose(t),at)
    ev = matmul([[b[i][j]-at[j][i] for j in range(2)] for i in range(3)],transpose(basis))
    correction = matmul(ev,transpose(ev))
    floor = I.raw(margin,margin)
    return [[h[i][j]+tat[i][j]-bt[i][j]-bt[j][i]-correction[i][j]/floor
             for j in range(3)] for i in range(3)]


def grid_box(x, step):
    cells = [x]
    while max(t.hi-t.lo for t in cells) > step:
        cells = [piece for t in cells for piece in t.split()]
    return cells


def check_separable_cells(root, inner_radius, site_radius, step):
    lam = multipliers(fan_rows(root))
    inner = root[1:4]
    wide = [x+I(-inner_radius,inner_radius) for x in inner]
    ref, lower = ([[ZERO]*3 for _ in range(3)] for _ in range(2))
    for site in range(9):
        center = root[4+2*site:6+2*site]
        h0 = site_hessian(root[0],inner,center,inner,lam,site)
        a = [row[3:] for row in h0[3:]]
        b = [row[3:] for row in h0[:3]]
        t = [[exact(x) for x in row] for row in matmul(inverse_mid(a),transpose(b))]
        basis = preconditioner(a)
        s0 = site_schur(h0,t,basis)
        assert s0 is not None
        cells = [grid_box(x+I(-site_radius,site_radius),I(step).hi) for x in center]
        lo = [[1000*I.SCALE]*3 for _ in range(3)]
        hi = [[-1000*I.SCALE]*3 for _ in range(3)]
        for x in cells[0]:
            for y in cells[1]:
                s = site_schur(site_hessian(root[0],wide,(x,y),inner,lam,site),t,basis)
                assert s is not None, f"site {site} outer block"
                for i in range(3):
                    for j in range(3):
                        lo[i][j] = min(lo[i][j],s[i][j].lo)
                        hi[i][j] = max(hi[i][j],s[i][j].hi)
        for i in range(3):
            for j in range(3):
                ref[i][j] += s0[i][j]
                lower[i][j] += I.raw(lo[i][j],hi[i][j])
    margin = diagonal_dominance(lower,preconditioner(ref))
    print("Inner Schur margin:",margin/I.SCALE)
    assert margin>0
    print(f"Positive definite dual on inner radius {inner_radius}, site radius {site_radius}.")


if __name__ == "__main__":
    import sys
    box = verify_root(CENTER, ETA)
    verify_geometry(box)
    root = symmetric_point(box)
    verify_active_arcs(box, root)
    if sys.argv[1:] == ["constants"]:
        export_constants(root)
    elif len(sys.argv) > 1 and sys.argv[1] == "dual-cells":
        check_separable_cells(root,*(Fraction(v) for v in sys.argv[2:]))
    elif len(sys.argv) > 1 and sys.argv[1] == "dual":
        check_separable(root, Fraction(sys.argv[2]), Fraction(sys.argv[3]))
    else:
        check(root, Fraction(sys.argv[1]) if len(sys.argv) > 1 else Fraction(1, 10000))
