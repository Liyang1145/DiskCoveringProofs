"""Exact local radius bound in seam coordinates for the candidate triangulation."""

from collections import Counter, deque
from fractions import Fraction as Q

from rational_trig import sqrt_bounds
from refine_template import dot, sub
from verify_local import (
    I, circumcenter, cross, pd_check, positive_triangles, require, rot,
    stationary_multipliers, template_configuration,
)

SEAM_NEIGHBORHOOD = Q("0.0255")


def lower(x):
    return Q(x.lo, I(1).lo)


def upper(x):
    return Q(x.hi, I(1).lo)


def contact_graph(sites, seams, multipliers):
    points, edges = sites.copy(), []
    for tri, mu in zip(positive_triangles(), multipliers):
        p, q, s = (sites[u] for u in tri)
        z = circumcenter(p, q, s)
        a, b, t = sub(q,p), sub(s,p), sub(z,p)
        beta = cross(t,b)/cross(a,b)
        gamma = cross(a,t)/cross(a,b)
        edges.extend((u, len(points), mu*w) for u, w in zip(tri, (1-beta-gamma, beta, gamma)))
        points.append(z)
    free = len(points)
    for j, (y, mu) in enumerate(zip(seams, multipliers[-len(seams):])):
        for u, sign in ((j,1), ((j+1)%len(seams),-1)):
            derivative = 2*sign*dot(sub(y,sites[u]),rot(y))
            require(derivative.lo > 0, "Wrong seam endpoint derivative")
            edges.append((u,free+j,mu/derivative))
    return points+seams, edges, free


def minimum_weight(points, edges, free):
    neighbors = [[] for _ in points]
    for u,v,w in edges:
        require(w.lo > 0, "A contact weight is not positive")
        neighbors[u].append(v)
        neighbors[v].append(u)
    distance = dict.fromkeys(range(free,len(points)), 0)
    todo = deque(distance)
    while todo:
        u = todo.popleft()
        for v in neighbors[u]:
            if v not in distance:
                distance[v] = distance[u]+1
                todo.append(v)
    require(len(distance) == len(points), "A contact component has no seam")
    return min(lower(w) for _,_,w in edges)


def harmonic_rows(points, edges, free):
    size = len(points)
    lap = [[I(0) for _ in points] for _ in points]
    for u,v,w in edges:
        lap[u][u] += w
        lap[v][v] += w
        lap[u][v] -= w
        lap[v][u] -= w
    rows = [row[:free]+[-a for a in row[free:]] for row in lap[:free]]
    # The free principal block is positive definite by connectivity to seams.
    for i in range(free):
        inv = rows[i][i].reciprocal()
        for j in range(i+1,size):
            rows[i][j] *= inv
        for k in range(free):
            if i != k:
                factor = rows[k][i]
                for j in range(i+1,size):
                    rows[k][j] -= factor*rows[i][j]
    count = size-free
    h = [row[free:] for row in rows] + [[I(i==j) for j in range(count)] for i in range(count)]
    reduced = [[sum(lap[i][k]*h[k][j] for k in range(size)) for j in range(count)]
               for i in range(free,size)]
    return h,reduced


def tangent_matrix(points,edges,free,radial,penalty,eta,edge_losses,seam_losses,gauge):
    # Fix one seam to remove the rotation direction.
    basis = [[(2*i,(I(1),I(0))), (2*i+1,(I(0),I(1)))] for i in range(free)]
    index = 2*free
    for j,y in enumerate(points[free:]):
        if j == gauge:
            basis.append([])
        else:
            basis.append([(index,rot(y))])
            index += 1
    size = 2*free+len(points)-free-1
    matrix = [[I(0) for _ in range(size)] for _ in range(size)]
    for (u,v,w), loss in zip(edges,edge_losses):
        d = sub(points[v],points[u])
        row = [(i,(-p[0],-p[1])) for i,p in basis[u]] + basis[v]
        jac = [2*dot(d,p) for _,p in row]
        normal = [dot(p,points[v]) if v >= free else I(0) for _,p in row]
        for (i,a), g, x in zip(row,jac,normal):
            for (j,b), h, y in zip(row,jac,normal):
                matrix[i][j] += (w-loss)*dot(a,b) + penalty*g*h - eta*w*x*y
    for v,w in radial.items():
        if v != free+gauge:
            i = basis[v][0][0]
            matrix[i][i] -= w+seam_losses[v]
    return matrix


def verify(gauge=0):
    width, penalty, eta, xi, normal = SEAM_NEIGHBORHOOD,Q(".06"),Q(".0357"),Q(".25"),Q(".501")
    sites,seams,q = template_configuration()
    _,_,_,multipliers = stationary_multipliers(sites,seams,q)
    points,edges,free = contact_graph(sites,seams,multipliers)
    weight = minimum_weight(points,edges,free)
    radial, seam_degree = Counter(), Counter()
    for u,v,w in edges:
        if v >= free:
            radial[v] += w*dot(sub(points[v],points[u]),points[v])
            seam_degree[v] += w
    require(len(radial) == len(seams) and all(w.lo > 0 for w in radial.values()),
            "The seam forces must point outwards")
    require(0 < width < Q(1,2) and normal**2*(1-width**2/4) >= Q(1,4), "Invalid radial bound")
    h, reduced = harmonic_rows(points,edges,free)
    op, negative = Q(".0036"), Q(".000563")
    b = len(seams)
    require(type(gauge) is int and 0 <= gauge < b,"Invalid fixed seam")
    moving = [j for j in range(b) if j != gauge]
    pd_check([[reduced[i][j]*dot(seams[i],seams[j]) + (I(negative)-radial[free+i] if i==j else I(0))
               for j in moving] for i in moving])
    cross = [[reduced[i][j]*dot(rot(seams[i]),seams[j]) for j in moving] for i in moving]
    pd_check([[I(op**2 if i==j else 0)-sum(row[i]*row[j] for row in cross)
               for j in range(b-1)] for i in range(b-1)])
    move = normal*width
    deficit = (b-1)*(negative + 2*op*move + max(map(upper,radial.values()))*move**2)
    require(2*penalty*deficit*width**2 <= weight**2, "Penalty may exceed a contact multiplier")
    seam_losses = {v: (upper(seam_degree[v])/eta+upper(s))*move**2 for v,s in radial.items()}
    edge_losses = []
    for u,v,w in edges:
        _, gap = sqrt_bounds(deficit/lower(w))
        harmonic = sum((h[u][j]-h[v][j]).magnitude() for j in moving)
        change = width*(gap+harmonic)
        edge_losses.append(2*penalty*(1+xi if v >= free else 1)*change**2)
        if v >= free:
            projection = dot(sub(points[v],points[u]),points[v]).magnitude()
            seam_losses[v] += 2*penalty*(1+1/xi)*(2*projection+change)**2*move**2
    matrix = tangent_matrix(points,edges,free,radial,penalty,eta,edge_losses,seam_losses,gauge)
    pivot = Q(pd_check(matrix), I(1).lo)
    print(f"PASS candidate contact graph with fixed seam {gauge}, distances <= {float(width):g}; "
          f"lower endpoints (rounded): weight {float(weight):.8g}, LDL pivot {float(pivot):.8g}")


if __name__ == "__main__":
    verify()
