"""Fast numeric seeds for b=14 flow certificates using edge direction cuts."""

import warnings

import numpy as np
from scipy.optimize import OptimizeWarning, linprog, minimize
from scipy.sparse import coo_matrix

from find_belt_geometry import initial_positions
from find_patch14 import balance_flow
from verify_belt_geometry import closure, gauge_weights
from verify_belt_pruning import B, SCALE
from verify_patch14 import ARC_CAP, RADIUS


def mean_gauge(dist):
    matrix = np.asarray(dist)
    width = (-matrix-matrix.T)/SCALE
    gram = width @ width.T
    b = len(dist)
    fit = minimize(lambda w: w @ gram @ w, np.full(b,1/b), jac=lambda w: 2*gram @ w,
                   bounds=[(0,1)]*b,
                   constraints=[{"type":"eq","fun":lambda w: np.sum(w)-1,"jac":lambda w: np.ones(b)}],
                   method="SLSQP",options={"ftol":1e-9,"maxiter":40})
    weights = [max(0,round(10**6*w)) for w in fit.x] if fit.success else [1]*b
    return weights if any(weights) else [1]*b


def linear_angle_flow(graph, paths, angle_edges, origin_cap=None, iterations=5, boundary=B, *,
                      radius=RADIUS, prefix_goal=None, anchor=0):
    """Search a polyhedral relaxation. Exact acceptance is separate."""
    _, _, free, edges = graph
    dist = closure(angle_edges, boundary)
    if dist is None:
        return None
    lower = np.array(dist[0]) / SCALE
    upper = -np.array([row[0] for row in dist]) / SCALE
    nominal = float(ARC_CAP) * np.arange(boundary)
    projection = None
    relative_lo, relative_hi = lower, upper
    if anchor != 0:
        weights = np.array(gauge_weights(anchor,boundary),dtype=float)
        matrix = np.asarray(dist)
        projection = np.eye(boundary)-weights
        relative_lo = weights @ matrix/SCALE
        relative_hi = -matrix @ weights/SCALE
        indices = [np.flatnonzero(projection[j]) for j in range(boundary)]
        nominal -= weights @ nominal
    width = relative_hi-relative_lo
    center = (relative_hi+relative_lo)/2

    def xy(u):
        t = nominal - u
        return np.column_stack((np.cos(t), np.sin(t)))

    left, right, mid = xy(relative_lo), xy(relative_hi), xy(center)
    slope = np.divide(right - left, width[:, None], out=np.zeros_like(left),
                      where=width[:, None] > 0)
    constant = left - relative_lo[:, None] * slope
    initial = initial_positions(graph, paths, mid, boundary)
    initial = np.vstack((initial, mid, np.zeros((1, 2)))) if origin_cap is not None \
        else np.vstack((initial, mid))
    origin_ratio = 1.0 if origin_cap is None else float(origin_cap / radius)
    precise = radius != RADIUS
    tol = 1e-9 if precise else 1e-5
    directions = np.linspace(0, 2 * np.pi, 8, endpoint=False)
    seeds = [(float(np.cos(t)), float(np.sin(t))) for t in directions]
    edge_directions = [list(seeds) for _ in edges]
    for ds, (u, v) in zip(edge_directions, edges):
        delta = initial[v] - initial[u]
        length = np.linalg.norm(delta)
        if length > 1e-8:
            x, y = delta / length
            ds.extend(((x, y), (-x, -y)))

    rhs, row, col, val = [], [], [], []

    def add(columns, coefficients, b):
        row.extend([len(rhs)] * len(columns))
        col.extend(columns)
        val.extend(coefficients)
        rhs.append(b)

    for u, v, w in angle_edges:
        add([2 * free + u, 2 * free + v], [1, -1], -w / SCALE)
    base = len(rhs)
    last = 2 * free + boundary
    objective = np.r_[np.zeros(last), 1.]
    bounds = [(None, None)] * (2 * free) + list(zip(lower, upper)) + [(0, None)]
    if prefix_goal is not None:
        j, sign = prefix_goal
        objective[last] = 0
        objective[2*free+j] = sign
        bounds[last] = (float(radius),float(radius))
    edge_array = np.asarray(edges,dtype=int)

    def ordinary_matrix(ds):
        lengths = np.asarray([len(d) for d in ds],dtype=int)
        source,dest = edge_array[np.repeat(np.arange(len(edges)),lengths)].T
        directions = np.asarray([v for d in ds for v in d])
        x,y = directions.T
        index = base+np.arange(len(directions))
        inside = dest < free
        seam = (dest >= free)&(dest < free+boundary)
        origin = dest == free+boundary
        j = dest[seam]-free
        sd = directions[seam]
        h = width[j]
        dot = np.sum(mid[j]*sd,axis=1)
        loss = np.maximum(0,-dot+np.sum(np.abs(sd),axis=1)*h/2)*h*h/8
        rhs_geom = np.zeros(len(directions))
        rhs_geom[seam] = loss-np.sum(constant[j]*sd,axis=1)
        rr = np.concatenate((row,index,index,index,index[inside],index[inside],index[seam]))
        cc = np.concatenate((col,2*source,2*source+1,np.full(len(index),last),
                             2*dest[inside],2*dest[inside]+1,2*free+j))
        vv = np.concatenate((val,-x,-y,-np.where(origin,origin_ratio,1),
                             x[inside],y[inside],np.sum(slope[j]*sd,axis=1)))
        return (coo_matrix((vv,(rr,cc)),shape=(base+len(index),last+1)).tocsc(),
                np.r_[rhs,rhs_geom],directions,lengths)

    best = None
    for _ in range(iterations):
        if projection is None:
            matrix, rhs_lp, flat_dirs, lengths = ordinary_matrix(edge_directions)
        else:
            del rhs[base:]
            while row and row[-1] >= base:
                row.pop()
                col.pop()
                val.pop()
            for (u,v),ds in zip(edges,edge_directions):
                for x,y in ds:
                    if v < free:
                        add([2*u,2*u+1,2*v,2*v+1,last],[-x,-y,x,y,-1.],0.)
                    elif v == free+boundary:
                        add([2*u,2*u+1,last],[-x,-y,-origin_ratio],0.)
                    else:
                        j = v-free
                        lowest = mid[j,0]*x+mid[j,1]*y-(abs(x)+abs(y))*width[j]/2
                        loss = max(0.,-lowest)*width[j]**2/8
                        factor = slope[j,0]*x+slope[j,1]*y
                        bound = loss-constant[j,0]*x-constant[j,1]*y
                        js = indices[j]
                        add([2*u,2*u+1,*(2*free+js),last],
                            [-x,-y,*(factor*projection[j,js]),-1.],bound)
            matrix = coo_matrix((val,(row,col)),shape=(len(rhs),last+1)).tocsc()
            rhs_lp = rhs
            lengths = np.asarray([len(d) for d in edge_directions],dtype=int)
            flat_dirs = np.asarray([v for d in edge_directions for v in d])
        with warnings.catch_warnings():
            warnings.filterwarnings("ignore", "Unrecognized options detected", OptimizeWarning)
            options = {"threads": 1}
            if precise:
                options.update(primal_feasibility_tolerance=1e-10, dual_feasibility_tolerance=1e-10)
            res = linprog(objective, A_ub=matrix, b_ub=rhs_lp, bounds=bounds,
                          method="highs", options=options)
        if not res.success:
            break
        multipliers = np.maximum(0,-np.asarray(res.ineqlin.marginals[base:]))
        starts = np.r_[0,np.cumsum(lengths[:-1])]
        flow = np.add.reduceat(multipliers[:,None]*flat_dirs,starts,axis=0)
        best = balance_flow(flow, free, len(initial), edges), res.fun
        if prefix_goal is None and res.fun > float(radius) + 2*tol:
            break
        prefix = res.x[2*free:last]
        xy_terminal = xy(prefix if projection is None else projection @ prefix)
        if origin_cap is not None:
            xy_terminal = np.vstack((xy_terminal, np.zeros((1, 2))))
        p = np.vstack((res.x[:2*free].reshape(-1, 2), xy_terminal))
        added = 0
        rho = res.x[last]
        for (u, v), ds in zip(edges, edge_directions):
            d = p[v] - p[u]
            norm = np.linalg.norm(d)
            if norm > rho + tol or (v == free + boundary and norm > origin_ratio * rho + tol):
                x, y = d / norm
                if all((x - a)**2 + (y - b)**2 > tol*1e-3 for a, b in ds):
                    ds.append((x, y))
                    added += 1
        if not added:
            break
    return best
