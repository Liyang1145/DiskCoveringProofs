"""Offline exploratory search. Requires locally installed NumPy and SciPy."""
import argparse
import itertools

import numpy as np
from scipy.optimize import minimize
from scipy.spatial import Delaunay


def cross(a, b):
    return a[..., 0] * b[..., 1] - a[..., 1] * b[..., 0]


def circumcenters(triangles):
    a = triangles[:, 0]
    u = triangles[:, 1] - a
    v = triangles[:, 2] - a
    determinant = cross(u, v)
    du = np.einsum('ij,ij->i', u, u)
    dv = np.einsum('ij,ij->i', v, v)
    zx = (du * v[:, 1] - dv * u[:, 1]) / (2 * determinant)
    zy = (dv * u[:, 0] - du * v[:, 0]) / (2 * determinant)
    z = np.column_stack((zx, zy))
    bary_b = cross(z, v) / determinant
    bary_c = cross(u, z) / determinant
    return a + z, np.column_stack((1 - bary_b - bary_c, bary_b, bary_c))


def exact_candidates(p):
    """Finite candidate set for the maximum, evaluated in floating point."""
    triangles = Delaunay(p).simplices
    z, _ = circumcenters(p[triangles])
    z = z[np.linalg.norm(z, axis=1) <= 1]
    i, j = np.array(list(itertools.combinations(range(len(p)), 2))).T
    d = p[j] - p[i]
    v = d / np.linalg.norm(d, axis=1)[:, None]
    k = (np.einsum('ij,ij->i', p[j], p[j]) - np.einsum('ij,ij->i', p[i], p[i])) / (2 * np.linalg.norm(d, axis=1))
    v = v[np.abs(k) <= 1]
    k = k[np.abs(k) <= 1]
    side = v[:, ::-1] * [-1, 1]
    base = k[:, None] * v
    offset = np.sqrt(1 - k**2)[:, None] * side
    all_points = np.vstack((z, base + offset, base - offset, -p / np.maximum(np.linalg.norm(p, axis=1), 1e-300)[:, None], [[1, 0]]))
    values = np.min(np.linalg.norm(all_points[:, None] - p[None, :], axis=2), axis=1)
    return np.max(values)


def optimize(initial, outer_count):
    n = len(initial)
    outer = np.arange(outer_count)
    after = np.roll(outer, -1)
    candidate = np.r_[initial.ravel(), exact_candidates(initial) + .002]
    for _ in range(6):
        p = candidate[:-1].reshape(-1, 2)
        triangles = Delaunay(p).simplices
        z, _ = circumcenters(p[triangles])
        triangles = triangles[np.linalg.norm(z, axis=1) <= 1.01]
        row_tri = np.arange(len(triangles))[:, None]

        def constraints(x, jac=False):
            p = x[:-1].reshape(-1, 2)
            r = x[-1]
            d = np.linalg.norm(p[outer], axis=1)
            c = (1 + d**2 - r**2) / (2*d)
            c_clipped = np.clip(c, -1 + 1e-9, 1 - 1e-9)
            w = np.arccos(c_clipped) - 20 * (c - c_clipped)
            gap = np.arctan2(cross(p[outer], p[after]), np.einsum('ij,ij->i', p[outer], p[after]))
            z, bary = circumcenters(p[triangles])
            diffs = p[triangles] - z[:, None, :]
            if not jac:
                return np.r_[w + w[after] - gap, r*r - np.einsum('ij,ij->i', diffs[:, 0], diffs[:, 0])]

            w_factor = np.where(c == c_clipped, -1/np.sqrt(1-c_clipped**2), -20)
            wd = w_factor * (1 - (1-r*r)/d**2) / 2
            wr = -w_factor * r / d
            wd_xy = (wd/d)[:, None] * p[outer]
            angle_xy = (p[outer, ::-1] * [-1, 1]) / d[:, None]**2
            j1 = np.zeros((outer_count, n*2+1))
            j1[outer, 2*outer] = (wd_xy+angle_xy)[:, 0]
            j1[outer, 2*outer+1] = (wd_xy+angle_xy)[:, 1]
            j1[outer, 2*after] = (wd_xy-angle_xy)[after, 0]
            j1[outer, 2*after+1] = (wd_xy-angle_xy)[after, 1]
            j1[:, -1] = wr + wr[after]
            j2 = np.zeros((len(triangles), n*2+1))
            j2[row_tri, 2*triangles] = -2 * bary * diffs[:, :, 0]
            j2[row_tri, 2*triangles+1] = -2 * bary * diffs[:, :, 1]
            j2[:, -1] = 2*r
            return np.vstack((j1, j2))

        fit = minimize(lambda x: x[-1], candidate, jac=lambda x: np.eye(1, 2*n+1, 2*n)[0],
                       bounds=[(-1, 1)]*(n*2)+[(.25, .75)], method='SLSQP',
                       constraints=[{'type': 'ineq', 'fun': constraints, 'jac': lambda x: constraints(x, True)}],
                       options={'maxiter': 180, 'ftol': 1e-13})
        candidate = fit.x
        p = candidate[:-1].reshape(-1, 2)
        checked = exact_candidates(p)
        if abs(checked - candidate[-1]) < 1e-9 and np.min(constraints(candidate)) > -1e-8:
            return checked, p
    return checked, p


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', type=int, default=40)
    parser.add_argument('--outer', type=int, choices=[10, 11], default=10)
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    n = args.outer
    m = 14 - n
    best = np.inf
    for i in range(args.runs):
        outer_angles = 2 * np.pi * np.arange(n) / n
        inner_angles = 2 * np.pi * np.arange(m) / m + rng.uniform(0, 2 * np.pi / n)
        p = np.vstack((.842 * np.column_stack((np.cos(outer_angles), np.sin(outer_angles))),
                       .275 * np.column_stack((np.cos(inner_angles), np.sin(inner_angles)))))
        p += rng.normal(0, .026 if i > 0 else .0, p.shape)
        try:
            value, p = optimize(p, n)
        except (ValueError, np.linalg.LinAlgError):
            continue
        print(i, format(value, '.15f'), flush=True)
        if value < best:
            best = value
            np.savetxt(f'exploratory-{n}.txt', p, fmt='%.17g')


if __name__ == '__main__':
    main()
