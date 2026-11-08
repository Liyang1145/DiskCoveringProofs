"""Offline floating-point search. Its results are not used as a proof."""

import argparse
import math

import numpy as np
from numba import njit
from scipy.optimize import differential_evolution, minimize


@njit(cache=False)
def coverage_squared(centers):
    n = len(centers)
    norms = np.sum(centers * centers, axis=1)
    best = 0.0
    for i in range(n):
        ax, ay = centers[i]
        aa = norms[i]
        if aa > 0:
            best = max(best, nearest(-ax / math.sqrt(aa), -ay / math.sqrt(aa), centers))
        for j in range(i):
            dx, dy = centers[j] - centers[i]
            dd = dx * dx + dy * dy
            if dd < 1e-20:
                continue
            u = (norms[j] - aa) / 2
            h2 = dd - u * u
            if h2 >= 0:
                h = math.sqrt(h2)
                best = max(best, nearest((u * dx + h * dy) / dd, (u * dy - h * dx) / dd, centers))
                best = max(best, nearest((u * dx - h * dy) / dd, (u * dy + h * dx) / dd, centers))
            for k in range(j):
                ex, ey = centers[k] - centers[i]
                v = (norms[k] - aa) / 2
                det = dx * ey - dy * ex
                if abs(det) < 1e-14:
                    continue
                x = (u * ey - dy * v) / det
                y = (dx * v - u * ex) / det
                if x * x + y * y <= 1.0:
                    best = max(best, nearest(x, y, centers))
    return best


@njit(cache=False)
def nearest(x, y, centers):
    result = math.inf
    for a, b in centers:
        result = min(result, (x - a) ** 2 + (y - b) ** 2)
    return result


def polar(r, a):
    return np.array([r * np.cos(a), r * np.sin(a)])


def setup(mode):
    if mode in ('D3a', 'D3b', 'C3'):
        def layout(p):
            inner = p[0]
            if mode == 'C3':
                ra, rb, rc, a, b, c = p[1:]
                base = [(ra, a), (rb, b), (rc, c)]
            else:
                ra, rb, a = p[1:]
                axis = 0 if mode == 'D3a' else math.pi / 3
                base = [(ra, axis), (rb, axis - a), (rb, axis + a)]
            return np.array([polar(r, a + k * math.tau / 3)
                             for r, a in [(inner, 0)] + base for k in range(3)])
        if mode == 'C3':
            bounds = [(.02, .39)] + [(.62, .98)] * 3 + [(-.5, .5), (.3, 1.1), (1., 1.9)]
        else:
            bounds = [(.02, .39), (.62, .98), (.62, .98), (.45, .94)]
    else:
        def layout(p):
            inner, axis_r, r1, r2, a1, a2 = p
            points = [[inner, 0], [-inner, 0]]
            axis = 0 if mode == 'D2a' else math.pi / 2
            points.extend(polar(axis_r, axis + k * math.pi) for k in range(2))
            for r, a in [(r1, a1), (r2, a2)]:
                points.extend(polar(r, angle) for angle in [a, -a, math.pi - a, math.pi + a])
            return np.array(points)
        bounds = [(.02, .38)] + [(.62, .98)] * 3 + [(.15, .85), (.81, 1.45)]
    return layout, bounds


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('modes', nargs='*', default=['D3a', 'D3b', 'D2a', 'D2b', 'C3'])
    parser.add_argument('--iters', type=int, default=450)
    args = parser.parse_args()
    for mode in args.modes:
        layout, bounds = setup(mode)

        def obj(p):
            return coverage_squared(layout(p))

        result = differential_evolution(obj, bounds, maxiter=args.iters, popsize=22,
                                        seed=123, tol=2e-12, polish=False)
        local = minimize(obj, result.x, method='Nelder-Mead', options={'maxiter': 1800, 'xatol': 1e-13})
        print(mode, math.sqrt(local.fun), repr(local.x), flush=True)
        print(layout(local.x), flush=True)


if __name__ == '__main__':
    main()
