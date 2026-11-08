"""Offline search for angular measures for a ten-outer-disk certificate."""

import argparse
import math
import warnings

import numpy as np
from scipy.optimize import OptimizeWarning, linprog


R = .36111
K = 32
EDGES = np.linspace(-.5, .5, K + 1)


def test_intervals(exposure):
    lo, hi = EDGES[:-1], EDGES[1:]
    full = np.column_stack([lo, hi])
    lo = np.maximum(lo, -exposure)
    hi = np.maximum(lo, np.minimum(hi, exposure))
    return full, np.column_stack([lo, hi])


def arc_lengths(vector, circle_radius, disk_radius, intervals):
    d = abs(vector)
    denominator = 2 * circle_radius * np.maximum(1e-40, d)
    cosine = (circle_radius ** 2 + d ** 2 - disk_radius ** 2) / denominator
    half = np.arccos(np.clip(cosine, -1, 1)) / math.tau
    if np.any(d == 0):
        half = np.where(d == 0, .5 if circle_radius <= disk_radius else 0., half)
    mid = np.angle(vector) / math.tau
    result = 0
    for shift in (-1, 0, 1):
        lo = np.maximum((mid - half + shift)[:, None], intervals[:, 0])
        hi = np.minimum((mid + half + shift)[:, None], intervals[:, 1])
        result += np.maximum(0, hi - lo)
    return result


def grid(n, m):
    d = np.linspace(1 - R, 1, n)
    theta = np.arange(m) * math.tau / m
    return (d[:, None] * np.exp(1j * theta[None, :])).ravel()


def measure_matrix(a, x, y, delta, samples, disk_radius=R, exposure=None):
    rho = R + delta
    if exposure is None:
        exposure = math.acos(-min(1., a / rho)) / math.tau
    unit, inner = test_intervals(exposure)
    mat = np.concatenate([arc_lengths(samples, 1, disk_radius, unit),
                          arc_lengths(samples - (x + a + 1j * y), rho, disk_radius, inner),
                          arc_lengths(-(samples - (x - a + 1j * y)), rho, disk_radius, inner)], axis=1)
    mass = np.concatenate([np.diff(unit, axis=1).ravel(), np.diff(inner, axis=1).ravel(), np.diff(inner, axis=1).ravel()])
    return mat, mass


def find_measure(matrix, mass):
    inequalities = np.column_stack([matrix, -np.ones(len(matrix))])
    c = np.r_[np.zeros(len(mass)), 1.]
    with warnings.catch_warnings():
        warnings.filterwarnings('ignore',message='Unrecognized options detected',category=OptimizeWarning)
        result = linprog(c, A_ub=inequalities, b_ub=np.zeros(len(matrix)),
                         A_eq=np.r_[mass, 0.][None, :], b_eq=[1.], bounds=(0, 50), method='highs',
                         options={'threads':1})
    if not result.success:
        return None, math.inf
    return result.x[:-1], result.fun


def main():
    p = argparse.ArgumentParser()
    p.add_argument('parameters', nargs='*', type=float)
    args = p.parse_args()
    trials = [args.parameters] if args.parameters else [
        (.174, 0, 0), (.174, .04, .03), (.174, .1, .04), (.20, 0, .02),
        (.14, .13, .04), (.06, .06, .06), (.25, .2, .05), (.31, .15, .03),
        (.03, .08, .06), (.21, .04, .017), (.15, 0, .045), (.23, 0, 0)]
    for a, x, y in trials:
        for delta in (0., .002, .004, .008, .012):
            matrix, mass = measure_matrix(a, x, y, delta, grid(28, 112))
            weights, cap = find_measure(matrix, mass)
            if weights is None:
                print(a, x, y, delta, 'no weights', flush=True)
                continue
            matrix, mass = measure_matrix(a, x, y, delta, grid(71, 256))
            worst = (matrix @ weights).max() / (mass @ weights)
            print(a, x, y, delta, cap, worst, flush=True)


if __name__ == '__main__':
    main()
