"""Untrusted SOCP discovery with classified norm cones; new exact BDual accept."""
from pathlib import Path
from fractions import Fraction as F
import os
import sys
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import numpy as np
from scipy.sparse import csc_matrix
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round2-grouped/deps/clarabel0111"))
import clarabel
import bounded_exact as E
import exact_graph as exact
from actual_norm_bounds import constants as norm_constants


class Solver:
    def __init__(self, actualN, B, centers, masks):
        self.constants, self.radii, self.premise = norm_constants(actualN, B, centers, len(masks))
        self.B = B
        self.faces, self.edges, self.V = exact.graph(B, centers, masks)
        self.nedges = len(self.edges)
        self.nvar = 2*(self.V-1)+1
        self.rows, self.cols, self.values = [], [], []
        self.offset = 3*self.nedges+B-1
        self.rhs = np.zeros(self.offset+3*(self.V-1))
        for j, (u, v) in enumerate(self.edges):
            self.rows.append(3*j)
            self.cols.append(self.nvar-1)
            self.values.append(-1.)
            for axis in (0, 1):
                for node, sign in ((u, 1), (v, -1)):
                    if node:
                        self.rows.append(3*j+1+axis)
                        self.cols.append(2*(node-1)+axis)
                        self.values.append(-float(sign))
                    elif axis == 0:
                        self.rhs[3*j+1+axis] += sign
        for node in range(1, self.V):
            self.rhs[self.offset+3*(node-1)] = float(self.radii[node-1])
            for axis in (0, 1):
                self.rows.append(self.offset+3*(node-1)+1+axis)
                self.cols.append(2*(node-1)+axis)
                self.values.append(-1.)
        self.cones = ([clarabel.SecondOrderConeT(3) for _ in self.edges] +
                      [clarabel.NonnegativeConeT(B-1)] +
                      [clarabel.SecondOrderConeT(3) for _ in range(self.V-1)])
        self.P = csc_matrix((self.nvar, self.nvar))
        self.objective = np.zeros(self.nvar)
        self.objective[-1] = 1.
        self.settings = clarabel.DefaultSettings()
        self.settings.verbose = False
        self.settings.max_iter = 200
        self.settings.tol_gap_abs = self.settings.tol_gap_rel = self.settings.tol_feas = 1e-9

    def solve(self, lo, hi):
        rows, cols, values = list(self.rows), list(self.cols), list(self.values)
        rhs = self.rhs.copy()
        for i, (lower, upper) in enumerate(zip(lo, hi)):
            a, b = exact.kernel.arc_halfplane(lower, upper)
            rhs[3*self.nedges+i] = -float(F(b, exact.kernel.QB))
            for axis in (0, 1):
                rows.append(3*self.nedges+i)
                cols.append(2*i+axis)
                values.append(-float(F(a[axis], exact.kernel.QA)))
        A = csc_matrix((values, (rows, cols)), shape=(len(rhs), self.nvar))
        problem = clarabel.DefaultSolver(self.P, self.objective, A, rhs, self.cones, self.settings)
        result = problem.solve()
        x, dual = np.asarray(result.x), np.asarray(result.z)
        if not np.all(np.isfinite(x)) or not np.all(np.isfinite(dual)):
            return None, x
        flow = -dual[:3*self.nedges].reshape(self.nedges, 3)[:, 1:]
        la = dual[3*self.nedges:3*self.nedges+self.B-1]
        support = -dual[self.offset:].reshape(self.V-1, 3)[:, 1:]
        _, _, chords = exact.kernel.tree(self.V, tuple(self.edges))
        magnitude = max(float(np.max(np.abs(v))) for v in (flow, la, support))
        if magnitude <= 0:
            return None, x
        for scale in (10**10, 10**12, 10**14, 10**16):
            cert = {"q": scale, "l": [max(0, round(float(v)/magnitude*scale)) for v in la],
                    "b": [round(float(v)/magnitude*scale) for v in support.ravel()],
                    "f": [round(float(flow[j, axis])/magnitude*scale) for j in chords for axis in (0, 1)]}
            margin = E.force_margin(self.B, self.V, self.edges, lo, hi, cert,
                                    F(self.constants["radius_upper"]), self.radii)
            if margin > 0:
                return cert, x
        return None, x
